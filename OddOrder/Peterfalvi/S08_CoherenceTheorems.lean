/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.FixedPointFree
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.BG.Ch1_Preliminary.S03_FrobeniusActions
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Peterfalvi §8: Some Coherence Theorems

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37.

This module records the main carrier structures for the §8 coherence theorems:
the solvable-normal filtration setup (6.1), the odd-order specialization
(6.4), and the Sibley-style final setup (6.8).  The hard numerical and
class-sum-algebra proofs are intentionally not asserted here.

Reference note: `notes/peterfalvi/s08_coherence_theorems.md`.
-/

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {Γ : Type*} [Group Γ]

/-- The induction summand commutes with complex conjugation. -/
theorem induceTerm_conjStar (H : Subgroup Γ) (θ : ClassFunction ↥H ℂ) (x g : Γ) :
    star (induceTerm H θ x g) = induceTerm H θ.conj x g := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [induceTerm_of_mem θ hx, induceTerm_of_mem θ.conj hx, conj_apply]
  · rw [induceTerm_of_not_mem θ hx, induceTerm_of_not_mem θ.conj hx, star_zero]

variable [Fintype Γ]

/-- The unnormalized induction sum commutes with complex conjugation. -/
theorem induceSum_conj (H : Subgroup Γ) (θ : ClassFunction ↥H ℂ) :
    (induceSum H θ).conj = induceSum H θ.conj := by
  ext g
  rw [conj_apply, induceSum_apply, induceSum_apply, star_sum]
  exact Finset.sum_congr rfl fun x _ => induceTerm_conjStar H θ x g

/-- The normalized induced class function commutes with complex conjugation. -/
theorem induce_conj (H : Subgroup Γ) [Invertible (Nat.card H : ℂ)]
    (θ : ClassFunction ↥H ℂ) :
    (induce H θ).conj = induce H θ.conj := by
  ext g
  rw [conj_apply, induce_apply, induce_apply, star_mul', star_sum]
  have hscale : star (⅟(Nat.card H : ℂ)) = ⅟(Nat.card H : ℂ) := by
    rw [invOf_eq_inv, star_inv₀, star_natCast]
  rw [hscale]
  exact congrArg (fun z => ⅟(Nat.card H : ℂ) * z)
    (Finset.sum_congr rfl fun x _ => induceTerm_conjStar H θ x g)

end ClassFunction

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
* `htau1_mem` — `ν χ ∈ ZIrr G` is the **injected** hypothesis `hνZ` (not derivable from `IsCoherent`,
  whose `extension` is a bare `→ₗ[ℤ]` with no ZIrr-codomain field).

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
    (χ : IrreducibleCharacter ↥L) {chi1 cj : ClassFunction ↥L ℂ} {a aj : ℕ} {Xχ Y : ClassFunction G ℂ}
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
    (hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G)
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
      hS₁ χ s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da hDaY_ZIrr hmemνZ hmemS1
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
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
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
  /-- The base character set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (Peterfalvi (6.8.b)). -/
  S : Set (ClassFunction ↥L ℂ)
  /-- `S` is exactly the set of characters induced from nontrivial irreducibles of `H`. -/
  S_eq : S = {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}
  /-- Peterfalvi (6.8)(c): the configuration is one of two cases.

  * **(c1)** `L` is a Frobenius group with kernel `H` and complement `W₁`.
  * **(c2)** Hypothesis (4.6) holds — encoded by a `S06.CertainTypeHypothesis` on the *same* Dade
    datum (`cert.dade = dade`) whose kernel is `K = H` — with `w₂ = |W₂|` prime, `W₂ ⊆ [H,H]`, and
    the Hall coprimality `gcd(|H|, |W₁|) = 1` (Peterfalvi (4.2.a): `W₁` is a cyclic *Hall* subgroup
    of `L = H ⋊ W₁`, so its order is coprime to `|H| = [L : W₁]`).  This coprimality is the input to
    Isaacs (3.28) that lifts a `W₁`-fixed coset of `H/[H,H]` to a `W₁`-fixed element of `H`.

  The (4.6)↔(6.8) renaming sets the (4.6)-kernel `K` to the (6.8) `H` (hence `cert.K = H`), and the
  (4.2)/(6.8) complement is shared (`cert.W1 = W1`, both giving `L = H ⋊ W₁`). With the S06 audit
  done (`S06.CertainTypeHypothesis` now faithfully encodes (4.2): the false `W₁ ⊔ W₂ = ⊤` removed,
  and complement / cyclic / `W₂ ≤ K` / `C_K(x) = W₂` / odd-`W` added), this matches textbook
  (6.8)(c2). -/
  cases :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H W1 ∨
    ∃ cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L,
      cert.dade = dade ∧ cert.K = H ∧ cert.W1 = W1 ∧
        (Nat.card cert.W2).Prime ∧ cert.W2 ≤ ⁅H, H⁆ ∧
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


namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- The coherence map `τ` of the (6.8) setup, realized as the genuine §4 Dade isometry
(`dadeIntegralCharacterMap`) — **not** an opaque global isometry. -/
noncomputable abbrev tau (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
    (hyp.dade.fullDadeIsometryData hyp.hconj)

/-- The (6.8) coherence target: `S` is coherent for the **real Dade map** `tau`.  This is exactly
the conclusion shape produced by the §7 engine, hence honestly dischargeable — unlike the legacy
`SibleySetup.CoherenceTarget`, which required a nonexistent global isometry. -/
abbrev CoherenceTarget (hyp : SibleyDadeHypothesis G L H) :=
  OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.S
    (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)

/-- (6.8)(a) consequence: `[L : H] = |W₁|`.  From the complement `L = H ⋊ W₁` (`hyp.split`).
This is the common degree of the members of `Y = S(H')`: by [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`), `(Ind_H^L θ)(1) = [L:H]·θ(1) = |W₁|` for the
degree-`1` characters `θ ∈ Irr(H/H')`. -/
theorem index_H_eq_card_W1 (hyp : SibleyDadeHypothesis G L H) :
    H.index = Nat.card hyp.W1 :=
  (Subgroup.IsComplement.card_right (Subgroup.isComplement'_def.mp hyp.split)).symm

/-- Degree-one source characters induce to class functions of degree |W1| in the (6.8)
setup. This is the degree side of the Y = S(Hprime) family used in the final coherence assembly. -/
theorem induce_apply_one_eq_card_W1_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L) =
      (Nat.card hyp.W1 : ℂ) := by
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ_one, mul_one,
    hyp.index_H_eq_card_W1]

/-- If two source class functions induce to the same value at 1, their induced difference is
supported on H-sharp in the (6.8) Dade support. -/
theorem support_sub_induce_subset_sharpImage_of_apply_one_eq
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : ClassFunction ↥H ℂ)
    (hone : OddOrder.RepresentationTheory.ClassFunction.induce H θ (1 : ↥L) =
      OddOrder.RepresentationTheory.ClassFunction.induce H ψ (1 : ↥L)) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H θ -
        OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  intro x hx
  have hθsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H θ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H θ
  have hψsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H ψ
  have hxH : x ∈ H := by
    rcases OddOrder.RepresentationTheory.ClassFunction.support_sub_subset
        (OddOrder.RepresentationTheory.ClassFunction.induce H θ)
        (OddOrder.RepresentationTheory.ClassFunction.induce H ψ) hx with hxθ | hxψ
    · exact hθsupp hxθ
    · exact hψsupp hxψ
  have hxne : x ≠ 1 := by
    intro hx1
    apply hx
    rw [hx1, OddOrder.RepresentationTheory.ClassFunction.sub_apply, hone, sub_self]
  change (x : G) ∈ sharpImage H
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  · intro hx1G
    exact hxne (Subtype.ext hx1G)

/-- Degree-one source characters give induced differences supported on H-sharp. -/
theorem support_sub_induce_subset_sharpImage_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hψ_one : (ψ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) -
        OddOrder.RepresentationTheory.ClassFunction.induce H (ψ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.support_sub_induce_subset_sharpImage_of_apply_one_eq
    (θ : ClassFunction ↥H ℂ) (ψ : ClassFunction ↥H ℂ) (by
      rw [hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθ_one,
        hyp.induce_apply_one_eq_card_W1_of_degree_one ψ hψ_one])

/-- Equal-degree induced irreducible families from degree-one source characters are coherent for
Sibley's Dade map. This is the engine-call form of the (6.8) Y = S(Hprime) step: once the
eta-family of irreducible induced characters is constructed and shown injective, the remaining
(1.1)+(1.4) equal-degree coherence hypotheses are discharged by the Sibley carrier. -/
noncomputable def coherentInducedDegreeOneFamily
    (hyp : SibleyDadeHypothesis G L H) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (θ : Fin n → IrreducibleCharacter ↥H) (η : Fin n → IrreducibleCharacter ↥L)
    (hη_ind : ∀ j,
      (η j : ClassFunction ↥L ℂ) =
        OddOrder.RepresentationTheory.ClassFunction.induce H (θ j : ClassFunction ↥H ℂ))
    (hηinj : Function.Injective η)
    (hθ_one : ∀ j, (θ j : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => (η j : ClassFunction ↥L ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hdeg : ∀ j, ((η j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      ((η 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    rw [hη_ind j, hη_ind 0,
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ j) (hθ_one j),
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ 0) (hθ_one 0)]
  have hsuppdiff : ∀ j,
      (OddOrder.RepresentationTheory.irreducibleCharacterDifference η j).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    simpa [OddOrder.RepresentationTheory.irreducibleCharacterDifference, hη_ind j, hη_ind 0] using
      hyp.support_sub_induce_subset_sharpImage_of_degree_one (θ j) (θ 0)
        (hθ_one j) (hθ_one 0)
  have h1notA : (1 : G) ∉ sharpImage H := by
    intro h
    exact h.2 rfl
  exact OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj hn η hηinj
    hdeg hsuppdiff h1notA

/-- **(6.8)(c2) inertia equality** for a nontrivial linear `θ`.

Under the (4.6)/(c2) data — `H ⋊ W₁`, `C_H(w) = W₂ ⊆ ⁅H,H⁆` for `w ∈ W₁∖1`, and the Hall
coprimality `gcd(|H|,|W₁|) = 1` — the inertia group of a nontrivial degree-one `θ` is exactly `H`.

Proof.  Pass to `Ḡ = L/⁅H,H⁆`, `H̄ = H/⁅H,H⁆` (abelian).  `θ` is linear, so inflates from a
nontrivial `θ̄ ∈ Irr H̄`.  The coprimality + Isaacs (3.28) lift gives `C_{H̄}(w̄) = 1` for
`w̄ ∈ W̄₁∖1`; since `H̄` is abelian, Brauer's permutation lemma turns this into "`w̄` fixes only the
trivial irreducible", so `w̄ ∉ I_{Ḡ}(θ̄)`.  The inertia-transfer bridge then gives `w ∉ I_L(θ)` for
`w ∈ W₁∖1`, and the complement `L = H ⋊ W₁` reduces a general `g ∉ H` to this case (`I_L(θ) ⊇ H`, so
the `H`-part is absorbed). -/
theorem inertia_eq_H_of_c2 (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  -- The quotient `Ḡ = L/⁅H,H⁆` and the image `H̄ = H/⁅H,H⁆`.
  set M : Subgroup ↥L := ⁅H, H⁆ with hM_def
  haveI hMnormal : M.Normal := by rw [hM_def]; infer_instance
  set mkM : ↥L →* (↥L ⧸ M) := QuotientGroup.mk' M with hmkM_def
  set Hbar : Subgroup (↥L ⧸ M) := H.map mkM with hHbar_def
  haveI hHbar_normal : Hbar.Normal := by rw [hHbar_def, hmkM_def]; infer_instance
  -- `H̄` is abelian: images of `H` commute since their commutators land in `⁅H,H⁆ = ker mkM`.
  have hHbar_comm : ∀ a b : ↥Hbar, Commute a b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [hHbar_def, Subgroup.mem_map] at ha hb
    obtain ⟨x, hxH, rfl⟩ := ha
    obtain ⟨y, hyH, rfl⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    -- `mkM x` and `mkM y` commute because `⁅x,y⁆ ∈ ⁅H,H⁆ = ker mkM`.
    have hcomm_elt : ⁅(x : ↥L), (y : ↥L)⁆ ∈ M := by
      rw [hM_def]; exact Subgroup.commutator_mem_commutator hxH hyH
    have hmk_one : mkM ⁅(x : ↥L), (y : ↥L)⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm_elt
    rw [map_commutatorElement] at hmk_one
    exact commutatorElement_eq_one_iff_mul_comm.mp hmk_one
  -- The corestriction `q : ↥H →* ↥H̄` with `(q x : Ḡ) = mkM x`.
  set q : ↥H →* ↥Hbar :=
    (mkM.comp H.subtype).codRestrict Hbar (fun x => by
      rw [hHbar_def]; exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩) with hq_def
  have hq : ∀ x : ↥H, ((q x : ↥Hbar) : ↥L ⧸ M) = mkM (x : ↥L) := fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩
    rw [hHbar_def, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz
    exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥Hbar ℂ → ClassFunction ↥H ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  -- `θ` is linear, hence kills `⁅H,H⁆.subgroupOf H = commutator ↥H`, so inflates from `H̄`.
  set N : Subgroup ↥H := M.subgroupOf H with hN_def
  haveI hN_normal : N.Normal := by rw [hN_def, hM_def]; exact hMnormal.subgroupOf H
  have hN_eq : N = _root_.commutator ↥H := by
    rw [hN_def, hM_def, ← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hker : (N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro n hn
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, hθ_one]
    -- `θ` is multiplicative with `θ(1)=1`, so `{x | θ x = 1}` is a subgroup containing commutators.
    have hθ1 : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1 := hθ_one
    have hn' : n ∈ Subgroup.closure (commutatorSet ↥H) := by
      have : n ∈ N := hn
      rwa [hN_eq, _root_.commutator_eq_closure] at this
    refine Subgroup.closure_induction
      (p := fun g _ => (θ : ClassFunction ↥H ℂ) g = 1) ?_ ?_ ?_ ?_ hn'
    · rintro _ ⟨a, b, rfl⟩
      exact θ.isIrreducible.apply_commutatorElement_eq_one_of_apply_one_eq_one hθ1 a b
    · exact hθ1
    · intro a b _ _ ha hb
      rw [θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1, ha, hb, one_mul]
    · intro a _ ha
      have hai := θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1 a a⁻¹
      rw [mul_inv_cancel, hθ1, ha, one_mul] at hai
      exact hai.symm
  have hkerq : q.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    change q x = 1 ↔ (x : ↥L) ∈ M
    constructor
    · intro hx
      have hx1 : mkM (x : ↥L) = 1 := by rw [← hq x, hx]; rfl
      rw [hmkM_def] at hx1
      exact (QuotientGroup.eq_one_iff _).mp hx1
    · intro hx
      apply Subtype.ext
      rw [hq x, hmkM_def]
      exact (QuotientGroup.eq_one_iff _).mpr hx
  -- `θ` inflates from a `θ̄ : Irr ↥H̄` along the surjection `q` (linear ⟹ `ker q = N ⊆ ker θ`).
  obtain ⟨θbar, hcompq⟩ :=
    exists_compHom_eq_of_subset_characterKernel hq_surj θ (by rw [hkerq]; exact hker)
  -- `θ̄` is nontrivial, else `θ = compHom q (triv) = triv`.
  have hθbar_ne : θbar ≠ trivialIrreducibleCharacter ↥Hbar := by
    intro hbar
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hcompq, hbar]
    ext x
    simp [ClassFunction.compHom_apply, trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  -- **B1′** (fixed-point-free action of `W̄₁` on `H̄`): `C_{H̄}(w̄) = 1` for `w̄ ∈ W̄₁∖1`.
  -- We only need the specific `w̄ = mkM w`; the S03 `≤ N` quotient lemma supplies it.
  have hNK : (⁅H, H⁆ : Subgroup ↥L) ≤ H := Subgroup.commutator_le_left H H
  have hcentral : ∀ x ∈ hyp.W1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥L) ⊓ H ≤ M := by
    intro x hxW1 hxne
    have hcw2 : Subgroup.centralizer ({x} : Set ↥L) ⊓ cert.K = cert.W2 :=
      cert.centralizer_W2 x (hW1 ▸ hxW1) hxne
    rw [hK] at hcw2
    rw [hcw2, hM_def]; exact hW2
  have hlift : ∀ x ∈ hyp.W1, x ≠ 1 → ∀ y ∈ H,
      mkM (x * y * x⁻¹) = mkM y →
        ∃ c : ↥L, c ∈ H ∧ mkM c = mkM y ∧ x * c * x⁻¹ = c := by
    intro x hxW1 hxne y hyH hfix
    have hcop_x : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥H) := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ Nat.card hyp.W1 := hyp.W1.orderOf_dvd_natCard hxW1
      exact (hcop.coprime_dvd_right hdvd).symm
    exact OddOrder.BG.Ch1.S03.fixedPoint_lift_of_generator_quotient_fixed
      hNK hcop_x (Or.inl (by infer_instance)) hyH hfix
  have hB1 : ∀ qx ∈ hyp.W1.map mkM, qx ≠ 1 →
      Subgroup.centralizer ({qx} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ := by
    rw [hHbar_def, hmkM_def]
    exact OddOrder.BG.Ch1.S03.quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift_of_le
      hcentral hlift
  -- Assemble: `I_L(θ) = H` by `le_antisymm`.
  apply le_antisymm
  · -- `I_L(θ) ≤ H`: a `g ∉ H` is `h·w` with `w ∈ W₁∖1`, and `w ∉ I_L(θ)`.
    intro g hg
    by_contra hgH
    -- Write `g = h * w` via the complement `L = H ⋊ W₁`.
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    -- `w ≠ 1`, else `g = h ∈ H`.
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1
      apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    -- `h ∈ H ⊆ I_L(θ)`, so `w = h⁻¹·g ∈ I_L(θ)`.
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).mul_mem
        ((ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).inv_mem hhinertia)
        (ClassFunction.mem_inertia.mpr hg)
    -- Transfer `w ∈ I_L(θ)` to `w̄ ∈ I_{Ḡ}(θ̄)`.
    rw [← hcompq] at hwinertia
    have hwbar : mkM (w : ↥L) ∈ ClassFunction.inertia (θbar : ClassFunction ↥Hbar ℂ) :=
      (mem_inertia_compHom_iff q hq hqinj (θbar : ClassFunction ↥Hbar ℂ) (w : ↥L)).mp hwinertia
    -- But `w̄ ∉ I_{Ḡ}(θ̄)`: `C_{H̄}(w̄) = 1`, abelian Brauer, `θ̄ ≠ triv`.
    have hwbar_mem : mkM (w : ↥L) ∈ hyp.W1.map mkM :=
      Subgroup.mem_map.mpr ⟨w, w.property, rfl⟩
    have hwbar_ne : mkM (w : ↥L) ≠ 1 := by
      intro hw1
      have hwM : (w : ↥L) ∈ M := by
        rw [hmkM_def, QuotientGroup.mk'_apply] at hw1
        exact (QuotientGroup.eq_one_iff _).mp hw1
      exact hwne (Subgroup.disjoint_def.mp hyp.split.disjoint (hNK (hM_def ▸ hwM)) w.property)
    have hfree : Subgroup.centralizer ({mkM (w : ↥L)} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ :=
      hB1 (mkM (w : ↥L)) hwbar_mem hwbar_ne
    have hclass : Nat.card (Function.fixedPoints
        (ConjClasses.conjByPerm (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)))) = 1 :=
      card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot
        (mkM (w : ↥L)) hHbar_comm hfree
    exact not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one
      (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)) hclass hθbar_ne hwbar
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **(T7-c2 case A) Inertia `I_L(θ) = H`** via the **fixed-point-free action on `Z`**.  Here
`Z ≤ H` is central in `H` (`Z.subgroupOf H ≤ Z(H)`), normalized by `W₁`, with `W₁∖1` acting
fixed-point-freely (`C_Z(w) = Z ∩ W₂ = 1` in case A).  If `w ∈ W₁∖1` fixed `θ`, the central linear
character `φ` of `Res_Z θ` ([Is] 2.27) would be `σ = (·)^w`-invariant, hence `≡ 1`
(`eq_one_of_fixedPointFree_invariant`), forcing `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
So `I_L(θ) ∩ W₁ = 1` and the complement split `L = H ⋊ W₁` gives `I_L(θ) = H`.  Needs no Hall
coprimality and works for an arbitrary (not necessarily linear) `θ`. -/
theorem inertia_eq_H_of_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {θ : IrreducibleCharacter ↥H}
    (hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  obtain ⟨φ, hφirr, hφ1, -, hφpt⟩ :=
    θ.isIrreducible.exists_central_linear_restriction (Z.subgroupOf H) hZcentral
  have hφmul : ∀ a b : ↥(Z.subgroupOf H), φ (a * b) = φ a * φ b :=
    hφirr.map_mul_of_apply_one_eq_one hφ1
  have hθ1_ne : (θ : ClassFunction ↥H ℂ) 1 ≠ 0 := by
    obtain ⟨n, hpos, hn1, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
    rw [hn1]; exact_mod_cast hpos.ne'
  apply le_antisymm
  · intro g hg
    by_contra hgH
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1; apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia _).mul_mem
        ((ClassFunction.inertia _).inv_mem hhinertia) (ClassFunction.mem_inertia.mpr hg)
    have hwW1 : (w : ↥L) ∈ hyp.W1 := w.property
    -- Conjugation `σ` by `w` on `Z`, fixed-point-free (`C_Z(w) = Z ∩ W₂ = 1`).
    set σ : MulAut ↥Z := Z.normalizerMonoidHom ⟨(w : ↥L), hZnorm (w : ↥L) hwW1⟩ with hσ_def
    have hσval : ∀ z : ↥Z, ((σ z : ↥Z) : ↥L) = (w : ↥L) * (z : ↥L) * (w : ↥L)⁻¹ := fun _ => rfl
    have hσfpf : MonoidHom.FixedPointFree σ := by
      intro z hz
      have hzmem : ((z : ↥Z) : ↥L) ∈ Subgroup.centralizer ({(w : ↥L)} : Set ↥L) ⊓ Z := by
        refine Subgroup.mem_inf.mpr ⟨?_, z.property⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        have hzL := congrArg (Subtype.val : ↥Z → ↥L) hz
        rw [hσval] at hzL
        rw [mul_inv_eq_iff_eq_mul] at hzL
        exact hzL
      rw [hZfpf (w : ↥L) hwW1 hwne, Subgroup.mem_bot] at hzmem
      exact Subtype.ext hzmem
    -- `f = φ ∘ iso` is multiplicative and `σ`-invariant; brick ① gives `φ ≡ 1`.
    set iso : ↥Z ≃* ↥(Z.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hZH).symm with hiso_def
    have hisoL : ∀ z : ↥Z, (((iso z : ↥(Z.subgroupOf H)) : ↥H) : ↥L) = (z : ↥L) := fun _ => rfl
    set f : ↥Z → ℂ := fun z => φ (iso z) with hf_def
    have hfmul : ∀ a b : ↥Z, f (a * b) = f a * f b := fun a b => by
      simp only [hf_def, map_mul, hφmul]
    have hfone : f 1 = 1 := by simp only [hf_def, map_one, hφ1]
    have hfinv : ∀ z : ↥Z, f (σ z) = f z := by
      intro z
      have hconj : ClassFunction.conjBy (w : ↥L) (θ : ClassFunction ↥H ℂ)
          = (θ : ClassFunction ↥H ℂ) := ClassFunction.mem_inertia.mp hwinertia
      have hval : (θ : ClassFunction ↥H ℂ) ((iso (σ z) : ↥(Z.subgroupOf H)) : ↥H)
          = (θ : ClassFunction ↥H ℂ) ((iso z : ↥(Z.subgroupOf H)) : ↥H) := by
        have hc := congrArg (fun ψ : ClassFunction ↥H ℂ => ψ ((iso z : ↥(Z.subgroupOf H)) : ↥H))
          hconj
        simp only [ClassFunction.conjBy_apply] at hc
        rw [← hc]
        congr 1
      have e1 := hφpt (iso (σ z))
      have e2 := hφpt (iso z)
      have hmul : φ (iso (σ z)) * (θ : ClassFunction ↥H ℂ) 1
          = φ (iso z) * (θ : ClassFunction ↥H ℂ) 1 := by rw [← e1, hval]; exact e2
      simp only [hf_def]
      exact mul_right_cancel₀ hθ1_ne hmul
    -- `φ ≡ 1` forces `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
    apply hZker
    intro x hx
    rw [SetLike.mem_coe] at hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have hφx : φ (⟨x, hx⟩ : ↥(Z.subgroupOf H)) = 1 := by
      have hfx := eq_one_of_fixedPointFree_invariant hσfpf hfmul hfone hfinv
        (iso.symm ⟨x, hx⟩)
      simpa only [hf_def, MulEquiv.apply_symm_apply] using hfx
    have hpt := hφpt (⟨x, hx⟩ : ↥(Z.subgroupOf H))
    rw [hφx, one_mul] at hpt
    exact hpt
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **Peterfalvi (6.8) Y-family irreducibility.**  For a nontrivial degree-one (linear) source
character `θ` of `H`, the induced character `Ind_H^L θ` is irreducible.  Inertia `I_L(θ) = H`
(free action of `W₁`) is discharged via the (6.8)(c) disjunction and fed to [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`):

* **(c1)** `L` Frobenius with kernel `H`: `isIrreducibleCharacter_induce_of_frobeniusGroup`
  (needs only `θ ≠ 1`; degree-one not used).
* **(c2)** Hyp (4.6): the inertia bridge `inertia_eq_H_of_c2` from
  `CertainTypeHypothesis.centralizer_W2` + Hall coprimality + Isaacs 3.28 on `H/H'` (T6 §5). -/
theorem isIrreducibleCharacter_induce_of_degree_one (hyp : SibleyDadeHypothesis G L H)
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rcases hyp.cases with hF | ⟨cert, _hdade, hK, hW1, _hprime, hW2, hcop⟩
  · exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne
  · -- (c2) inertia bridge: `I_L(θ) = H` via the abelian quotient `H/⁅H,H⁆` (Brauer + Isaacs 3.28).
    exact isIrreducibleCharacter_induce_of_inertia_eq θ
      (hyp.inertia_eq_H_of_c2 cert hK hW1 hW2 hcop hθ_one hθ_ne)

/-- **(6.8) `Y = S(H')` coherence (engine call from a constructed family).**  Given a family of
nontrivial linear source characters `χ_j : H →* ℂˣ` indexed by `Fin n` (`n ≥ 2`), pairwise
non-`L`-conjugate, with each `Ind_H^L (linear χ_j)` irreducible (`hirr`), the induced family
`Y = {Ind_H^L (linear χ_j)}` is coherent for Sibley's Dade map `tau`.

This is the (6.8) `Y`-step: the `χ_j` are the `Irr(H/H') ∖ {1}` orbit representatives (degree one,
so each `Ind` has the common degree `|W₁|`).  `hirr` and the pairwise non-conjugacy come from the
free `W₁`-action (`isIrreducibleCharacter_induce_of_degree_one`).  Injectivity of
`j ↦ Ind_H^L (linear χ_j)` is the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`;
the equal-degree coherence is then `coherentInducedDegreeOneFamily`. -/
noncomputable def coherentYFamily (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j))
    (hirr : ∀ j, IsIrreducibleCharacter
      (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hηinj : Function.Injective
      (fun j => (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
        hirr j⟩ : IrreducibleCharacter ↥L)) := by
    intro i j hij
    by_contra hne
    have h0 := inner_induce_eq_zero_of_not_conj
      (linearIrreducibleCharacter (χ i)) (linearIrreducibleCharacter (χ j))
      (fun g => hpairwise i j hne g)
    have hcoe : ClassFunction.induce H (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
        ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      congrArg Subtype.val hij
    rw [hcoe] at h0
    have h1 : ClassFunction.inner
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
          hirr j⟩ : IrreducibleCharacter ↥L)
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ), hirr j⟩)
    rw [h1] at h0
    exact one_ne_zero h0
  exact coherentInducedDegreeOneFamily hyp hn
    (fun j => linearIrreducibleCharacter (χ j))
    (fun j => ⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
      hirr j⟩)
    (fun _ => rfl) hηinj (fun j => linearIrreducibleCharacter_apply_one (χ j))

/-- **(6.8) `Y = S(H')` coherence, with induced irreducibility discharged internally.**
Compared with `coherentYFamily`, the caller supplies only nontrivial linear source characters and
pairwise non-`L`-conjugacy.  The irreducibility of each induced member is the genuine T6/c1-c2
brick `isIrreducibleCharacter_induce_of_degree_one`, not an extra hypothesis. -/
noncomputable def coherentYFamily_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.coherentYFamily hn χ hpairwise ?_
  intro j
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one (χ j)) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne j)

/-! ### Peterfalvi (6.8) `X`-characterization (T7): the sets `S(A)`, `X = S − S(Z)`, `Y = S(H')`

mmd 04.8 L150-164.  The (6.8) proof denotes `H' = [H,H]`, sets `Z = Z(H) ∩ H'` in case (A) and
`Z = W₂` in case (B), and forms `X = S − S(Z)`, `Y = S(H')` (`Z ⊆ H'` makes `X ∩ Y = ∅`).
`S(A)` is the (6.1) filtration: the members of `S` whose source `θ` has `A` in its kernel. -/

/-- **Peterfalvi (6.1) filtration `S(A)`** in the (6.8) setup: the members `Ind_H^L θ` of `S`
(`θ ∈ Irr H`, `θ ≠ 1_H`) whose source `θ` has `A` (as a subgroup of `H`) inside its kernel.
`S(1) = S`, and the (6.8) sets are `X = S − S(Z)` and `Y = S(H')`. -/
def SsubFiltration (_hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    (A.subgroupOf H : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}

/-- The (6.8) set `X = S − S(Z)` (the (6.6) `X`-set) for a normal `Z ⊆ Z(H)`. -/
def Xset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  hyp.S \ hyp.SsubFiltration Z

/-- The (6.8) set `Y = S(H')` (`H' = [H,H]`), the equal-degree family handled by T6. -/
def Yset (hyp : SibleyDadeHypothesis G L H) : Set (ClassFunction ↥L ℂ) :=
  hyp.SsubFiltration ⁅H, H⁆

/-- Membership in `S(A)`, unfolded. -/
theorem mem_SsubFiltration (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.SsubFiltration A ↔ ∃ θ : IrreducibleCharacter ↥H,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
      (A.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
      φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
  Iff.rfl

/-- Membership in `X = S − S(Z)`, unfolded. -/
theorem mem_Xset (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Xset Z ↔ φ ∈ hyp.S ∧ φ ∉ hyp.SsubFiltration Z :=
  Iff.rfl

/-- Every member of the filtration `S(A)` is a member of the ambient set `S`. -/
theorem SsubFiltration_subset_S (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L} :
    hyp.SsubFiltration A ⊆ hyp.S := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, _hker, hφeq⟩ := hφ
  rw [hyp.S_eq]
  exact ⟨θ, hθ_ne, hφeq⟩

/-- `X(Z) = S - S(Z)` is contained in `S`. -/
theorem Xset_subset_S (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} :
    hyp.Xset Z ⊆ hyp.S := by
  intro φ hφ
  exact (hyp.mem_Xset.mp hφ).1

/-- `Y = S(H')` is contained in `S`. -/
theorem Yset_subset_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Yset ⊆ hyp.S := by
  intro φ hφ
  rw [Yset] at hφ
  exact hyp.SsubFiltration_subset_S hφ

/-- `X(Z) = S - S(Z)` is disjoint from `S(Z)`. -/
theorem disjoint_Xset_SsubFiltration
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Disjoint (hyp.Xset Z) (hyp.SsubFiltration Z) := by
  rw [Set.disjoint_left]
  intro φ hφX hφZ
  exact (hyp.mem_Xset.mp hφX).2 hφZ

/-- `X(Z)` and `S(Z)` partition `S`. -/
theorem Xset_union_SsubFiltration_eq_S
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.Xset Z ∪ hyp.SsubFiltration Z = hyp.S := by
  ext φ
  constructor
  · intro hφ
    rcases hφ with hφX | hφZ
    · exact hyp.Xset_subset_S hφX
    · exact hyp.SsubFiltration_subset_S hφZ
  · intro hφS
    by_cases hφZ : φ ∈ hyp.SsubFiltration Z
    · exact Or.inr hφZ
    · exact Or.inl (hyp.mem_Xset.mpr ⟨hφS, hφZ⟩)

/-- The Peterfalvi filtration is antitone: a larger subgroup imposes a stronger kernel
condition. -/
theorem SsubFiltration_antitone
    (hyp : SibleyDadeHypothesis G L H) {A B : Subgroup ↥L} (hAB : A ≤ B) :
    hyp.SsubFiltration B ⊆ hyp.SsubFiltration A := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  refine ⟨θ, hθ_ne, ?_, hφeq⟩
  intro x hxA
  exact hker (Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hxA)))

/-- `X(A) = S - S(A)` grows with the subgroup parameter. -/
theorem Xset_mono
    (hyp : SibleyDadeHypothesis G L H) {A B : Subgroup ↥L} (hAB : A ≤ B) :
    hyp.Xset A ⊆ hyp.Xset B := by
  intro φ hφ
  obtain ⟨hφS, hφnotA⟩ := hyp.mem_Xset.mp hφ
  exact hyp.mem_Xset.mpr ⟨hφS, fun hφB => hφnotA (hyp.SsubFiltration_antitone hAB hφB)⟩

/-- If `Z ≤ H'`, then the larger capstone set `S - S(H')` splits into the smaller
`X(Z) = S - S(Z)` plus the filtration layer between `Z` and `H'`.  This is the set-theoretic
bridge needed by the case-A/case-B route, where the textbook first proves coherence for a smaller
central/fixed-point-free subgroup `Z`. -/
theorem Xset_commutator_eq_Xset_union_filtrationDiff
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} (hZH' : Z ≤ ⁅H, H⁆) :
    hyp.Xset ⁅H, H⁆ =
      hyp.Xset Z ∪ (hyp.SsubFiltration Z \ hyp.SsubFiltration ⁅H, H⁆) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨hφS, hφnotH'⟩ := hyp.mem_Xset.mp hφ
    by_cases hφZ : φ ∈ hyp.SsubFiltration Z
    · exact Or.inr ⟨hφZ, hφnotH'⟩
    · exact Or.inl (hyp.mem_Xset.mpr ⟨hφS, hφZ⟩)
  · rintro (hφZ | ⟨hφFilZ, hφnotH'⟩)
    · exact hyp.Xset_mono hZH' hφZ
    · exact hyp.mem_Xset.mpr ⟨hyp.SsubFiltration_subset_S hφFilZ, hφnotH'⟩

/-- The (6.8) sets `X = S - S(H')` and `Y = S(H')` are disjoint. -/
theorem disjoint_Xset_Yset (hyp : SibleyDadeHypothesis G L H) :
    Disjoint (hyp.Xset ⁅H, H⁆) hyp.Yset := by
  simpa [Yset] using hyp.disjoint_Xset_SsubFiltration (Z := ⁅H, H⁆)

/-- The (6.8) sets `X = S - S(H')` and `Y = S(H')` partition `S`. -/
theorem Xset_union_Yset_eq_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Xset ⁅H, H⁆ ∪ hyp.Yset = hyp.S := by
  simpa [Yset] using hyp.Xset_union_SsubFiltration_eq_S (Z := ⁅H, H⁆)

/-- A nontrivial linear source character induces to a member of `Y = S(H')`.

The witness in `S(H')` is `linearIrreducibleCharacter χ`.  Its kernel contains
`H' = [H,H]` because a degree-one character kills commutators. -/
theorem induce_linearIrreducibleCharacter_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {χ : ↥H →* ℂˣ}
    (hχ_ne : χ ≠ 1) :
    ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) ∈
      hyp.Yset := by
  rw [Yset]
  refine ⟨linearIrreducibleCharacter χ, ?_, ?_, rfl⟩
  · rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
    exact hχ_ne
  · intro x hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, linearIrreducibleCharacter_apply_one]
    have hsubgroupOf_eq :
        ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
      rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [hsubgroupOf_eq] at hx
    have hxclosure : x ∈ Subgroup.closure (commutatorSet ↥H) := by
      rwa [_root_.commutator_eq_closure] at hxcomm
    refine Subgroup.closure_induction
      (p := fun y _ => (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) y = 1)
      ?_ ?_ ?_ ?_ hxclosure
    · rintro _ ⟨a, b, rfl⟩
      have hlin := (linearIrreducibleCharacter χ).isIrreducible
      exact hlin.apply_commutatorElement_eq_one_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a b
    · exact linearIrreducibleCharacter_apply_one χ
    · intro a b _ _ ha hb
      rw [(linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ), ha, hb, one_mul]
    · intro a _ ha
      have hai := (linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a a⁻¹
      rw [mul_inv_cancel, linearIrreducibleCharacter_apply_one χ, ha, one_mul] at hai
      exact hai.symm


/-- A source character whose kernel contains `H'` comes from a linear character of `H`.

The proof factors the source through the abelianization `H/H'`; irreducible characters of a finite
commutative group are degree one, hence are `linearIrreducibleCharacter`s, and pulling that linear
character back along `Abelianization.of` recovers the original source. -/
theorem exists_linearIrreducibleCharacter_eq_of_YsetSource
    (_hyp : SibleyDadeHypothesis G L H) {θ : IrreducibleCharacter ↥H}
    (hker : (((⁅H, H⁆ : Subgroup ↥L).subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    ∃ χ : ↥H →* ℂˣ,
      (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) = (θ : ClassFunction ↥H ℂ) := by
  classical
  have hsubgroupOf_eq :
      ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
    rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  let q : ↥H →* Abelianization ↥H := Abelianization.of
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥H) y
    exact ⟨x, rfl⟩
  have hker_q :
      ((q.ker : Subgroup ↥H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro x hx
    apply hker
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [show q.ker = _root_.commutator ↥H by
        change Abelianization.of.ker = _root_.commutator ↥H
        exact Abelianization.ker_of ↥H] at hx
    rwa [hsubgroupOf_eq]
  obtain ⟨θbar, hθbar⟩ := exists_compHom_eq_of_subset_characterKernel hq_surj θ hker_q
  haveI : Finite (Abelianization ↥H) := Finite.of_surjective q hq_surj
  obtain ⟨χbar, hχbar⟩ :=
    θbar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  refine ⟨χbar.comp q, ?_⟩
  rw [← ClassFunction.compHom_linearIrreducibleCharacter, hχbar, hθbar]

/-- Every member of `Y = S(H')` is induced from a nontrivial linear character of `H`. -/
theorem exists_linear_source_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  rw [Yset, SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, hker, hφ⟩ := hφ
  obtain ⟨χ, hχθ⟩ := hyp.exists_linearIrreducibleCharacter_eq_of_YsetSource hker
  refine ⟨χ, ?_, ?_⟩
  · intro hχ
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hχθ]
    exact congrArg (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ))
      ((linearIrreducibleCharacter_eq_trivial_iff (χ := χ)).mpr hχ)
  · rw [hφ, ← hχθ]

/-- `Y = S(H')` is exactly the image of the nontrivial linear characters of `H` under induction. -/
theorem mem_Yset_iff_exists_linear_source
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Yset ↔ ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  constructor
  · exact hyp.exists_linear_source_of_mem_Yset
  · rintro ⟨χ, hχ_ne, rfl⟩
    exact hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne

/-- Family form of `induce_linearIrreducibleCharacter_mem_Yset`. -/
theorem range_induce_linearIrreducibleCharacter_subset_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ}
    (χ : Fin n → (↥H →* ℂˣ)) (hχ_ne : ∀ j, χ j ≠ 1) :
    Set.range (fun j => ClassFunction.induce H
      (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) ⊆ hyp.Yset := by
  rintro φ ⟨j, rfl⟩
  exact hyp.induce_linearIrreducibleCharacter_mem_Yset (hχ_ne j)

/-- If an index family covers all nontrivial linear sources after induction, its induced range is
exactly `Y = S(H')`.

This is the orbit-representative form needed for (6.8): the family need only hit each induced
character in `Y`, not each nontrivial linear source before quotienting by `L`-conjugacy. -/
theorem range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {ι : Type*}
    (χ : ι → (↥H →* ℂˣ)) (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η)) :
    Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  ext φ
  constructor
  · rintro ⟨j, rfl⟩
    simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset (hχ_ne j)
  · intro hφ
    obtain ⟨η, hη_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    obtain ⟨j, hηj⟩ := hχ_cover η hη_ne
    refine ⟨j, ?_⟩
    rw [hφeq, linearIrreducibleCharacter_coe]
    exact hηj

/-- There are finitely many linear characters `Γ →* ℂˣ` for a finite group `Γ`.

Local to §8 because the immediate consumer is the finiteness of `Y = S(H')`; a more global API can
move this later if it gets reused outside the Peterfalvi assembly. -/
theorem finite_linearCharacters_of_finite {Γ : Type*} [Group Γ] [Finite Γ] :
    Finite (Γ →* ℂˣ) := by
  haveI : Finite (IrreducibleCharacter Γ) := finite_irreducibleCharacter (G := Γ)
  exact Finite.of_injective (linearIrreducibleCharacter (H := Γ))
    linearIrreducibleCharacter_injective

/-- `Y = S(H')` is finite: it is covered by inducing the finite set of nontrivial
linear source characters of `H`. -/
theorem Yset_finite (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Finite := by
  classical
  haveI : Finite (↥H →* ℂˣ) := finite_linearCharacters_of_finite (Γ := ↥H)
  let T : Set (↥H →* ℂˣ) := {χ | χ ≠ 1}
  refine ((Set.toFinite T).image
    (fun χ => ClassFunction.induce H (linearClassFunction χ))).subset ?_
  intro φ hφ
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  refine ⟨χ, hχ_ne, ?_⟩
  rw [hφeq, linearIrreducibleCharacter_coe]

/-- Every member of `Y = S(H')` is irreducible. -/
theorem isIrreducibleCharacter_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    IsIrreducibleCharacter φ := by
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [hφeq]
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one χ) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne)

/-- Disjoint families of irreducible characters are orthogonal after passing to their
integer spans. -/
theorem inner_eq_zero_of_mem_span_of_disjoint_irreducible
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X Y : Set (ClassFunction Γ ℂ)}
    (hXirr : ∀ χ ∈ X, IsIrreducibleCharacter χ)
    (hYirr : ∀ η ∈ Y, IsIrreducibleCharacter η)
    (hdisj : Disjoint X Y) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem χ hχ =>
      intro v hv
      refine OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan ?_ hv
      intro η hη
      have hχη : χ ≠ η := by
        intro h
        exact (Set.disjoint_left.mp hdisj) hχ (by simpa [← h] using hη)
      have hχirr : IsIrreducibleCharacter χ := hXirr χ hχ
      have hηirr : IsIrreducibleCharacter η := hYirr η hη
      have hneq :
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ≠ ⟨η, hηirr⟩ := by
        intro h
        exact hχη (congrArg Subtype.val h)
      simpa [hneq] using
        irreducibleCharacter_inner_eq_ite
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ⟨η, hηirr⟩
  | zero =>
      intro v _hv
      exact ClassFunction.inner_zero_left v
  | add x y _hx _hy ihx ihy =>
      intro v hv
      rw [ClassFunction.inner_add_left, ihx v hv, ihy v hv, zero_add]
  | smul a x _hx ih =>
      intro v hv
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih v hv, mul_zero]

/-- Source-side orthogonality of the (6.8) partition `X = S - S(H')` and `Y = S(H')`,
assuming the `X` side has already been shown irreducible. -/
theorem inner_span_Xset_Yset_eq_zero_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ) :
    ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0 := by
  letI : H.Normal := hyp.H_normal
  exact inner_eq_zero_of_mem_span_of_disjoint_irreducible hXirr
    (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hyp.disjoint_Xset_Yset

/-- Enumerating `Yset` gives nontrivial linear source representatives for its induced members.

The returned family is indexed by `Fin n`, covers `Yset` after induction, and is pairwise
non-`L`-conjugate.  The cardinal lower bound is kept as an explicit input because the later
coherence engine requires `2 ≤ n`. -/
theorem exists_Yset_linearRepresentativeFamily
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    ∃ (n : ℕ) (_ : NeZero n) (χ : Fin n → ↥H →* ℂˣ),
      2 ≤ n ∧
      (∀ j, χ j ≠ 1) ∧
      (∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
        ClassFunction.induce H (linearClassFunction (χ j)) =
          ClassFunction.induce H (linearClassFunction η)) ∧
      (∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
        IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
          linearIrreducibleCharacter (χ j)) ∧
      Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  classical
  obtain ⟨n, ζ, hζinj, hζrange⟩ :=
    exists_finEnum_irreducible (hyp.Yset_finite)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ)
  have hζmem : ∀ j, (ζ j : ClassFunction ↥L ℂ) ∈ hyp.Yset := by
    intro j
    rw [← hζrange]
    exact Set.mem_range_self j
  choose χ hχ_ne hχeq using fun j => hyp.exists_linear_source_of_mem_Yset (hζmem j)
  have hindRange : Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) =
      hyp.Yset := by
    ext φ
    constructor
    · rintro ⟨j, rfl⟩
      have hζeq :
          (ζ j : ClassFunction ↥L ℂ) =
            ClassFunction.induce H (linearClassFunction (χ j)) := by
        simpa [linearIrreducibleCharacter_coe] using hχeq j
      change ClassFunction.induce H (linearClassFunction (χ j)) ∈ hyp.Yset
      rw [← hζeq]
      exact hζmem j
    · intro hφ
      rw [← hζrange] at hφ
      obtain ⟨j, hj⟩ := hφ
      refine ⟨j, ?_⟩
      rw [← hj]
      simpa [linearIrreducibleCharacter_coe] using (hχeq j).symm
  have hcover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η) := by
    intro η hη_ne
    have hmem : ClassFunction.induce H (linearClassFunction η) ∈ hyp.Yset := by
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_linearIrreducibleCharacter_mem_Yset hη_ne
    rw [← hindRange] at hmem
    exact hmem
  have hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j) := by
    intro i j hij g hconj
    apply hij
    apply hζinj
    apply IrreducibleCharacter.ext
    have hind :
        ClassFunction.induce H
            (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
          ClassFunction.induce H
            (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      (induce_eq_induce_iff_conj
        (G := ↥L) (H := H)
        (linearIrreducibleCharacter (χ i))
        (linearIrreducibleCharacter (χ j))).mpr ⟨g, hconj⟩
    rw [hχeq i, hχeq j]
    exact hind
  have hcoeinj : Function.Injective (fun j => (ζ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hζinj (IrreducibleCharacter.ext hij)
  have hncard : hyp.Yset.ncard = n := by
    rw [← hζrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨n, inferInstance, χ, hn2, hχ_ne, hcover, hpairwise, hindRange⟩

/-- `Y = S(H')` coherence from finite orbit representatives of nontrivial linear characters.

The caller supplies representatives whose induced characters cover `Y`, together with the usual
pairwise non-`L`-conjugacy input that makes the constructed family orthonormal.  The exact range
equality rewrites `coherentYFamily` from the constructed range to `hyp.Yset`. -/
noncomputable def coherentYset_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hcoh := hyp.coherentYFamily_of_pairwiseNonconj hn χ hχ_ne hpairwise
  have hrange :=
    hyp.range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective χ hχ_ne hχ_cover
  simpa [hrange] using hcoh

/-- `Y = S(H')` coherence from the finite `Yset` representative construction.

This packages `exists_Yset_linearRepresentativeFamily` with the concrete coherence engine; the
remaining downstream input is the cardinal lower bound `2 ≤ |Y|`. -/
noncomputable def coherentYset_of_two_le_ncard
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  choose n hnzero χ hn2 hχ_ne hχ_cover hpairwise _hrange using
    hyp.exists_Yset_linearRepresentativeFamily hYtwo
  letI : NeZero n := hnzero
  exact hyp.coherentYset_of_pairwiseNonconj hn2 χ hχ_ne hχ_cover hpairwise

/-- `Y = S(H')` is nonempty.

The nontrivial nilpotent group `H` is solvable, hence has proper commutator subgroup.  The
abelianization therefore has a nontrivial linear character, whose induced character lies in
`Yset`. -/
theorem Yset_nonempty (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Nonempty := by
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcomm : _root_.commutator ↥H ≠ ⊤ :=
    (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H)).ne
  obtain ⟨χ, hχ_ne⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top hcomm
  exact ⟨ClassFunction.induce H (linearClassFunction χ),
    by simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne⟩

/-- `Y = S(H')` contains no real characters.

Each member of `Yset` is an irreducible induced character of degree `|W₁|`; since `W₁` is
nontrivial this degree is not `1`, so the member is not the trivial irreducible character.  Odd
order of `L` then gives non-realness by Peterfalvi (1.1). -/
theorem Yset_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Yset := by
  intro φ hφ hreal
  let η : IrreducibleCharacter ↥L := ⟨φ, hyp.isIrreducibleCharacter_of_mem_Yset hφ⟩
  have hη_ne : η ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro hη
    have hφ_one_triv : φ (1 : ↥L) = 1 := by
      have h := congrArg (fun ψ : IrreducibleCharacter ↥L =>
        (ψ : ClassFunction ↥L ℂ) (1 : ↥L)) hη
      simpa [η, trivialClassFunction_apply] using h
    obtain ⟨χ, _hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    have hφ_one : φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) := by
      rw [hφeq]
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_apply_one_eq_card_W1_of_degree_one
          (linearIrreducibleCharacter χ) (linearIrreducibleCharacter_apply_one χ)
    have hcard_ne : (Nat.card hyp.W1 : ℂ) ≠ 1 := by
      have hcard_nat : Nat.card hyp.W1 ≠ 1 := by
        intro hcard
        exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp hcard)
      exact_mod_cast hcard_nat
    exact hcard_ne (hφ_one.symm.trans hφ_one_triv)
  exact (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd hη_ne) hreal

/-- `Y = S(H')` is closed under complex conjugation. -/
theorem Yset_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.Yset := by
  intro φ hφ
  rw [Yset, SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, ?_, ?_, ?_⟩
  · intro hθc
    apply hθ_ne
    apply IrreducibleCharacter.ext
    have hval : (θ : ClassFunction ↥H ℂ).conj =
        (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
      simpa [θc] using congrArg
        (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ)) hθc
    calc
      (θ : ClassFunction ↥H ℂ) = ((θ : ClassFunction ↥H ℂ).conj).conj := by
        rw [ClassFunction.conj_conj]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ).conj := by
        rw [hval]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
        ext x
        simp
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- `Y = S(H')` has at least two members. -/
theorem two_le_Yset_ncard (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    2 ≤ hyp.Yset.ncard :=
  OddOrder.Peterfalvi.S07.two_le_ncard_of_conjugate_closed_of_noReal
    hyp.Yset_finite
    hyp.Yset_nonempty
    hyp.Yset_closedUnderConjugate
    hyp.Yset_hasNoRealCharacters

/-- `Y = S(H')` coherence, with the cardinal lower bound discharged internally. -/
noncomputable def coherentYset (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentYset_of_two_le_ncard hyp.two_le_Yset_ncard

/-- Glue `X = S - S(H')` coherence with the internally constructed `Y = S(H')` coherence.

This is the final algebraic assembly shape needed by Peterfalvi (6.8): callers still provide the
case-dependent `X` coherence and the two orthogonality/agreement inputs, but the `Y` side and the
set-theoretic rewrite from `X ∪ Y` to `S` are discharged here. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  let hY := hyp.coherentYset
  have hU : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
    OddOrder.Peterfalvi.S07.coherentUnion_of_glued
      (hX := hX) (hY := hY) ν hagreeX hagreeY hsrc_ortho himg_ortho hgen
  simpa [hyp.Xset_union_Yset_eq_S] using hU

/-- Variant of the (6.8) glue step where source-side orthogonality is discharged from
irreducibility of the `X` side and disjointness of the `X/Y` partition. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  letI : H.Normal := hyp.H_normal
  exact hyp.coherentS_of_Xset_commutator_Yset_glued hX ν hagreeX hagreeY
    (hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X hXirr) himg_ortho hgen

/-- Variant of the (6.8) glue step where source-side orthogonality is discharged from
irreducibility of `X`, and image-side orthogonality is discharged from mixed inner preservation
of the glued map `ν`. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hmixed : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner (ν u) (ν v) =
        ClassFunction.inner u v)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  let hsrc := hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X hXirr
  exact hyp.coherentS_of_Xset_commutator_Yset_glued hX ν hagreeX hagreeY hsrc
    (OddOrder.Peterfalvi.S07.image_orthogonal_of_mixed_inner_eq
      hagreeX hagreeY hmixed hsrc)
    hgen

/-- Generator-level variant of
`coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner`.

The `τ₃` candidate only has to be checked on the characters in `Xset H'` and `Yset`; agreement and
mixed-inner preservation on the integral spans are derived internally. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆, ν x = hX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner hXirr hX ν
    (fun _ hu => OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeX hu)
    (fun _ hv => OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeY hv)
    (OddOrder.Peterfalvi.S07.mixed_inner_eq_on_zSpan_of_eq_on hmixed)
    hgen

/-- **(6.8.1), case (c1):** in the Frobenius case every member of `S` is irreducible (hence
`X ⊆ Irr L`).  By [Is] Thm 6.34 (`isIrreducibleCharacter_induce_of_frobeniusGroup`), inducing any
nontrivial irreducible of the kernel `H` to the Frobenius group `L` gives an irreducible. -/
theorem isIrreducibleCharacter_of_mem_S_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.S) : IsIrreducibleCharacter φ := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, rfl⟩ := hφ
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne

/-- **(6.8.1), case (c1):** `X ⊆ Irr L` in the Frobenius case, since `X ⊆ S` and `S ⊆ Irr L`.
This is the irreducibility input the §6 coherence engine (T8) consumes for the `X`-family (and the
`hX` hypothesis of the (6.6) characterization). -/
theorem isIrreducibleCharacter_of_mem_Xset_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Xset Z) :
    IsIrreducibleCharacter φ :=
  hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hyp.mem_Xset.mp hφ).1

/-- **(6.8.1), Frobenius case:** source-side orthogonality for the final
`X = S - S(H')`, `Y = S(H')` partition. -/
theorem inner_span_Xset_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) :
    ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0 :=
  hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)

/-- **(6.8.1), Frobenius case:** glue the Frobenius `X` coherence with the internally
constructed `Y` coherence, with source-side orthogonality discharged from Frobenius
irreducibility. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY himg_ortho hgen

/-- **(6.8.1), Frobenius case:** glue the Frobenius `X` coherence with the internally
constructed `Y` coherence, using mixed inner preservation of `ν` to discharge image-side
orthogonality. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hmixed : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner (ν u) (ν v) =
        ClassFunction.inner u v)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY hmixed hgen

/-- **(6.8.1), Frobenius case:** generator-level mixed-inner glue adapter.

This is the Frobenius specialization of the generator-level `τ₃` interface: the `X`-side
irreducibility is discharged from `hF`, while agreement and mixed-inner preservation are required
only on members of `Xset H'` and `Yset`. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆, ν x = hX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY hmixed hgen

/-- **(T7-c2 case A) `X ⊆ Irr L`.**  In case A every `χ ∈ X = S − S(Z)` is irreducible.  Writing
`χ = Ind_H^L θ` (`θ ≠ 1`, from `χ ∈ S`), membership `χ ∉ S(Z)` forces `Z.subgroupOf H ⊄ Ker θ`, so
`inertia_eq_H_of_c2_caseA` gives `I_L(θ) = H`, and [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`) makes `Ind_H^L θ = χ` irreducible.  This is the
case-A analogue of `isIrreducibleCharacter_of_mem_Xset_of_frobenius` (the Frobenius case). -/
theorem isIrreducibleCharacter_of_mem_Xset_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    letI : H.Normal := hyp.H_normal
    IsIrreducibleCharacter χ := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨hχS, hχnotZ⟩ := hχX
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, hθne, hχeq⟩ := hχS
  have hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ)) :=
    fun hsub => hχnotZ ⟨θ, hθne, hsub, hχeq⟩
  have hinertia := hyp.inertia_eq_H_of_c2_caseA hZH hZcentral hZnorm hZfpf hZker
  rw [hχeq]
  exact isIrreducibleCharacter_induce_of_inertia_eq θ hinertia

/-- **Peterfalvi (6.6) `X`-characterization** (mmd 04.8 L74-76).  For a normal `Z ≤ H` such that
every member of `X = S − S(Z)` is irreducible (the (6.8) Frobenius/case-A input `hX`), `X` is
exactly the set of irreducible characters of `L` whose kernel does not contain `Z`:
`X = {χ ∈ Irr L | Z ⊄ Ker χ}`.

Both inclusions route the kernel comparison through a *genuine* character — `Res_H φ` for `⊆`
(via `characterKernel_subset_of_isCharacter_of_inner_ne_zero`) and `Ind_H^L θ` for `⊇` (via
`characterKernel_subset_of_inner_induce_ne_zero`) — together with the (1.6.a) forward bridge
`subsetCharacterKernel_induce_of_subgroupOf`; no use of [Is] Lemma 2.21 is needed. -/
theorem Xset_eq_irreducible_not_subset_characterKernel (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    hyp.Xset Z = {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  ext φ
  constructor
  · -- (⊆): φ ∈ X is irreducible (hX); if `Z ⊆ Ker φ` then `φ = Ind θ ∈ S(Z)`, contradiction.
    intro hφX
    have hφirr : IsIrreducibleCharacter φ := hX φ hφX
    refine ⟨hφirr, ?_⟩
    obtain ⟨hφS, hφnotSZ⟩ := hyp.mem_Xset.mp hφX
    rw [hyp.S_eq] at hφS
    obtain ⟨θ, hθ_ne, hφeq⟩ := hφS
    intro hZker
    apply hφnotSZ
    rw [hyp.mem_SsubFiltration]
    refine ⟨θ, hθ_ne, ?_, hφeq⟩
    -- `Z.subgroupOf H ⊆ Ker θ`: read off from `Res_H φ` (a genuine constituent of `θ`).
    have hRes : IsCharacter (ClassFunction.restrict H φ) := isCharacter_restrict hφirr.isCharacter H
    have hθirr : IsIrreducibleCharacter (θ : ClassFunction ↥H ℂ) := θ.property
    have hnorm : ClassFunction.inner φ φ = 1 := by
      have h := irreducibleCharacter_inner_eq_ite (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
      simpa using h
    have hinner_ne : ClassFunction.inner (ClassFunction.restrict H φ)
        (θ : ClassFunction ↥H ℂ) ≠ 0 := by
      have hfrob := ClassFunction.inner_induce_eq_inner_restrict H (θ : ClassFunction ↥H ℂ) φ
      rw [← hφeq, hnorm] at hfrob
      rw [inner_conj_symm θ (ClassFunction.restrict H φ), ← hfrob]
      simp
    intro n hn
    refine characterKernel_subset_of_isCharacter_of_inner_ne_zero hRes hθirr hinner_ne ?_
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    simp only [ClassFunction.restrict_apply]
    have hnZ : ((n : ↥L)) ∈ Z := Subgroup.mem_subgroupOf.mp hn
    have hker := hZker hnZ
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hker
    rw [hker, OneMemClass.coe_one]
  · -- (⊇): χ irreducible with `Z ⊄ Ker χ`.  Take a source `θ` of `χ`; show `Ind θ ∈ X`, hence
    -- irreducible (hX), hence `= χ` by orthonormality.
    rintro ⟨hχirr, hχZ⟩
    obtain ⟨θ, hθinner⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := H)
      (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
    -- A source `θ'` of `χ` with `Z.subgroupOf H ⊆ Ker θ'` would force `Z ⊆ Ker χ` (contradiction).
    have hkey : ∀ θ' : IrreducibleCharacter ↥H,
        ClassFunction.inner (ClassFunction.induce H (θ' : ClassFunction ↥H ℂ)) φ ≠ 0 →
        ((Z.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥H ℂ)) → False := by
      intro θ' hθ'inner hθ'ker
      apply hχZ
      have hZind := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (G := ↥L) hZH (θ' : ClassFunction ↥H ℂ) hθ'ker
      intro z hz
      exact characterKernel_subset_of_inner_induce_ne_zero θ'.property.isCharacter hχirr
        hθ'inner (hZind hz)
    have hθ_ne : θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H := by
      intro hθtriv
      refine hkey θ hθinner (fun n _ => ?_)
      rw [hθtriv]
      simp [OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    have hIndnotSZ : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∉ hyp.SsubFiltration Z := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', _, hθ'ker, hθ'eq⟩ := hmem
      exact hkey θ' (by rw [← hθ'eq]; exact hθinner) hθ'ker
    have hIndX : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∈ hyp.Xset Z :=
      hyp.mem_Xset.mpr ⟨by rw [hyp.S_eq]; exact ⟨θ, hθ_ne, rfl⟩, hIndnotSZ⟩
    have hIndirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) :=
      hX _ hIndX
    have heq : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) = φ := by
      have hite := irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hIndirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      by_cases hAB : (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hIndirr⟩ :
          IrreducibleCharacter ↥L) = (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      · exact congrArg Subtype.val hAB
      · rw [if_neg hAB] at hite
        exact absurd hite hθinner
    rw [← heq]; exact hIndX

/-- **(T8 leaf 1) `X`-member character facts**, from the abstract input `X ⊆ Irr L`.

Every `χ ∈ X = S − S(Z)` is non-real (Peterfalvi (1.1), `L` odd) with
`‖χ‖² = ‖χ̄‖² = 1` and `⟨χ̄, χ⟩ = ⟨χ, χ̄⟩ = 0`.  These are the
`hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar'` fields of `S07.DadeChainStep`.
Non-triviality is read off the (6.6) characterization
(`Z ⊄ Ker χ` via `Xset_eq_irreducible_not_subset_characterKernel`, so `χ ≠ 1`),
then (1.1) (`not_isReal_of_ne_trivial_of_odd_card'`) gives non-realness and
`irreducibleCharacter_inner_eq_ite` gives the orthonormality.

This form is shared by the Frobenius case and the case-A `X ⊆ Irr L` bridge. -/
theorem xMember_characterFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  -- `Z ⊄ Ker χ` from the (6.6) characterization, hence `χ ≠ 1`.
  have hZker : ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ) := by
    have hXeq := hyp.Xset_eq_irreducible_not_subset_characterKernel hZH hX
    rw [hXeq] at hχX
    exact hχX.2
  have hne_triv : (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ≠
      OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro htriv
    apply hZker
    have hχtriv : χ = OddOrder.RepresentationTheory.trivialClassFunction ↥L :=
      congrArg Subtype.val htriv
    rw [hχtriv, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  have hreal : ¬ ClassFunction.IsReal χ :=
    OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hyp.card_L_odd hne_triv
  have hbi_ne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, ?_, ?_, ?_, ?_⟩
  · simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
  · simpa using
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ.conj, hconjirr⟩
    rwa [if_neg (fun h => hbi_ne h.symm)] at h

/-- **(T8 leaf 1) `X`-member character facts** (Frobenius case). -/
theorem xMember_characterFacts (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 :=
  hyp.xMember_characterFacts_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχX

/-- **(T8 leaf 2) `X`-member difference support**, from the abstract input `X ⊆ Irr L`.

For `χ ∈ X = S − S(Z)` the conjugate difference `χ̄ − χ` is supported on
`H^# = sharpImage H` (the `hdiffsupp` field of `S07.DadeChainStep`).  Since
`χ = Ind_H^L θ` with `H ⊴ L`, `support χ ⊆ H` (`support_induce_subset_of_normal`);
`χ̄ − χ` vanishes at `1` (the degree `χ(1)` is the real `(n : ℂ)`), so it omits `1`
and lands in `H ∖ {1}`. -/
theorem xMember_diffSupport_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hχS : χ ∈ hyp.S := (hyp.mem_Xset.mp hχX).1
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast, sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8 leaf 2) `X`-member difference support** (Frobenius case). -/
theorem xMember_diffSupport (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.xMember_diffSupport_of_irreducible_X
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχX

/-- **(T8 leaf 3a) `X` is closed under conjugation**, from the abstract input `X ⊆ Irr L`.

`Z ⊴ L` gives `Ker χ̄ = Ker χ` (`characterKernel_conj`), so the (6.6) characterization
`X = {χ ∈ Irr L | Z ⊄ Ker χ}` is conjugation-invariant.  This is the
`ClosedUnderConjugate` input to the degree-monotone enumeration of `X` into conjugate pairs
(`S07.two_le_ncard_of_conjugate_closed_of_noReal`, `S07.exists_monotoneDegreeEnum`). -/
theorem Xset_closedUnderConjugate_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) := by
  have hXeq := hyp.Xset_eq_irreducible_not_subset_characterKernel hZH hX
  intro χ hχX
  rw [hXeq] at hχX ⊢
  refine ⟨hχX.1.conj, ?_⟩
  rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
  exact hχX.2

/-- **(T8 leaf 3a) `X` is closed under conjugation** (Frobenius case). -/
theorem Xset_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
  hyp.Xset_closedUnderConjugate_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 3b) `X` has no real characters**, from the abstract input `X ⊆ Irr L`. -/
theorem Xset_hasNoRealCharacters_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
  fun _ hχX => (hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX).1

/-- **(T8 leaf 3b) `X` has no real characters** (Frobenius case). -/
theorem Xset_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
  hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 4) `X` is finite**, from the abstract input `X ⊆ Irr L`.

This is the `hXfin` input to the degree-monotone enumeration
`S07.exists_monotoneDegreeEnum` and the chain assembly. -/
theorem xSet_finite_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    (hyp.Xset Z).Finite := by
  haveI := OddOrder.RepresentationTheory.finite_irreducibleCharacter (G := ↥L)
  have hIrrFin : (irreducibleCharacters ↥L).Finite :=
    (Set.finite_range (fun χ : IrreducibleCharacter ↥L => (χ : ClassFunction ↥L ℂ))).subset
      (fun φ hφ => ⟨⟨φ, mem_irreducibleCharacters.mp hφ⟩, rfl⟩)
  exact hIrrFin.subset
    (fun χ hχ => mem_irreducibleCharacters.mpr (hX χ hχ))

/-- **(T8 leaf 4) `X` is finite** (Frobenius case). -/
theorem xSet_finite (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} :
    (hyp.Xset Z).Finite :=
  hyp.xSet_finite_of_irreducible_X
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 5) the base block `S₀`**: the minimal-(real-)degree members of `X`.  This is the
equal-minimal-degree prefix `{χ₁,…,χₖ}` of (6.6), on which (1.1)+(1.4) supplies the base coherence
`coherentEqualDegree_fromDade` before the (5.6) adjoining of the strictly-higher-degree conjugate
pairs.  `S₀` must contain **all** minimal-degree members (not just one pair): the first (5.6)
adjoining of a pair of degree ratio `a` needs `2a < ∑_{S₀} aⱼ²`, which fails at equal degree. -/
def xBaseBlock (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {χ ∈ hyp.Xset Z | ∀ ψ ∈ hyp.Xset Z,
    (OddOrder.Peterfalvi.S03.characterDegree χ).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree ψ).re}

theorem xBaseBlock_subset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.xBaseBlock Z ⊆ hyp.Xset Z :=
  fun _ hχ => hχ.1

/-- Any two members of the base block have the same degree (the base is an *equal*-degree family,
the input shape of `coherentEqualDegree_fromDade`). -/
theorem xBaseBlock_degree_re_eq (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.xBaseBlock Z) (hχ' : χ' ∈ hyp.xBaseBlock Z) :
    (OddOrder.Peterfalvi.S03.characterDegree χ).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ').re :=
  le_antisymm (hχ.2 χ' hχ'.1) (hχ'.2 χ hχ.1)

/-- If `χ₁` is a base-block anchor and `χ ∈ X`, then the natural degree of `χ₁` is no larger
than the natural degree of `χ`. -/
theorem natDegree_le_of_xBaseBlock_anchor (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ₁ χ : IrreducibleCharacter ↥L} {d₁ d : ℕ}
    (hχ₁base : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχ₁one : (χ₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hχone : (χ : ClassFunction ↥L ℂ) 1 = (d : ℂ)) :
    d₁ ≤ d := by
  have hre := hχ₁base.2 (χ : ClassFunction ↥L ℂ) hχX
  rw [OddOrder.Peterfalvi.S03.characterDegree_def,
    OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one, hχone] at hre
  exact_mod_cast hre

/-- If `χ₁` is a base-block anchor and `χ ∈ X` is not itself in the base block, then the
natural degree of `χ` is strictly larger. -/
theorem natDegree_lt_of_xBaseBlock_anchor_of_not_mem
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ₁ χ : IrreducibleCharacter ↥L} {d₁ d : ℕ}
    (hχ₁base : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχnotbase : (χ : ClassFunction ↥L ℂ) ∉ hyp.xBaseBlock Z)
    (hχ₁one : (χ₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hχone : (χ : ClassFunction ↥L ℂ) 1 = (d : ℂ)) :
    d₁ < d := by
  have hle : d₁ ≤ d :=
    hyp.natDegree_le_of_xBaseBlock_anchor hχ₁base hχX hχ₁one hχone
  have hne : d₁ ≠ d := by
    intro hEq
    apply hχnotbase
    refine ⟨hχX, ?_⟩
    intro ψ hψX
    have hbase_le := hχ₁base.2 ψ hψX
    have hχre :
        (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction ↥L ℂ)).re =
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction ↥L ℂ)).re := by
      rw [OddOrder.Peterfalvi.S03.characterDegree_def,
        OddOrder.Peterfalvi.S03.characterDegree_def, hχone, hχ₁one]
      exact_mod_cast hEq.symm
    rw [hχre]
    exact hbase_le
  omega

/-- The base block is closed under conjugation, from the abstract input `X ⊆ Irr L`:
conjugation preserves the degree (`characterDegree_conj`) and `X`
(`Xset_closedUnderConjugate_of_irreducible_X`).  With the no-real property this makes `S₀`
contain a conjugate pair, so `2 ≤ |S₀|`. -/
theorem xBaseBlock_closedUnderConjugate_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) := by
  intro χ hχ
  refine ⟨hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX hχ.1, fun ψ hψ => ?_⟩
  have hre : (OddOrder.Peterfalvi.S03.characterDegree χ.conj).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ).re := by
    simp [OddOrder.Peterfalvi.S03.characterDegree_conj]
  rw [hre]
  exact hχ.2 ψ hψ

/-- The base block is closed under conjugation (Frobenius case). -/
theorem xBaseBlock_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
  hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- A member `χ = Ind_H^L θ` of `S` is supported on `H` (its induced character vanishes off the
normal subgroup `H`). -/
theorem sMember_support_subset_H (hyp : SibleyDadeHypothesis G L H)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) :
    χ.support ⊆ (H : Set ↥L) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  rw [hχeq]
  exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)

/-- **(T8 leaf 6) equal-degree difference support.**  For two members `χ, χ'` of `S` of equal
degree (`χ(1) = χ'(1)`) the difference `χ − χ'` is supported on `H^# = sharpImage H`: both are
supported on `H` (`sMember_support_subset_H`) and the difference vanishes at `1` (equal degree).
This is the `hsuppdiff` input of `coherentEqualDegree_fromDade` for the equal-minimal-degree base
block `S₀` (`irreducibleCharacterDifference χ j = χⱼ − χ₀`), and the (5.6) `χ − a·χ₁` support shape. -/
theorem sMember_diffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) (hdeg : χ 1 = χ' 1) :
    (χ - χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by rw [ClassFunction.sub_apply, hχg, h0, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8.11d) scaled degree-matched support.**

For two `S`-members whose degrees satisfy `χ(1) = a χ₁(1)`, the scaled difference
`χ - aχ₁` is supported on `H^# = sharpImage H`.  This is the support bridge used for the
`hmemdegdiffsupp` and `hdiffasuppχ` fields once the integer degree ratios are available. -/
theorem sMember_scaledDiffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) {a : ℕ}
    (hdeg : χ 1 = (a : ℂ) * χ' 1) :
    (χ - a • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by
      rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ', ClassFunction.smul_apply,
        hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by
          rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ',
            ClassFunction.smul_apply, hχg, h0, mul_zero, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8.11e) scaled supported differences map to virtual characters.**

Once the degree-ratio support field for `χ - aχ₁` is known, the real Dade map sends that
scaled difference to `ℤ[Irr G]`.  This is exactly the `htau1_memaχ` field of
`XAdjoinStepInput`, separated from the arithmetic that produces the ratio and support. -/
theorem scaledDiff_dadeImage_mem_ZIrr (hyp : SibleyDadeHypothesis G L H)
    {χ χ₁ : IrreducibleCharacter ↥L} {a : ℕ}
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    hyp.tau ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dade hyp.hconj hdiffasupp
    (Submodule.sub_mem _ χ.mem_ZIrr (nsmul_mem χ₁.mem_ZIrr a))

/-- **(T8.11f) X-members with a degree ratio have supported scaled difference.**

This is the `X = S - S(Z)` adapter for `sMember_scaledDiffSupport_of_charValue_eq`: once
the degree-ratio equation `χ(1)=aχ₁(1)` is available, the scaled difference
`χ-aχ₁` is supported on `H^#`. -/
theorem xMember_scaledDiffSupport_of_degreeData (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} {χ χ₁ : IrreducibleCharacter ↥L} {a : ℕ}
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχ₁X : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hdeg : (χ : ClassFunction ↥L ℂ) 1 = (a : ℂ) * (χ₁ : ClassFunction ↥L ℂ) 1) :
    ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  exact hyp.sMember_scaledDiffSupport_of_charValue_eq
    (hyp.mem_Xset.mp hχX).1 (hyp.mem_Xset.mp hχ₁X).1 hdeg

/-- **(T8.11g) member-family scaled supports from degree data.**

Given a finite accumulator family inside `X` and degree ratios against the distinguished member
`χ₁`, all scaled member differences `χᵢ-degᵢχ₁` are supported on `H^#`.  This is the
`hmemdegdiffsupp` half of `XAdjoinStepInput`, separated from the arithmetic that constructs the
ratios. -/
theorem xMember_scaledDiffSupports_of_degreeData (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} {ι : Type*} {s : Finset ι}
    {χmem : ι → IrreducibleCharacter ↥L} {deg : ι → ℕ} {i₁ : ι}
    (hmemX : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hi₁ : i₁ ∈ s)
    (hdeg : ∀ i ∈ s,
      (χmem i : ClassFunction ↥L ℂ) 1 =
        (deg i : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) :
    ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro i hi
  exact hyp.xMember_scaledDiffSupport_of_degreeData (hmemX i hi) (hmemX i₁ hi₁) (hdeg i hi)

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, from the abstract input `X ⊆ Irr L`.

If `X` is nonempty, its base block `S₀` (minimal-degree members) contains a minimal-degree `χ`
together with its conjugate `χ̄ ≠ χ` (`Xset_hasNoRealCharacters_of_irreducible_X`,
`xBaseBlock_closedUnderConjugate_of_irreducible_X`), so `2 ≤ |S₀|`. -/
theorem two_le_xBaseBlock_ncard_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard := by
  have hXfin := hyp.xSet_finite_of_irreducible_X hX
  obtain ⟨χ, hχX, hχmin⟩ := Set.exists_min_image (hyp.Xset Z)
    (fun ψ => (OddOrder.Peterfalvi.S03.characterDegree ψ).re) hXfin hXne
  have hχS₀ : χ ∈ hyp.xBaseBlock Z := ⟨hχX, hχmin⟩
  have hconjS₀ : χ.conj ∈ hyp.xBaseBlock Z :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX hχS₀
  have hne : χ.conj ≠ χ := hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX hχX
  have hS₀fin : (hyp.xBaseBlock Z).Finite := hXfin.subset (hyp.xBaseBlock_subset Z)
  have h1 : 1 < (hyp.xBaseBlock Z).ncard :=
    (Set.one_lt_ncard hS₀fin).mpr ⟨χ.conj, hconjS₀, χ, hχS₀, hne⟩
  omega

/-- **(T8 leaf 8) `2 ≤ |S₀|`** (Frobenius case). -/
theorem two_le_xBaseBlock_ncard (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard :=
  hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`**, from the abstract input
`X ⊆ Irr L`.

The minimal-degree base block `S₀ = xBaseBlock Z` is coherent for the real Dade map `tau`.  It is a
finite, equal-degree family of `≥ 2` irreducible characters of `L`
(`exists_finEnum_irreducible`, `xBaseBlock_degree_re_eq` with the integer degrees
`irreducibleCharacter_apply_one_eq_pos_natCast`, `two_le_xBaseBlock_ncard_of_irreducible_X`) whose
pairwise differences `χⱼ − χ₀` vanish off `H^# = sharpImage H`
(`sMember_diffSupport_of_charValue_eq`), so the §7 base engine `coherentEqualDegree_fromDade`
((6.6) base case, via (1.1)+(1.4)) applies with `A = H^#` — matching
`tau = dadeIntegralCharacterMap hyp.dade …`.

`noncomputable def` (not `theorem`): `IsCoherent` carries the isometric extension map as data
(it lives in `Type`, not `Prop`), exactly like `sibleySetup_is_coherent`/`CoherenceTarget`. -/
noncomputable def xBaseBlock_isCoherent_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- Enumerate the finite irreducible base block `S₀` as `χ : Fin k → Irr L`.  The conclusion
  -- `IsCoherent` is `Type`-valued (carries the extension map), so the enumeration data must be
  -- extracted with `choose` (via choice), not `obtain` (which would large-eliminate a `Prop ∃`).
  have hS₀fin : (hyp.xBaseBlock Z).Finite :=
    (hyp.xSet_finite_of_irreducible_X hX).subset (hyp.xBaseBlock_subset Z)
  have hS₀irr : ∀ φ ∈ hyp.xBaseBlock Z, IsIrreducibleCharacter φ :=
    fun φ hφ => hX φ (hyp.xBaseBlock_subset Z hφ)
  choose k χ hχinj hrange using exists_finEnum_irreducible hS₀fin hS₀irr
  have hmemS₀ : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z :=
    fun j => hrange ▸ Set.mem_range_self j
  -- `2 ≤ k`: the coerced enumeration is injective, so `|S₀| = k`.
  have hcoeinj : Function.Injective (fun j => (χ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hχinj (IrreducibleCharacter.ext hij)
  have hk2 : 2 ≤ k := by
    have hcard : (hyp.xBaseBlock Z).ncard = k := by
      rw [← hrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h2 := hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH hX hXne
    omega
  haveI : NeZero k := ⟨by omega⟩
  -- `S₀ ⊆ S`.
  have hmemS : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.S :=
    fun j => (hyp.mem_Xset.mp (hyp.xBaseBlock_subset Z (hmemS₀ j))).1
  -- Equal degree: real parts equal (base block) and the degrees are positive integers.
  have hdeg : ∀ j, ((χ j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((χ 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    obtain ⟨dj, _, hdj⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ j)
    obtain ⟨d0, _, hd0⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ 0)
    have hre := hyp.xBaseBlock_degree_re_eq (hmemS₀ j) (hmemS₀ 0)
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def, hdj, hd0] at hre
    rw [hdj, hd0]
    have hdd : dj = d0 := by exact_mod_cast hre
    rw [hdd]
  -- Difference support: `χⱼ − χ₀` vanishes off `H^#` (equal degree, both supported on `H`).
  have hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun j => hyp.sMember_diffSupport_of_charValue_eq (hmemS j) (hmemS 0) (hdeg j)
  -- `1 ∉ A = H^#`.
  have h1notA : (1 : G) ∉ sharpImage H := by simp [sharpImage]
  -- Apply the §7 base engine; its `range χ = S₀` and Dade map `= hyp.tau`.
  have hcoh := OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj
    hk2 χ hχinj hdeg hsuppdiff h1notA
  rw [hrange] at hcoh
  exact hcoh

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`** (Frobenius case). -/
noncomputable def xBaseBlock_isCoherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9, case A) base coherence `IsCoherent τ S₀`.**

This specializes the abstract `X ⊆ Irr L` base-block engine using the case-A irreducibility bridge
`isIrreducibleCharacter_of_mem_Xset_caseA`. -/
noncomputable def xBaseBlock_isCoherent_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_caseA hZH hZcentral hZnorm hZfpf h)
    hXne


/-- **(T8.11b) X-pair step core facts.**

For a pair supplied by `exists_conjugatePairCover`, the first eight fields of
`XAdjoinStepInput` are forced by membership in `X` and the disjoint-prefix property: the new
character is non-real, has the required difference support, is orthonormal to its conjugate, and is
orthogonal to the accumulated prefix. -/
theorem xPair_stepCoreFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N) :
    ¬ ClassFunction.IsReal (χs i : ClassFunction ↥L ℂ) ∧
      (((χs i : ClassFunction ↥L ℂ).conj - (χs i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ) (χs i : ClassFunction ↥L ℂ) = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ).conj = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ)
        (χs i : ClassFunction ↥L ℂ).conj = 0 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ) = 0 ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ) x = 0) ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj x = 0) := by
  classical
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX with
    ⟨hrealχ, hχχ, hχbarχbar, hχbarχ, hχχbar⟩
  have hdiffsuppχ := hyp.xMember_diffSupport_of_irreducible_X hX hχX
  have hortho := pairCover_orthogonal_to_prefix
    (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z) (pair := pair) (N := N)
    (i := i) (χ := χs i) hX (hyp.xBaseBlock_subset Z) hpairs
    (hpair0 i hi) (hpair1 i hi) (hdisj i hi) hi
  exact ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hortho.1, hortho.2⟩

/-- **(T8.11c) Accumulator member-family enumeration.**

Every prefix accumulator `pairUnion (xBaseBlock Z) pair i` in the X-chain is a finite family of
irreducible characters, closed under conjugation.  This packages the `Fin k` enumeration and the
member facts needed by the member-family half of `XAdjoinStepInput`.  The remaining
degree-ratio and lattice-generation fields stay separate. -/
theorem exists_pairUnion_memberFamily_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hi : i < N) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i ∧
      (∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j : Fin k,
        ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ j l : Fin k,
        ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
          (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ := fun φ hφ => hX φ (hS₁X hφ)
  have hS₁fin : S₁.Finite := (hyp.xSet_finite_of_irreducible_X hX).subset hS₁X
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  have hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hS₀conj hbase))
    · have hjN : j < N := hji.trans hi
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ | hφ
        · right
          rw [hφ, hpair0 j hjN, hpair1 j hjN]
        · left
          rw [hφ, hpair1 j hjN, hpair0 j hjN]
          simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  obtain ⟨k, χmem, hχinj, hrange⟩ := exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    rw [← hrange]
    exact Set.mem_range_self j
  have hmembarS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁ :=
    fun j => hS₁conj (hmemS1 j)
  have hmemreal : ∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ) := by
    intro j
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).1
  have hmemdiffsupp : ∀ j : Fin k,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    exact hyp.xMember_diffSupport_of_irreducible_X hX (hS₁X (hmemS1 j))
  have hmemconjortho : ∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0 := by
    intro j
    rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j)) with
      ⟨_, _, _, _, hχχbar⟩
    exact hχχbar
  have hmemortho : ∀ j l : Fin k,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0 := by
    intro j l
    by_cases hjl : j = l
    · subst j
      simpa using irreducibleCharacter_inner_eq_ite (χmem l) (χmem l)
    · have hχne : χmem j ≠ χmem l := fun h => hjl (hχinj h)
      simpa [hjl, hχne] using irreducibleCharacter_inner_eq_ite (χmem j) (χmem l)
  exact ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1,
    hmemconjortho, hmemortho⟩

open scoped Classical in
/-- **(T8.11l) X-adjoin input from member-family degree ratios.**

Given a conjugate-pair cover step, an explicit finite member-family cover of the current prefix
`S₁ = pairUnion (xBaseBlock Z) pair i`, and degree-ratio data against a chosen anchor `χ₁`, this
assembles the full `XAdjoinStepInput` for adjoining `χᵢ`.  The theorem deliberately leaves the
arithmetical (6.6) payload as inputs: the member and new-character degree ratios, `deg i₁ = 1`, and
the strict inequality `2a < ∑ deg²`.  All non-arithmetical fields are discharged from the X-pair
cover, support bridges, virtual-character bridge, and the §7 anchor-generation lemma. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeRatios
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {deg : ι → ℕ} {i₁ : ι} {a : ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (ha1 : deg i₁ = 1)
    (hdeg_mem : ∀ j ∈ s,
      (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hDeg : 2 * (a : ℝ) < ∑ j ∈ s, ((deg j : ℝ)) ^ 2) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  have hmemX : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := by
    intro j hj
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp (hmemS1 j hj) with hbase | ⟨k, hki, hkpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs k (hki.trans hi) hkpair
  rcases hyp.xPair_stepCoreFacts_of_irreducible_X hZH hX hpair0 hpair1 hpairs hdisj hi with
    ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hχ_S1, hχbar_S1⟩
  have hmemdegdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ) - deg j •
          (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupports_of_degreeData hmemX hi₁ hdeg_mem
  have hdiffasuppχ : ((χs i : ClassFunction ↥L ℂ) - a •
        (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupport_of_degreeData hχX (hmemX i₁ hi₁) hdegχ
  have htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
      (hyp.dade.fullDadeIsometryData hyp.hconj)
      ((χs i : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
    simpa [SibleyDadeHypothesis.tau] using hyp.scaledDiff_dadeImage_mem_ZIrr hdiffasuppχ
  have hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          {(χmem i₁ : ClassFunction ↥L ℂ)}) :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (L := ↥L) (S₁ := S₁)
      (A := OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      (χmem := fun j => (χmem j : ClassFunction ↥L ℂ)) (deg := deg) (i₁ := i₁)
      (by simpa [S₁] using hcover) hi₁ (by simpa [S₁] using hmemS1)
      (by simpa using hmemdegdiffsupp)
  exact
    { hrealχ := hrealχ
      hdiffsuppχ := hdiffsuppχ
      hχχ := hχχ
      hχbarχbar := hχbarχbar
      hχχbar := hχχbar
      hχbarχ := hχbarχ
      hχ_S1 := hχ_S1
      hχbar_S1 := hχbar_S1
      ι := ι
      s := s
      χmem := χmem
      deg := deg
      i₁ := i₁
      hi₁ := hi₁
      hmemreal := hmemreal
      hmemdiffsupp := hmemdiffsupp
      hmemdegdiffsupp := hmemdegdiffsupp
      hmemS1 := hmemS1
      hmembarS1 := hmembarS1
      hmemconjortho := hmemconjortho
      hmemortho := hmemortho
      a := a
      hdiffasuppχ := hdiffasuppχ
      htau1_memaχ := htau1_memaχ
      ha1 := ha1
      hDeg := hDeg
      hSgen := hSgen }

/-- **(T8 leaf 10 / T-A4) X-chain assembly from per-pair adjoining data.**

This is the Sibley/Xset wrapper around the abstract `xChainCoherent` fold.  It builds the
conjugate-pair cover of `X = hyp.Xset Z` over the minimal-degree base block
`S0 = hyp.xBaseBlock Z` (`exists_conjugatePairCover`), supplies the base coherence
`xBaseBlock_isCoherent_of_irreducible_X`, and leaves exactly the per-step (5.6)/(6.6) adjoining
payload as `hstep`.

The extra disjoint-prefix and degree-monotonicity facts exposed to `hstep` are produced by the pair
cover but are not consumed by `xChainCoherent` itself; they are the data needed to construct each
`XAdjoinStepInput` without re-enumerating `X`. -/
noncomputable def Xset_isCoherent_from_adjoinSteps_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstep : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
        XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hXfin : (hyp.Xset Z).Finite := hyp.xSet_finite_of_irreducible_X hX
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
    hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
    hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX
  have hS0conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z)
      hXfin hXconj hXreal hX hS0conj
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hX _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi
    rw [hpair0Raw i hi]
    simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi
    rw [hpair1Raw i hi]
    simp [χs, hi]
  have hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  exact xChainCoherent hyp.dade hyp.hconj pair N χs hpair0 hpair1
    (hyp.xBaseBlock_subset Z) hpairs hcover
    (hyp.xBaseBlock_isCoherent_of_irreducible_X hZH hX hXne)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh)

end SibleyDadeHypothesis

/-- **(T8.11m) normalized degree gap from an absolute degree bound.**

If the new character and the prefix member family have natural degree ratios against the same
anchor `χ₁`, then the absolute §6.6 inequality
`2 * χ(1) * χ₁(1) < ∑ χmem(j)(1)^2` is equivalent, after dividing by the positive square
`χ₁(1)^2`, to the normalized `XAdjoinStepInput.hDeg` inequality
`2 * a < ∑ deg(j)^2`. -/
theorem normalizedDegreeGap_of_realDegreeBound
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a : ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hAbs : 2 *
        ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 := by
  classical
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  have hd₁real_pos : 0 < (d₁ : ℝ) := by exact_mod_cast hd₁pos
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re =
        (a : ℝ) * (d₁ : ℝ) := by
    have h := congrArg Complex.re hχdeg
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hmemre : ∀ i ∈ s,
      (OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re =
        (deg i : ℝ) * (d₁ : ℝ) := by
    intro i hi
    have h := congrArg Complex.re (hmemdeg i hi)
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hleft :
      2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) =
        (2 * (a : ℝ)) * (d₁ : ℝ) ^ 2 := by
    rw [hχre, hχ₁re]
    ring
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, (((deg i : ℝ) * (d₁ : ℝ)) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmemre i hi]
      _ = ∑ i ∈ s, ((deg i : ℝ) ^ 2 * (d₁ : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
            rw [← Finset.sum_mul]
  rw [hleft, hright] at hAbs
  have hd₁sq_pos : 0 < (d₁ : ℝ) ^ 2 := sq_pos_of_pos hd₁real_pos
  nlinarith

/-- **(T8.11n) real absolute degree bound from natural prime-power data.**

This is the adapter from the pure §6.6 number-theoretic leaf in §7 to the real-valued
bound used by
`normalizedDegreeGap_of_realDegreeBound`: if natural degree values identify `χ(1)=dχ`,
`χ₁(1)=d₁`, and the member-family square sum is `D`, then the prime-power gap plus
square-divisibility `dχ^2 ∣ D` gives
`2 * χ(1).re * χ₁(1).re < ∑ χmem(j)(1).re^2`. -/
theorem realDegreeBound_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_primePow_gap hp hpos₁ hq hdiv hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11o) normalized degree gap from natural prime-power data.**

Combines `realDegreeBound_of_natDegreeSumPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`, so a §6.6 caller with natural degree data and ratio data
can produce the `XAdjoinStepInput.hDeg` field directly. -/
theorem normalizedDegreeGap_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hpos₁ hq hdiv hlt hdvd hDpos)

/-- **(T8.11r0) intrinsic degree-divisibility from common-index p-power data.**

`exists_pos_natDegreeRatio_of_dvd` consumes an intrinsic predicate over any natural witnesses for
`χ(1)` and `χ₁(1)`.  This lemma produces that predicate from the (6.6) degree-sort data: both
degrees have the same positive induced index `idx`, their residual factors are powers of the same
base `p`, and the sorted degrees satisfy `d₁ ≤ d`. -/
theorem natDegreeDvd_of_commonIndex_primePowerData
    {G : Type*} [Group G] {χ χ₁ : IrreducibleCharacter G}
    {p idx d d₁ θ θ₁ m n : ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hd : d = idx * θ) (hd₁ : d₁ = idx * θ₁)
    (hθ : θ = p ^ m) (hθ₁ : θ₁ = p ^ n) (hle : d₁ ≤ d) :
    ∀ e e₁ : ℕ, (χ : ClassFunction G ℂ) 1 = (e : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (e₁ : ℂ) → e₁ ∣ e := by
  intro e e₁ he he₁
  have hed : e = d := Nat.cast_injective (he.symm.trans hχone)
  have he₁d₁ : e₁ = d₁ := Nat.cast_injective (he₁.symm.trans hχ₁one)
  subst e
  subst e₁
  exact OddOrder.Peterfalvi.S07.mul_primePow_dvd_mul_primePow_of_le
    hp hidx hd₁ hd hθ₁ hθ hle

/-- **(T8.11r) degree-divisibility inputs from common-index p-power sorted degrees.**

This packages both divisibility predicates required by
`xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`: the anchor degree divides every
prefix member degree and the new character degree.  The hypotheses are the honest (6.6) data
behind those predicates — common induced index, p-power residual degrees, and sorted natural
degrees — rather than abstract divisibility assumptions. -/
theorem degreeDivisibilityInputs_of_commonIndex_primePowerData
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ : ℕ}
    {dmem θmem mmem : ι → ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction G ℂ) 1 = (dmem j : ℂ))
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j ∈ s, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j ∈ s, θmem j = p ^ mmem j)
    (hleχ : d₁ ≤ dχ) (hlemem : ∀ j ∈ s, d₁ ≤ dmem j) :
    (∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) ∧
    (∀ d dAnchor : ℕ,
      (χ : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      (hmemone j hj) hχ₁one (hdmem j hj) hd₁ (hθmem j hj) hθ₁ (hlemem j hj)
  · exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      hχone hχ₁one hdχ hd₁ hθχ hθ₁ hleχ


namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(T8.11p) X-adjoin input from natural degree-gap data.**

This combines `xAdjoinStepInput_of_memberFamily_degreeRatios` with
`normalizedDegreeGap_of_natDegreeSumPrimePowerGap`.  A §6.6 caller that already has the finite
member-family data, degree-ratio equations, natural degree witnesses, and the prime-power /
square-divisibility gap can now produce the full `XAdjoinStepInput` without separately supplying
the normalized `hDeg` field. -/
noncomputable def xAdjoinStepInput_of_memberFamily_natDegreeGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {deg : ι → ℕ} {i₁ : ι} {a p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (ha1 : deg i₁ = 1)
    (hdeg_mem : ∀ j ∈ s,
      (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) :=
  hyp.xAdjoinStepInput_of_memberFamily_degreeRatios hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    (normalizedDegreeGap_of_natDegreeSumPrimePowerGap hdegχ hdeg_mem
      hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos)

open scoped Classical in
/-- **(T8.11q) X-adjoin input from divisibility and natural degree-gap data.**

This is the same per-step constructor as `xAdjoinStepInput_of_memberFamily_natDegreeGap`,
but it derives the member-family ratios and the new-character ratio from natural degree
divisibility data.  A §6.6 caller can now provide the character-theoretic divisibility
hypotheses together with the prime-power/square-divisibility gap data, without naming the
ratio function `deg` or scalar `a` separately. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let hratioFamily :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatioFamily_of_dvd
      (G := ↥L) (χ := χmem) (s := s) (i₁ := i₁) hdvd_mem
  let deg : ι → ℕ := Classical.choose hratioFamily
  have ha1 : deg i₁ = 1 := (Classical.choose_spec hratioFamily).1
  have hdeg_mem : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 :=
    (Classical.choose_spec hratioFamily).2.2
  let hratioχ :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatio_of_dvd
      (G := ↥L) (χs i) (χmem i₁) hdvdχ
  let a : ℕ := Classical.choose hratioχ
  have hdegχ_char : OddOrder.Peterfalvi.S03.characterDegree (χs i : ClassFunction ↥L ℂ) =
      (a : ℂ) *
        OddOrder.Peterfalvi.S03.characterDegree (χmem i₁ : ClassFunction ↥L ℂ) :=
    (Classical.choose_spec hratioχ).2
  have hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hdegχ_char
  exact hyp.xAdjoinStepInput_of_memberFamily_natDegreeGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos

open scoped Classical in
/-- **(T8.11r) X-adjoin input from degree divisibility and prime-power sum data.**

This is the same constructor as `xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`, but it
no longer asks the caller to provide the square-divisibility `dχ² ∣ D` as an opaque hypothesis.  The
hypothesis is derived internally from the (6.6) mmd L78-80 arithmetic chain: sorted common-index
p-power tail degrees, total-side p-power square divisibility, the additive head/tail identity, and
coprimality of the fixed induction index with the p-power factor. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_primePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι κ : Type} {s : Finset ι} {tailSet : Finset κ}
    {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ q qtot c total θχ mχ mq : ℕ}
    {dmem : ι → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hθχ : θχ = p ^ mχ)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : D + (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_D : idx * idx ∣ D)
    (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hcop : Nat.Coprime idx θχ := coprime_commonIndex_primePower hidx_p hθχ
  have hdvd : dχ * dχ ∣ D :=
    OddOrder.Peterfalvi.S07.sq_dvd_head_of_commonIndex_primePower_sums
      tailSet (by omega) hidxpos hθχ hθtail htail_le hsum hqtot hθsq_le_qtot htotal
      hidx_D hdχ hcop
  have hpos₁ : 0 < d₁ := natDegree_pos_of_irreducibleCharacter_apply_one_eq hχ₁one
  have hDpos : 0 < D := natDegreeSquareSum_pos_of_memberFamily hi₁ hmemone hDsum
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho hdvd_mem hdvdχ
    hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos

open scoped Classical in
/-- **(T8.11t) X-adjoin input from common-index p-power degree data.**

This is the `primePowerSums` constructor with the two degree-divisibility predicate inputs
also derived internally from the (6.6) common-index p-power degree data.  The caller supplies the
anchor, new-character, and prefix-member factorizations through the same fixed index `idx`, sorted
natural-degree inequalities, and the tail square-sum divisibility data; no abstract `hdvd_mem`,
`hdvdχ`, or `dχ ^ 2 ∣ D` arithmetic black boxes remain at this interface. -/
noncomputable def xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι κ : Type} {s : Finset ι} {tailSet : Finset κ}
    {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ q qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : ι → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j ∈ s, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j ∈ s, θmem j = p ^ mmem j)
    (hlemem : ∀ j ∈ s, d₁ ≤ dmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : D + (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hdvds :=
    OddOrder.Peterfalvi.S08.degreeDivisibilityInputs_of_commonIndex_primePowerData
      (G := ↥L) (χ := χs i) (χ₁ := χmem i₁) (χmem := χmem) (s := s)
      (p := p) (idx := idx) (d₁ := d₁) (dχ := dχ)
      (θ₁ := θ₁) (θχ := θχ) (m₁ := m₁) (mχ := mχ)
      (dmem := dmem) (θmem := θmem) (mmem := mmem)
      (show 2 ≤ p by omega) hidxpos hχone hχ₁one hmemone hdχ hd₁ hdmem hθχ hθ₁
      hθmem (Nat.le_of_lt hlt) hlemem
  have hidx_D : idx * idx ∣ D :=
    OddOrder.Peterfalvi.S08.sq_dvd_natDegreeSquareSum_of_commonIndex hDsum hdmem
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeDivisibility_primePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho hdvds.1 hdvds.2
    hχone hχ₁one hmemone hDsum hp hq hdiv hlt
    hdχ hθχ hθtail htail_le hsum hqtot hθsq_le_qtot htotal hidx_D hidx_p

open scoped Classical in
/-- **(T8.11u) X-adjoin input from a pairUnion enumeration and p-power degree data.**

This specializes `xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums` to the actual
running accumulator `pairUnion (xBaseBlock Z) pair i`.  A caller supplies an injective finite
enumeration of that accumulator; this adapter turns it into the member-family cover and all routine
X-member facts (non-real, conjugate support, conjugate membership, and orthonormality).  The
remaining inputs are the genuine (6.6) degree, p-power, sum, and coprimality data indexed by the
same enumeration. -/
noncomputable def xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {κ : Type} {tailSet : Finset κ}
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hχinj : Function.Injective χmem)
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    {i₁ : Fin k} {p idx d₁ dχ q qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : Fin k → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hp : 3 ≤ p)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j, θmem j = p ^ mmem j)
    (hlemem : ∀ j, d₁ ≤ dmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : (∑ j : Fin k, dmem j * dmem j) +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    change (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
    rw [← hrange]
    exact Set.mem_range_self j
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  have hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hS₀conj hbase))
    · have hjN : j < N := hji.trans hi
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ | hφ
        · right
          rw [hφ, hpair0 j hjN, hpair1 j hjN]
        · left
          rw [hφ, hpair1 j hjN, hpair0 j hjN]
          simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx
    have hxrange : x ∈ Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) := by
      rw [hrange]
      exact hx
    rcases hxrange with ⟨j, rfl⟩
    exact ⟨j, by simp, rfl⟩
  have hmemreal : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ) := by
    intro j _
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).1
  have hmemdiffsupp : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j _
    exact hyp.xMember_diffSupport_of_irreducible_X hX (hS₁X (hmemS1 j))
  have hmemS1' : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := fun j _ => hmemS1 j
  have hmembarS1 : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁ := fun j _ => hS₁conj (hmemS1 j)
  have hmemconjortho : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0 := by
    intro j _
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).2.2.2.2
  have hmemortho : ∀ j ∈ (Finset.univ : Finset (Fin k)), ∀ l ∈ (Finset.univ : Finset (Fin k)),
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        @ite ℂ (j = l) (Classical.propDecidable (j = l)) 1 0 := by
    intro j _ l _
    by_cases hjl : j = l
    · subst j
      simpa using irreducibleCharacter_inner_eq_ite (χmem l) (χmem l)
    · have hχne : χmem j ≠ χmem l := fun h => hjl (hχinj h)
      simpa [hjl, hχne] using irreducibleCharacter_inner_eq_ite (χmem j) (χmem l)
  let Dprefix : ℕ := ∑ j : Fin k, dmem j * dmem j
  have hDsum : ∑ j ∈ (Finset.univ : Finset (Fin k)), dmem j * dmem j = Dprefix := by
    simp [Dprefix]
  have hsum' : Dprefix +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total := by
    simpa [Dprefix] using hsum
  exact hyp.xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover (by simp) hmemreal hmemdiffsupp
    hmemS1' hmembarS1 hmemconjortho hmemortho
    hχone hχ₁one (fun j _ => hmemone j) hDsum
    hp hq hdiv hlt hdχ hd₁ (fun j _ => hdmem j) hθχ hθ₁
    (fun j _ => hθmem j) (fun j _ => hlemem j)
    hθtail htail_le hsum' hqtot hθsq_le_qtot htotal hidx_p

/-- **(T8.11v0) X-adjoin input from a pairUnion enumeration with a base-block anchor.**

This variant of `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums` removes two sorted-degree
inputs.  If the chosen anchor `χ₁` lies in the minimal-degree base block, then every member of the
running prefix has degree at least `χ₁(1)`.  The current pair is disjoint from the prefix, hence its
first character is not itself in the base block, so its degree is strictly larger. -/
noncomputable def xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {κ : Type} {tailSet : Finset κ}
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hχinj : Function.Injective χmem)
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    {i₁ : Fin k} {p idx d₁ dχ q qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : Fin k → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hanchor : (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hp : 3 ≤ p)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j, θmem j = p ^ mmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : (∑ j : Fin k, dmem j * dmem j) +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    change (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
    rw [← hrange]
    exact Set.mem_range_self j
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  have hχnotbase : (χs i : ClassFunction ↥L ℂ) ∉ hyp.xBaseBlock Z := by
    intro hχbase
    have hχprefix : (χs i : ClassFunction ↥L ℂ) ∈ S₁ :=
      OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hχbase)
    exact (Set.disjoint_left.mp (hdisj i hi)) hχpair hχprefix
  have hlt : d₁ < dχ :=
    hyp.natDegree_lt_of_xBaseBlock_anchor_of_not_mem hanchor hχX hχnotbase hχ₁one hχone
  have hlemem : ∀ j : Fin k, d₁ ≤ dmem j := by
    intro j
    exact hyp.natDegree_le_of_xBaseBlock_anchor hanchor (hS₁X (hmemS1 j))
      hχ₁one (hmemone j)
  exact hyp.xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) hχinj hrange
    hχone hχ₁one hmemone hp hq hdiv hlt
    hdχ hd₁ hdmem hθχ hθ₁ hθmem hlemem
    hθtail htail_le hsum hqtot hθsq_le_qtot htotal hidx_p

/-- **(T8.11v) Common-index p-power data for one X-chain step.**

This is the remaining genuine (6.6) payload for one step after the routine `pairUnion` bookkeeping
has been discharged.  The fields are indexed by the same finite enumeration of the running
accumulator `pairUnion (xBaseBlock Z) pair i`, so downstream callers can supply the character-degree
and p-power data directly without rebuilding the member-family facts or the `XAdjoinStepInput`
record by hand. -/
structure PairUnionCommonIndexPrimePowerStepData
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L} where
  κ : Type
  tailSet : Finset κ
  k : ℕ
  χmem : Fin k → IrreducibleCharacter ↥L
  hχinj : Function.Injective χmem
  hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  i₁ : Fin k
  p : ℕ
  idx : ℕ
  d₁ : ℕ
  dχ : ℕ
  q : ℕ
  qtot : ℕ
  c : ℕ
  total : ℕ
  θ₁ : ℕ
  θχ : ℕ
  m : ℕ
  m₁ : ℕ
  mχ : ℕ
  mq : ℕ
  dmem : Fin k → ℕ
  θmem : Fin k → ℕ
  mmem : Fin k → ℕ
  θtail : κ → ℕ
  mtail : κ → ℕ
  hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ)
  hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ)
  hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ)
  hp : 3 ≤ p
  hq : q = p ^ m
  hdiv : dχ = q * d₁
  hlt : d₁ < dχ
  hdχ : dχ = idx * θχ
  hd₁ : d₁ = idx * θ₁
  hdmem : ∀ j, dmem j = idx * θmem j
  hθχ : θχ = p ^ mχ
  hθ₁ : θ₁ = p ^ m₁
  hθmem : ∀ j, θmem j = p ^ mmem j
  hlemem : ∀ j, d₁ ≤ dmem j
  hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j
  htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j
  hsum : (∑ j : Fin k, dmem j * dmem j) +
    (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total
  hqtot : qtot = p ^ mq
  hθsq_le_qtot : θχ * θχ ≤ qtot
  htotal : total = qtot * c
  hidx_p : Nat.Coprime idx p

/-- **(T8.11v1) Base-anchor common-index p-power data for one X-chain step.**

This is the chain-step payload matching
`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`: the caller supplies the
chosen anchor in `xBaseBlock Z`, and the adapter derives the sorted-degree facts
`d₁ < dχ` and `∀ j, d₁ ≤ dmem j` internally. -/
structure PairUnionBaseAnchorCommonIndexPrimePowerStepData
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L} where
  κ : Type
  tailSet : Finset κ
  k : ℕ
  χmem : Fin k → IrreducibleCharacter ↥L
  hχinj : Function.Injective χmem
  hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  i₁ : Fin k
  p : ℕ
  idx : ℕ
  d₁ : ℕ
  dχ : ℕ
  q : ℕ
  qtot : ℕ
  c : ℕ
  total : ℕ
  θ₁ : ℕ
  θχ : ℕ
  m : ℕ
  m₁ : ℕ
  mχ : ℕ
  mq : ℕ
  dmem : Fin k → ℕ
  θmem : Fin k → ℕ
  mmem : Fin k → ℕ
  θtail : κ → ℕ
  mtail : κ → ℕ
  hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ)
  hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ)
  hanchor : (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z
  hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ)
  hp : 3 ≤ p
  hq : q = p ^ m
  hdiv : dχ = q * d₁
  hdχ : dχ = idx * θχ
  hd₁ : d₁ = idx * θ₁
  hdmem : ∀ j, dmem j = idx * θmem j
  hθχ : θχ = p ^ mχ
  hθ₁ : θ₁ = p ^ m₁
  hθmem : ∀ j, θmem j = p ^ mmem j
  hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j
  htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j
  hsum : (∑ j : Fin k, dmem j * dmem j) +
    (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total
  hqtot : qtot = p ^ mq
  hθsq_le_qtot : θχ * θχ ≤ qtot
  htotal : total = qtot * c
  hidx_p : Nat.Coprime idx p

open scoped Classical in
/-- **(T8.11w) X-chain coherence from per-step common-index p-power data.**

This is the chain-level consumer of `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums`.
The caller no longer has to construct an `XAdjoinStepInput` at each step: it supplies only a
`PairUnionCommonIndexPrimePowerStepData` package for the actual prefix accumulator chosen by the
conjugate-pair cover.  The adapter folds the chain using
`Xset_isCoherent_from_adjoinSteps_of_irreducible_X` and constructs each step input internally. -/
noncomputable def Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionCommonIndexPrimePowerStepData hyp (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hmemone
    data.hp data.hq data.hdiv data.hlt data.hdχ data.hd₁ data.hdmem
    data.hθχ data.hθ₁ data.hθmem data.hlemem data.hθtail data.htail_le data.hsum
    data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

open scoped Classical in
/-- **(T8.11w1) X-chain coherence from base-anchor common-index p-power data.**

This is the chain-level consumer of
`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`.  Compared with
`Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X`, each step package no
longer includes the sorted-degree fields `d₁ < dχ` and `∀ j, d₁ ≤ dmem j`; the base-block anchor
and pair-cover disjointness provide them internally. -/
noncomputable def Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hanchor data.hmemone data.hp data.hq data.hdiv
    data.hdχ data.hd₁ data.hdmem data.hθχ data.hθ₁ data.hθmem data.hθtail
    data.htail_le data.hsum data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

/-- **(6.8.1), Frobenius case:** chain-level coherence for
`X = S - S(H')`, using common-index p-power data.

This is the `Z = H'` specialization of
`Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X` for the Frobenius
alternative.  The subgroup facts `H' ≤ H`, `H' ⊴ L`, and `X ⊆ Irr L` are discharged internally;
the remaining inputs are the honest (6.6) nonemptiness and per-step degree data. -/
noncomputable def Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.8.1), Frobenius case:** chain-level coherence for
`X = S - S(H')`, using the base-anchor common-index p-power step packages.

Compared with
`Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius`, each step data
package only supplies a base-block anchor; the sorted-degree facts are derived by the existing
base-anchor adapter. -/
noncomputable def
    Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.8.1), Frobenius case:** final glue from common-index p-power X-chain data.

This composes the Frobenius `X = S - S(H')` coherence constructor with the generator-level `τ₃`
glue adapter.  The caller supplies only the genuine (6.6) X-chain step data and generator-level
`τ₃` agreement/mixed-inner facts; the `X` coherence witness is built internally. -/
noncomputable def coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x = (hyp.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
        hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner hF
    (hyp.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

/-- **(6.8.1), Frobenius case:** final glue from base-anchor common-index p-power X-chain data.

This is the same capstone as
`coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner`, but using the
base-anchor step package that derives the sorted-degree inequalities internally. -/
noncomputable def
    coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
          hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner hF
    (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

end SibleyDadeHypothesis

/-- **Peterfalvi (6.8) Theorem** (statement; proof deferred).  Under the faithful Sibley
hypotheses `SibleyDadeHypothesis` (a)/(b)/(c), the set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` is
coherent: there is an integral isometric extension of the §4 Dade map `τ` from `Z[S, H^#]` to
`Z[S]` (`hyp.CoherenceTarget = IsCoherent hyp.tau S H^#`).

The full proof is the central technical content of §8 — the reduction to `H` a non-abelian
`p`-group ((6.5)), the case split (A)/(B) on `Z(H) ∩ W₂` (mmd L150-), and gluing the
`Y = S(H')`-coherence (equal degree `|W₁|`, via [Is] Thm 6.34, now available as
`isIrreducibleCharacter_induce_of_inertia_eq`) with the `X = S − S(Z)`-coherence ((6.6)) through
the §7 engine `coherentUnion_of_glued`. This is one of the two sorries blocking §9 (7.10)
`card_G0_lower_bound`; see `issues/0046-peterfalvi-s08-6-8-coherence.md` and
`notes/peterfalvi/s08_6_8_assembly_plan.md` (task DAG T0–T11).

`noncomputable def` (not `theorem`) because `CoherenceTarget` (an `IsCoherent`) carries the
extension map `ν` as data, living in `Type`, not `Prop`. -/
noncomputable def sibleySetup_is_coherent {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : SibleyDadeHypothesis G L H) : hyp.CoherenceTarget := by
  sorry

/-- **Peterfalvi (6.8) → (7.10) consumer interface.**
A degree-scaled `Z`-chain decomposition: given a coherence input `τ` on `(S, A)`
and an orthonormal family `ζ : Fin n → ClassFunction L ℂ` in `S` with explicit
integer degree ratios `d : Fin n → ℤ` (`d 0 = 1`), the family of images
`χ t = ν (ζ t)` under the coherence extension `ν` is orthonormal, and
`τ (ζ t - d t • ζ 0) = χ t - d t • χ 0`.

This packages the orthonormal-subsets-with-Ind-equation language used in the
(7.10) proof (see `references/peterfalvi/04.9_*.mmd` L133-135). -/
structure IndChainDecomposition
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G)
    {n : ℕ} [NeZero n]
    (ζ : Fin n → ClassFunction L ℂ) (d : Fin n → ℤ)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The orthonormal output family `χ_t = ν(ζ_t)` in `ClassFunction G ℂ`. -/
  χ : Fin n → ClassFunction G ℂ
  /-- Each `χ_t` has norm `1`. -/
  norm_one : ∀ t, ClassFunction.inner (χ t) (χ t) = 1
  /-- Distinct indices give orthogonal `χ`. -/
  pairwise_inner_zero :
    ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (χ t) (χ u) = 0
  /-- The reference index has trivial scaling: `d 0 = 1`. -/
  d_zero : d 0 = 1
  /-- The Ind equation: `τ(ζ_t - d_t · ζ_0) = χ_t - d_t · χ_0`. -/
  image_eq :
    ∀ t, τ (ζ t - (d t) • ζ 0) = χ t - (d t) • χ 0

namespace IndChainDecomposition

variable {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
variable {n : ℕ} [NeZero n]

/-- The Ind-chain decomposition vanishes at the reference index: for `t = 0`,
`τ(ζ 0 - d 0 · ζ 0) = 0`. -/
@[simp] theorem image_eq_zero
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ (ζ 0 - (d 0) • ζ 0) = 0 := by
  rw [data.d_zero, one_smul, sub_self, map_zero]

/-- The output family of an `IndChainDecomposition` is orthonormal, packaged as a
single `if` formula. -/
theorem inner_chi_eq_ite
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) (t u : Fin n) :
    ClassFunction.inner (data.χ t) (data.χ u) = if t = u then 1 else 0 := by
  by_cases htu : t = u
  · subst u
    rw [if_pos rfl, data.norm_one]
  · rw [if_neg htu, data.pairwise_inner_zero htu]

/-- The weighted output sum `∑ d_t χ_t` used in Peterfalvi (7.10). -/
noncomputable def weightedOutput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) : ClassFunction G ℂ :=
  ∑ t : Fin n, (d t : ℂ) • data.χ t

/-- The integral weighted source difference `∑ d_t (ζ_t - d_t ζ_0)` used in Peterfalvi (7.10). -/
noncomputable def weightedDifferenceInput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (_data : IndChainDecomposition (L := L) (G := G) τ ζ d) : ClassFunction L ℂ :=
  ∑ t : Fin n, (d t) • (ζ t - (d t) • ζ 0)

/-- Coefficient recovery for the weighted output sum. -/
theorem inner_chi_weightedOutput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) (t : Fin n) :
    ClassFunction.inner (data.χ t) data.weightedOutput = (d t : ℂ) := by
  classical
  rw [weightedOutput, inner_sum_right]
  have hsum :
      (∑ u : Fin n, ClassFunction.inner (data.χ t) ((d u : ℂ) • data.χ u)) =
        ∑ u : Fin n, (if u = t then (d u : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, data.inner_chi_eq_ite t u, star_intCast]
    by_cases hut : u = t
    · subst u
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg (Ne.symm hut), if_neg hut, mul_zero]
  rw [hsum, Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) t]
  simp

/-- Parseval for the weighted output: `‖∑ d_tχ_t‖² = ∑ d_t²`. -/
theorem weightedOutput_inner_self_eq_sum_sq
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    ClassFunction.inner data.weightedOutput data.weightedOutput =
      ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  classical
  rw [weightedOutput, inner_sum_left]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ClassFunction.inner_smul_left]
  have hinner := data.inner_chi_weightedOutput t
  rw [weightedOutput] at hinner
  rw [hinner]
  ring

/-- The Ind equations combine linearly on Peterfalvi's weighted source difference. -/
theorem image_weightedDifferenceInput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ data.weightedDifferenceInput =
      ∑ t : Fin n, (d t) • (data.χ t - (d t) • data.χ 0) := by
  classical
  rw [weightedDifferenceInput, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_zsmul, data.image_eq t]

/-- Construct an `IndChainDecomposition` from a coherence input `hτ : IsCoherent τ S A`
together with the membership `ζ_t ∈ S`, the orthonormality of the input family `ζ`,
and the support of each scaled difference `ζ_t - d_t · ζ_0` in `Z[S, A]`.

The orthonormality of the images `χ_t = ν(ζ_t)` uses the **lattice-relative**
isometry `hτ.extension_inner_eq` on the generators `ζ_t ∈ S ⊆ Z[S] = zSpan S`
(`Submodule.subset_span`); this is all the weakened `IsCoherent` interface
supplies, and all it needs to. -/
noncomputable def ofIsCoherent
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hτ : OddOrder.Peterfalvi.S07.IsCoherent (L := L) (G := G) τ S A)
    {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A) :
    IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := hτ.extension (ζ t)
  norm_one t := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hτ.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul]


end IndChainDecomposition

namespace SibleyDadeHypothesis

/-- **(6.8.1) → (7.10), Frobenius case:** an `IndChainDecomposition` from the
base-anchor common-index p-power X-chain data and generator-level `τ₃` glue.

This is the S09-facing consumer form of the Frobenius/c1 capstone: it first builds the full
`hyp.CoherenceTarget` using the base-anchor X-chain constructor and final generator-level glue, then
turns that coherence witness into the `IndChainDecomposition` package used by the §9 weighted-sum
argument. -/
noncomputable def
    indChainDecomposition_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
          hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction ↥L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ hyp.S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    IndChainDecomposition (L := ↥L) (G := G) hyp.tau ζ d := by
  exact IndChainDecomposition.ofIsCoherent
    (hyp.coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
      hF hXne hstepData ν hagreeX hagreeY hmixed hgen)
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08
