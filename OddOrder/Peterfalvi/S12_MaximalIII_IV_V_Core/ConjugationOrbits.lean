/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
public import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible

/-!
# Peterfalvi (10.1): complex conjugation and the conjugation orbits of `Irr(M')`

Complex conjugation of class functions commutes with conjugation by `G`, and for an odd-order
group a nontrivial irreducible character is never conjugate to its complex conjugate
(`conjPerm_not_mem_conjByOrbit`).  These are the inputs to the non-reality of the induced family
of Hypothesis (10.1) (`inducedFamily_hasNoRealCharacters`).  Split from
`S12_MaximalIII_IV_V_Core.Hypothesis` when that file passed 1,500 lines (issue 0190).
-/

@[expose] public section

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open scoped Pointwise

/-- **Complex conjugation commutes with `G`-conjugation** of class functions: for a normal
subgroup `H ⊴ G`, `(θ^g)‾ = (θ‾)^g`.  Both sides evaluate to `star (θ ⟨g·h·g⁻¹⟩)`.  This is the
`σ`-commutes-with-the-`M`-action input to the odd-order orbit argument showing that an induced
character `Ind_{M'}^M θ` (`θ ≠ 1`) is non-real. -/
theorem conjBy_conj {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    (g : K) (θ : ClassFunction ↥H ℂ) :
    (ClassFunction.conjBy g θ).conj = ClassFunction.conjBy g θ.conj := by
  ext h
  simp only [ClassFunction.conj_apply, ClassFunction.conjBy_apply]

/-- **The complex-conjugation involution `conjPerm` commutes with `M`-conjugation `conjBy`** on the
irreducible characters of a normal subgroup `H ⊴ K`.  Lifts `conjBy_conj` to `IrreducibleCharacter`
via the coercion lemmas.  This is what makes the conjugation orbit `conjByOrbit θ` invariant under
`conjPerm`, the key to the odd-order non-reality of `Ind_{M'}^M θ`. -/
theorem conjPerm_conjBy_comm {K : Type*} [Group K] {H : Subgroup K} [H.Normal] [Finite ↥H]
    (g : K) (θ : IrreducibleCharacter ↥H) :
    IrreducibleCharacter.conjPerm ↥H (IrreducibleCharacter.conjBy g θ)
      = IrreducibleCharacter.conjBy g (IrreducibleCharacter.conjPerm ↥H θ) := by
  refine IrreducibleCharacter.ext ?_
  simp only [IrreducibleCharacter.conjPerm_apply_coe, IrreducibleCharacter.coe_conjBy]
  exact conjBy_conj g (θ : ClassFunction ↥H ℂ)

/-- **The conjugation orbit `conjByOrbit θ` is `conjPerm`-invariant** once it contains `θ̄`.  If the
complex conjugate `θ̄ = conjPerm θ` lies in the `M`-conjugation orbit of `θ`, then so does the
conjugate of every orbit member.  Combines `conjPerm_conjBy_comm` (`σ` commutes with the action)
with the group-action laws (`conjBy_mul`). -/
theorem conjPerm_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal] [Finite ↥H]
    {θ : IrreducibleCharacter ↥H}
    (hmem : IrreducibleCharacter.conjPerm ↥H θ ∈ IrreducibleCharacter.conjByOrbit (G := K) θ)
    {η : IrreducibleCharacter ↥H} (hη : η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ) :
    IrreducibleCharacter.conjPerm ↥H η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  obtain ⟨g, rfl⟩ := hη
  rw [conjPerm_conjBy_comm]
  obtain ⟨g₀, hg₀⟩ := hmem
  rw [← hg₀, ← IrreducibleCharacter.conjBy_mul]
  exact IrreducibleCharacter.conjBy_mem_conjByOrbit θ (g₀ * g)

/-- **`G`-conjugation fixes the trivial character.** -/
theorem conjBy_trivial {K : Type*} [Group K] {H : Subgroup K} [H.Normal] (g : K) :
    IrreducibleCharacter.conjBy g (trivialIrreducibleCharacter ↥H)
      = trivialIrreducibleCharacter ↥H := by
  apply IrreducibleCharacter.ext
  ext h
  simp [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]

/-- **The trivial character is not in the conjugation orbit of a nontrivial character.**  If
`conjBy g θ = 1` then `θ = conjBy g⁻¹ 1 = 1` (`conjBy_trivial`). -/
theorem trivial_not_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    {θ : IrreducibleCharacter ↥H} (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    trivialIrreducibleCharacter ↥H ∉ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  rintro ⟨g, hg⟩
  apply hθ
  have : θ = IrreducibleCharacter.conjBy g⁻¹ (trivialIrreducibleCharacter ↥H) := by
    rw [← hg]; exact (IrreducibleCharacter.conjBy_inv_conjBy g θ).symm
  rw [this, conjBy_trivial]

/-- **No `conjPerm`-fixed point in the conjugation orbit of a nontrivial character** (odd order).
A fixed point `η` of `conjPerm` is real (`conjPerm_eq_self_iff`), hence trivial in odd order
(`not_isReal_of_ne_trivial_of_odd_card'`); but the trivial character is not in `conjByOrbit θ` for
`θ ≠ 1` (`trivial_not_mem_conjByOrbit`). -/
theorem conjPerm_ne_self_of_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    [Finite ↥H] (hodd : Odd (Nat.card ↥H)) {θ : IrreducibleCharacter ↥H}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥H) {η : IrreducibleCharacter ↥H}
    (hη : η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ) :
    IrreducibleCharacter.conjPerm ↥H η ≠ η := by
  intro hfix
  have hreal : ClassFunction.IsReal (η : ClassFunction ↥H ℂ) :=
    (IrreducibleCharacter.conjPerm_eq_self_iff η).mp hfix
  have htriv : η = trivialIrreducibleCharacter ↥H := by
    by_contra hne
    exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hne hreal
  exact trivial_not_mem_conjByOrbit hθ (htriv ▸ hη)

/-- **`conjPerm` is an involution**: `(χ̄)‾ = χ`. -/
theorem conjPerm_conjPerm {L : Type*} [Group L] [Finite L] (χ : IrreducibleCharacter L) :
    IrreducibleCharacter.conjPerm L (IrreducibleCharacter.conjPerm L χ) = χ := by
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.conjPerm_apply_coe, IrreducibleCharacter.conjPerm_apply_coe,
    ClassFunction.conj_conj]

/-- **A nontrivial character is not conjugate to its complex conjugate, in odd order** (the orbit
form of Peterfalvi (1.1)).  The conjugation orbit `conjByOrbit θ` has odd cardinality `[K : I_θ]`
(`card_conjByOrbit_eq_index_inertia`, a divisor of the odd `|K|`); were `θ̄ ∈ conjByOrbit θ`, the
involution `σ = conjPerm` would restrict to it, and by `card_fixedPoints_modEq` (`p = 2`) an
involution on an odd-cardinality set has a fixed point — a real, hence trivial, character in the
orbit, impossible by `conjPerm_ne_self_of_mem_conjByOrbit`. -/
theorem conjPerm_not_mem_conjByOrbit {K : Type*} [Group K] [Finite K] {H : Subgroup K} [H.Normal]
    (hodd : Odd (Nat.card K)) {θ : IrreducibleCharacter ↥H}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    IrreducibleCharacter.conjPerm ↥H θ ∉ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  intro hmem
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have : Invertible (Nat.card K : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have : Invertible (Nat.card ↥H : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have : Fintype ↥(IrreducibleCharacter.conjByOrbit (G := K) θ) := Fintype.ofFinite _
  have hoddH : Odd (Nat.card ↥H) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  set f : Function.End ↥(IrreducibleCharacter.conjByOrbit (G := K) θ) :=
    fun η => ⟨IrreducibleCharacter.conjPerm ↥H η.1, conjPerm_mem_conjByOrbit hmem η.2⟩ with hf
  have hf2 : f ^ 2 = 1 := by
    funext η
    change f (f η) = η
    exact Subtype.ext (conjPerm_conjPerm η.1)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) (by simpa using hf2)
  have hodd_orbit : Odd (Fintype.card ↥(IrreducibleCharacter.conjByOrbit (G := K) θ)) := by
    rw [← Nat.card_eq_fintype_card, card_conjByOrbit_eq_index_inertia]
    exact hodd.of_dvd_nat (Subgroup.index_dvd_card _)
  have hfp_pos : 0 < Fintype.card f.fixedPoints := by
    have h1 := Nat.odd_iff.mp hodd_orbit
    rw [Nat.ModEq] at hmod
    omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hfp_pos
  have hxf : f x.1 = x.1 := x.2
  have hfix : IrreducibleCharacter.conjPerm ↥H x.1.1 = x.1.1 := Subtype.ext_iff.mp hxf
  exact conjPerm_ne_self_of_mem_conjByOrbit hoddH hθ x.1.2 hfix

end OddOrder.Peterfalvi.S12
