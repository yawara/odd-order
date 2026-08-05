/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.PRegularCosetCharacter
import OddOrder.GroupTheory.RepresentationTheory.UnitCharacter

/-!
# Gorenstein Lemma 7.6

Assembling the pieces (issue 9508, 段 E).  Let `p` be a prime, `u` a `p`-regular element of a
finite group `G`, `P` a `p`-subgroup centralising `u`, and `H = ⟨u⟩ P`.  Put `n = orderOf u` and

`ψ = n · 1_{uP} : H → K`.

Then

* `ψ ∈ ch_R(H)`, because `ψ` is the fibre `λ⁻¹(ζ)` of the linear character `λ` of
  `PRegularCosetCharacter`, scaled by `n` — a `ℤ[ω]`-combination of the powers of `λ`;
* `ψ*(y) = σ(y)/|P|` is an **integer** (i);
* `ψ*(y) = 0` unless `y` lies in the `p`-class of `u` (ii);
* `ψ*(u) = |C_G(u)| / |P| = |C_G(u) : P|` (iii), which is prime to `p` once `P` is a Sylow
  `p`-subgroup of `C_G(u)`.

## Main definitions

* `OddOrder.RepresentationTheory.cosetIndicator` — Gorenstein's `ψ`

## Main results

* `OddOrder.RepresentationTheory.cosetIndicator_mem_adjoinSpan`
* `OddOrder.RepresentationTheory.induceFun_cosetIndicator` — (i)
* `OddOrder.RepresentationTheory.induceFun_cosetIndicator_eq_zero` — (ii)
* `OddOrder.RepresentationTheory.induceFun_cosetIndicator_self` — (iii)

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G K : Type*} [Group G] [Finite G] [Field K] [CharZero K]
  {p : ℕ} {u : G} {P H : Subgroup G} {ω : K} {ζ : Kˣ}

open scoped Classical in
/-- **Gorenstein's `ψ`**: `n · 1_{uP}` as a function on `H`, `n = orderOf u`. -/
noncomputable def cosetIndicator (u : G) (P H : Subgroup G) (K : Type*) [Field K] : ↥H → K :=
  fun h => if (h : G) ∈ leftCosetOf u P then (orderOf u : K) else 0

omit [CharZero K] in
/-- An inverse power of a root of unity is again a nonnegative power of it. -/
theorem inv_pow_eq_pow_of_pow_eq_one {x : K} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) (i : ℕ) :
    (x ^ i)⁻¹ = x ^ (n * i - i) := by
  have hle : i ≤ n * i := Nat.le_mul_of_pos_left i hn
  have hmul : x ^ i * x ^ (n * i - i) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hle, pow_mul, hx, one_pow]
  exact inv_eq_of_mul_eq_one_right hmul

variable (hp : p.Prime) (hu : IsPRegular p u) (hPp : IsPGroup p ↥P)
  (hcomm : ∀ v ∈ P, Commute u v) (hord : orderOf ζ = orderOf u)
  (hgen : ∀ h : G, h ∈ H → ∃ (a : ℕ) (v : G), v ∈ P ∧ h = u ^ a * v)

include hp hu hPp hcomm hord hgen in
open scoped Classical in
/-- **`ψ ∈ ch_R(H)`**: it is the fibre `λ⁻¹(ζ)` scaled by `n`. -/
theorem cosetIndicator_mem_adjoinSpan (hω : IsIntegral ℤ ω)
    (hζω : (ζ : K) ∈ Algebra.adjoin ℤ ({ω} : Set K)) :
    cosetIndicator u P H K ∈ adjoinSpan ω (virtualCharacters K ↥H) := by
  classical
  have hnpos : 0 < orderOf u := orderOf_pos u
  have hζn : (ζ : K) ^ orderOf u = 1 := by
    have h1 : ζ ^ orderOf u = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
    simpa using congrArg (Units.val : Kˣ → K) h1
  have hprim : IsPrimitiveRoot ((ζ : K)) (orderOf u) := by
    rw [← hord]
    exact IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf ζ)
  have hinv : ∀ i : ℕ, ((ζ : K) ^ i)⁻¹ ∈ Algebra.adjoin ℤ ({ω} : Set K) := fun i => by
    rw [inv_pow_eq_pow_of_pow_eq_one hnpos hζn i]
    exact Subalgebra.pow_mem _ hζω _
  have hlam : ∀ h : ↥H,
      ((cosetCharacter hp hu hPp hcomm hord hgen h : Kˣ) : K) ^ orderOf u = 1 := by
    intro h
    obtain ⟨a, v, hv, hh⟩ := hgen (h : G) h.2
    rw [cosetCharacter_apply hp hu hPp hcomm hord hgen hv hh]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]
  have hfun : cosetIndicator u P H K
      = fun h : ↥H =>
        if ((cosetCharacter hp hu hPp hcomm hord hgen h : Kˣ) : K) = (ζ : K)
          then ((orderOf u : ℕ) : K) else 0 := by
    funext h
    rw [cosetIndicator]
    refine if_congr ?_ rfl rfl
    rw [← Units.ext_iff]
    exact (cosetCharacter_apply_eq_iff hp hu hPp hcomm hord hgen).symm
  rw [hfun]
  exact fibreIndicator_mem_adjoinSpan hω hnpos hprim _ hlam hinv

variable (huH : u ∈ H) (hPH : P ≤ H)
  (hcard : Nat.card ↥H = orderOf u * Nat.card ↥P)

omit [Finite G] in
include hcomm huH hPH hcard in
open scoped Classical in
/-- **Gorenstein Lemma 7.6(i)**: the induced function is the integer `σ(y)/|P|`. -/
theorem induceFun_cosetIndicator [Fintype G] (y : G) :
    induceFun H (cosetIndicator u P H K) y
      = ((conjugateCount (leftCosetOf u P) y / Nat.card ↥P : ℕ) : K) := by
  classical
  refine induceFun_indicator_eq_natCast (P := P) _ (leftCosetOf_subset huH hPH) hcard ?_ y
  intro g hg v hv
  have hw : u⁻¹ * g ∈ P := hg
  have hrw : v⁻¹ * g * v = u * (v⁻¹ * (u⁻¹ * g) * v) := by
    have hc : Commute v⁻¹ u := ((hcomm v hv).symm).inv_left
    calc v⁻¹ * g * v = v⁻¹ * (u * (u⁻¹ * g)) * v := by rw [mul_inv_cancel_left]
      _ = (v⁻¹ * u) * ((u⁻¹ * g) * v) := by simp only [mul_assoc]
      _ = (u * v⁻¹) * ((u⁻¹ * g) * v) := by rw [hc.eq]
      _ = u * (v⁻¹ * (u⁻¹ * g) * v) := by simp only [mul_assoc]
  rw [mem_leftCosetOf, hrw, inv_mul_cancel_left]
  exact P.mul_mem (P.mul_mem (P.inv_mem hv) hw) hv

omit [Finite G] in
include hp hu hPp hcomm huH hPH hcard in
open scoped Classical in
/-- **Gorenstein Lemma 7.6(ii)**: the induced function vanishes off the `p`-class of `u`. -/
theorem induceFun_cosetIndicator_eq_zero [Fintype G] {y : G} (hy : ¬ IsConj (pRegularPart p y) u) :
    induceFun H (cosetIndicator u P H K) y = 0 := by
  classical
  rw [induceFun_cosetIndicator hcomm huH hPH hcard y,
    conjugateCount_eq_zero_of_not_isConj hp hu hPp hcomm hy, Nat.zero_div, Nat.cast_zero]

omit [Finite G] in
include hp hu hPp hcomm huH hPH hcard in
open scoped Classical in
/-- **Gorenstein Lemma 7.6(iii)**: at `u` the value is `|C_G(u) : P|`. -/
theorem induceFun_cosetIndicator_self [Fintype G] :
    induceFun H (cosetIndicator u P H K) u
      = ((Nat.card ↥(Subgroup.centralizer ({u} : Set G)) / Nat.card ↥P : ℕ) : K) := by
  classical
  rw [induceFun_cosetIndicator hcomm huH hPH hcard u,
    conjugateCount_self hp hu hPp hcomm]

end OddOrder.RepresentationTheory
