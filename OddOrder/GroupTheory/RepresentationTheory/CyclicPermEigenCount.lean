/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CyclicShiftEigenspace

/-!
# Eigenspace count for a monomial permutation operator (orbit assembly of BG (2.11))

`OddOrder.GroupTheory.RepresentationTheory` shared module: the **orbit assembly** of the
Bender–Glauberman (2.11) keystone `dim E₀ = dim E_m + 1`.

Setup (abstract). A finite-dimensional space `W` with a basis `b : Basis κ F W`, an endomorphism
`T : End F W`, and a permutation `σ : Equiv.Perm κ` such that `T` acts **monomially**:
`T^k (b c) = a • b (σ^k c)` for some nonzero scalar `a`.  We assume `σ^h = 1`, `T^h = 1`, that `ε`
is a primitive `h`-th root of unity, and `(h : F) ≠ 0`.  There is a distinguished `σ`-fixed point
`c₀` with `T (b c₀) = b c₀` (eigenvalue `1`), and every *other* `σ`-orbit is **free** of size `h`
(`C_{P/Z}(xᵏ) = 1`).

Conclusion: `finrank (T.eigenspace (ε^0)) = finrank (T.eigenspace (ε^m)) + 1` for `m ≢ 0`, the
keystone input to BG Theorem 2.5 (`ExtraspecialThm25.lean`).

The method (no global squeeze, no DirectSum): the Fourier projection `proj_m`
(`range_sum_pow_eq_eigenspace`) has range `E_m`, so `{proj_m (b c) : c}` spans `E_m`; orbit
proportionality (`sum_pow_smul_pow_comm`) collapses the span onto orbit representatives; and
disjoint-support independence (`linearIndependent_of_triangular`) makes the representative family a
**basis** of `E_m`.  The count is then the number of orbits contributing to `E_m`: every orbit for
`E_0`, only the free orbits for `E_m` (`m ≠ 0`), so `dim E₀ − dim E_m = 1`.
-/

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction Module

namespace CyclicPermEigen

variable {κ : Type*}
variable (σ : Equiv.Perm κ) {h : ℕ} [NeZero h]

/-- Composing two `ZMod h`-indexed powers of `σ` adds the indices (mod `h`), since `σ^h = 1`. -/
theorem perm_pow_val_add (hσ : σ ^ h = 1) (a b : ZMod h) (c : κ) :
    (σ ^ a.val) ((σ ^ b.val) c) = (σ ^ (a + b).val) c := by
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  have hmod : a.val + b.val ≡ (a + b).val [MOD h] := by
    rw [ZMod.val_add]; exact (Nat.mod_modEq _ _).symm
  rw [pow_eq_pow_of_modEq hσ hmod]

/-! ### The `σ`-orbit setoid on the index type `κ` -/

/-- Two indices are in the same `σ`-orbit (parametrised by `ZMod h`): `c ~ c'` iff
`σ^{k} c = c'` for some `k : ZMod h`.  An equivalence relation once `σ^h = 1`. -/
def orbitSetoid (hσ : σ ^ h = 1) : Setoid κ where
  r c c' := ∃ k : ZMod h, (σ ^ k.val) c = c'
  iseqv := by
    refine ⟨fun c => ⟨0, by simp⟩, ?_, ?_⟩
    · rintro c c' ⟨k, hk⟩
      exact ⟨-k, by rw [← hk, perm_pow_val_add σ hσ (-k) k c]; simp⟩
    · rintro c c' c'' ⟨k, hk⟩ ⟨l, hl⟩
      exact ⟨l + k, by rw [← perm_pow_val_add σ hσ l k c, hk, hl]⟩

/-! ### Geometric sums over `ZMod h` -/

variable {F : Type*} [Field F]

/-- `∑_{k : ZMod h} ζ^{k} = 0` for a root of unity `ζ ≠ 1` (`ζ^h = 1`): multiplying the sum by
`ζ` permutes the summands (`Equiv.addRight 1`), so `(ζ − 1)·sum = 0`. -/
theorem sum_pow_val_eq_zero {ζ : F} (hζh : ζ ^ h = 1) (hζ : ζ ≠ 1) :
    ∑ k : ZMod h, ζ ^ k.val = 0 := by
  have hstep : ∀ k : ZMod h, ζ ^ (k.val + 1) = ζ ^ (k + 1).val := by
    intro k
    refine pow_eq_pow_of_modEq hζh ((ZMod.natCast_eq_natCast_iff _ _ _).1 ?_)
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_rightInverse k, ZMod.natCast_rightInverse (k + 1)]
  have key : ζ * ∑ k : ZMod h, ζ ^ k.val = ∑ k : ZMod h, ζ ^ k.val := by
    rw [Finset.mul_sum]
    calc ∑ k : ZMod h, ζ * ζ ^ k.val
        = ∑ k : ZMod h, ζ ^ (k.val + 1) := by simp_rw [pow_succ']
      _ = ∑ k : ZMod h, ζ ^ (k + 1).val := Finset.sum_congr rfl fun k _ => hstep k
      _ = ∑ k : ZMod h, ζ ^ k.val :=
        Equiv.sum_comp (Equiv.addRight (1 : ZMod h)) fun k => ζ ^ k.val
  have hsub : (ζ - 1) * ∑ k : ZMod h, ζ ^ k.val = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 hsub).resolve_left (sub_ne_zero.2 hζ)

/-- `∑_{k : ZMod h} 1 = h`. -/
theorem sum_one_eq_card : ∑ _k : ZMod h, (1 : F) = (h : F) := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/-! ### Operator power helpers -/

variable {W : Type*} [AddCommGroup W] [Module F W]

/-- A power of an operator fixes any vector it fixes. -/
theorem pow_apply_fixed (T : Module.End F W) {v : W} (hv : T v = v) (n : ℕ) : (T ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, hv, ih]

/-- If `T^h = 1` (`h ≠ 0`) then every power `T^k` is injective: `T^{k(h-1)}` is a left inverse. -/
theorem pow_injective (T : Module.End F W) (hTh : T ^ h = 1) (k : ℕ) :
    Function.Injective (T ^ k) := by
  have hinv : (T ^ (k * (h - 1))) * (T ^ k) = 1 := by
    rw [← pow_add,
      show k * (h - 1) + k = h * k by
        conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne h))]
        ring,
      pow_mul, hTh, one_pow]
  intro x y hxy
  have h2 := congrArg (T ^ (k * (h - 1))) hxy
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hinv, Module.End.one_apply,
    Module.End.one_apply] at h2

/-! ### Coordinates of the Fourier projection `∑_k (ε^m)⁻¹^{k} • T^{k} (b c)` -/

variable {κ : Type*} (b : Basis κ F W) (T : Module.End F W) (σ : Equiv.Perm κ)

/-- **Off-orbit coordinates vanish.** If `c'` is not in the `σ`-orbit of `c`, the Fourier
projection of `b c` has zero `c'`-coordinate (each summand `T^{k}(b c)` is supported on
`b (σ^k c)`). -/
theorem repr_sum_fourier_orbit_zero
    (hmon : ∀ (k : ℕ) (c : κ), ∃ a : F, (T ^ k) (b c) = a • b ((σ ^ k) c))
    {ε : F} {m : ℕ} {c c' : κ} (hcc' : ∀ k : ZMod h, (σ ^ k.val) c ≠ c') :
    b.repr (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c)) c' = 0 := by
  classical
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨a, ha⟩ := hmon k.val c
  rw [ha]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [if_neg (hcc' k), mul_zero, mul_zero]

/-- **Diagonal coordinate is `1` on a free orbit.** If the `σ`-orbit of `c` is free
(`σ^{k} c = c ⟹ k = 0`), the Fourier projection of `b c` has `c`-coordinate `1` (only the `k = 0`
summand `b c` contributes). -/
theorem repr_sum_fourier_self_free
    (hmon : ∀ (k : ℕ) (c : κ), ∃ a : F, (T ^ k) (b c) = a • b ((σ ^ k) c))
    {ε : F} {m : ℕ} {c : κ} (hfree : ∀ k : ZMod h, (σ ^ k.val) c = c → k = 0) :
    b.repr (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c)) c = 1 := by
  classical
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single (0 : ZMod h)]
  · simp only [ZMod.val_zero, pow_zero, one_smul, Module.End.one_apply,
      Basis.repr_self, Finsupp.single_eq_same]
  · intro k _ hk
    obtain ⟨a, ha⟩ := hmon k.val c
    rw [ha]
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul]
    rw [if_neg (fun heq => hk (hfree k heq)), mul_zero, mul_zero]
  · intro hc0; exact absurd (Finset.mem_univ _) hc0

/-- **The Fourier projection of a fixed point is a scalar multiple of it.** If `T (b c₀) = b c₀`
(eigenvalue `1`), then `∑_k (ε^m)⁻¹^{k} • T^{k}(b c₀) = (∑_k (ε^m)⁻¹^{k}) • b c₀`. -/
theorem sum_fourier_fixed_eq (T : Module.End F W)
    {c₀ : κ} (hc₀ : T (b c₀) = b c₀) {ε : F} (m : ℕ) :
    (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c₀))
      = (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val)) • b c₀ := by
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_apply_fixed T hc₀]

end CyclicPermEigen

end OddOrder.RepresentationTheory
