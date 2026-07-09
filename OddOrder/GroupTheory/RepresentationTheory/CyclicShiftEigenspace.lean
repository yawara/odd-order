/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceBlockDecomp

/-!
# Eigenspaces of a cyclic shift (single-cycle core of BG (2.11))

`OddOrder.GroupTheory.RepresentationTheory` shared module: the linear-algebra core behind the
`F[H]`-module structure of `E(P)` in Bender–Glauberman (2.11).  A **cyclic shift** is the
permutation operator of a single `h`-cycle: a finite-dimensional space `W` with a basis
`b : ZMod h → W` and an operator `T` with `T (b j) = b (j + 1)`.  Over a field containing a
primitive `h`-th root of unity `ε`, every eigenvalue `εᵐ` of `T` has a **one-dimensional**
eigenspace (the shift is the regular representation of the cyclic group, which splits into the `h`
distinct characters, each with multiplicity one).

The proof avoids a full diagonalization: the `h` eigenspaces are independent
(`cyclicEigenspaceFin_iSupIndep`, distinct eigenvalues), each is nonzero (explicit eigenvector
`v_i = ∑_j (ε^{i})⁻¹^{j.val} • b j`), and their dimensions sum to at most `dim W = h`, forcing each
to be exactly `1`.

This is the per-orbit input to the pure-permutation eigenspace count yielding the keystone
`dim E₀ = dim E_m + 1`.
-/

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction Module

variable {F : Type*} [Field F]
variable {W : Type*} [AddCommGroup W] [Module F W]

/-- A power of a finite-order element is periodic in its exponent modulo `hh`: if `ζ^hh = 1` and
`a ≡ c [MOD hh]` then `ζ^a = ζ^c`. (Stated for any monoid, so it applies both to roots of unity in
`F` and to finite-order endomorphisms `T : End W`.) -/
theorem pow_eq_pow_of_modEq {M : Type*} [Monoid M] {ζ : M} {hh : ℕ} (hζ : ζ ^ hh = 1) {a c : ℕ}
    (hac : a ≡ c [MOD hh]) : ζ ^ a = ζ ^ c := by
  wlog hle : c ≤ a generalizing a c
  · exact (this hac.symm (not_le.mp hle).le).symm
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hac.symm
  rw [show a = c + hh * t by omega, pow_add, pow_mul, hζ, one_pow, mul_one]

/-- **Triangular linear independence** (disjoint-support criterion). If each `g a` has a basis
coordinate `coord a` at which it is nonzero, while every *other* `g a'` vanishes there (`a ≠ a'`),
then `g` is linearly independent. (Used for vectors supported on disjoint `σ`-orbits: `g ω =
proj (b (rep ω))` is nonzero at coordinate `rep ω` and zero at `rep ω'` for `ω' ≠ ω`.) -/
theorem linearIndependent_of_triangular {ι κ : Type*} [Finite κ] (b : Basis ι F W) (g : κ → W)
    (coord : κ → ι) (hdiag : ∀ a, b.repr (g a) (coord a) ≠ 0)
    (hoff : ∀ a a', a ≠ a' → b.repr (g a) (coord a') = 0) :
    LinearIndependent F g := by
  classical
  haveI := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff]
  intro c hc a₀
  have hb : (b.repr (∑ a, c a • g a)) (coord a₀) = 0 := by rw [hc]; simp
  rw [map_sum] at hb
  simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hb
  rw [Finset.sum_eq_single a₀] at hb
  · exact (mul_eq_zero.mp hb).resolve_right (hdiag a₀)
  · intro a _ ha; rw [hoff a a₀ ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

section CyclicShift

variable {h : ℕ} [NeZero h]

/-- `↑(x.val) = x` for the self-cast `ZMod h → ZMod h`. -/
private theorem natCast_val_zmod (x : ZMod h) : ((x.val : ℕ) : ZMod h) = x :=
  ZMod.natCast_rightInverse x

/-- The explicit eigenvector identity for a cyclic shift on **any family** `b : ZMod h → W` (no
basis needed): `v = ∑_j (ε^i)⁻¹^{j.val} • b j` is an `ε^i`-eigenvector of `T` whenever
`T (b j) = b (j+1)` and `ε^h = 1`. -/
theorem cyclicShift_hasEigenvector (T : Module.End F W) (b : ZMod h → W) {ε : F} (hε : ε ≠ 0)
    (hεpow : ε ^ h = 1) (hb : ∀ j, T (b j) = b (j + 1)) (i : ℕ) :
    T (∑ j : ZMod h, ((ε ^ i)⁻¹ ^ j.val) • b j)
      = (ε ^ i) • ∑ j : ZMod h, ((ε ^ i)⁻¹ ^ j.val) • b j := by
  set ζ : F := (ε ^ i)⁻¹ with hζdef
  have hζne : ζ ≠ 0 := inv_ne_zero (pow_ne_zero i hε)
  have hζpow : ζ ^ h = 1 := by
    rw [hζdef, inv_pow, ← pow_mul, mul_comm, pow_mul, hεpow, one_pow, inv_one]
  -- key index identity: `ζ^{(k-1).val} = ε^i · ζ^{k.val}`
  have hgeom : ∀ k : ZMod h, ζ ^ (k - 1).val = ε ^ i * ζ ^ k.val := by
    intro k
    have hmod : (k - 1).val + 1 ≡ k.val [MOD h] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      push_cast
      rw [natCast_val_zmod (k - 1), natCast_val_zmod k]
      ring
    have hstepmul : ζ ^ (k - 1).val * ζ = ζ ^ k.val := by
      rw [← pow_succ]; exact pow_eq_pow_of_modEq hζpow hmod
    have hεi : ζ⁻¹ = ε ^ i := by rw [hζdef, inv_inv]
    have hstep : ζ ^ (k - 1).val = ζ ^ k.val * ζ⁻¹ := by
      rw [← hstepmul, mul_assoc, mul_inv_cancel₀ hζne, mul_one]
    rw [hstep, hεi, mul_comm]
  -- expand `T v`, reindex by `+1`, apply the geometric identity
  rw [map_sum]
  simp only [map_smul, hb]
  rw [Finset.smul_sum]
  have hLHS : (∑ j : ZMod h, ζ ^ j.val • b (j + 1))
      = ∑ k : ZMod h, ζ ^ (k - 1).val • b k := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod h)) (fun k => ζ ^ (k - 1).val • b k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [hLHS]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hgeom k, mul_smul]

/-- **Projection onto an `ε^i`-eigenspace** (the BG (2.11) `F[H]`-module count input). For a
finite-order endomorphism `T` (`T^h = 1`) and any vector `w`, the "Fourier mode"
`∑_j (ε^i)⁻¹^{j.val} • T^{j.val} w` lies in `T.eigenspace (ε^i)` (`ε^h = 1`). This is
`cyclicShift_hasEigenvector` applied to the cyclic family `j ↦ T^{j.val} w`, on which `T` acts as
the shift (`T (Tʲw) = Tʲ⁺¹w`, periodic since `T^h = 1`). -/
theorem sum_pow_smul_mem_eigenspace (T : Module.End F W) {ε : F} (hε : ε ≠ 0) (hεpow : ε ^ h = 1)
    (hTh : T ^ h = 1) (w : W) (i : ℕ) :
    (∑ j : ZMod h, ((ε ^ i)⁻¹ ^ j.val) • (T ^ j.val) w) ∈ Module.End.eigenspace T (ε ^ i) := by
  rw [Module.End.mem_eigenspace_iff]
  have hb : ∀ j : ZMod h, T ((T ^ j.val) w) = (T ^ (j + 1).val) w := by
    intro j
    have hmod : j.val + 1 ≡ (j + 1).val [MOD h] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      push_cast
      rw [natCast_val_zmod j, natCast_val_zmod (j + 1)]
    have hpow : T ^ (j.val + 1) = T ^ (j + 1).val := pow_eq_pow_of_modEq hTh hmod
    rw [← Module.End.mul_apply, ← pow_succ', hpow]
  exact cyclicShift_hasEigenvector T (fun j => (T ^ j.val) w) hε hεpow hb i

/-- `T^n` acts on an `ε^i`-eigenvector by the scalar `(ε^i)^n`. -/
private theorem pow_apply_of_eigenvector {T : Module.End F W} {ε : F} {i : ℕ} {v : W}
    (hv : T v = (ε ^ i) • v) (n : ℕ) : (T ^ n) v = ((ε ^ i) ^ n) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, ← pow_succ']

/-- **The eigenspace-projection's range is the whole eigenspace.** The "Fourier projection"
`proj := ∑_{k} (ε^i)⁻¹^{k.val} • T^{k.val}` (`= h · π_{ε^i}`) has `range proj = T.eigenspace (ε^i)`
(`ε^h = 1`, `T^h = 1`, `h ≠ 0`): `range ⊆ eigenspace` since each `proj w` is an eigenvector
(`sum_pow_smul_mem_eigenspace`); `eigenspace ⊆ range` since `proj` acts as `h · id` on it
(so `v = proj ((h:F)⁻¹ • v)`). Hence `dim (T.eigenspace (ε^i)) = rank proj`. -/
theorem range_sum_pow_eq_eigenspace (T : Module.End F W) {ε : F} (hε : ε ≠ 0) (hεpow : ε ^ h = 1)
    (hTh : T ^ h = 1) (hh : (h : F) ≠ 0) (i : ℕ) :
    LinearMap.range (∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • T ^ k.val)
      = Module.End.eigenspace T (ε ^ i) := by
  have happly : ∀ w : W, (∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • T ^ k.val) w
      = ∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • (T ^ k.val) w := by
    intro w; simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    rw [happly]
    exact sum_pow_smul_mem_eigenspace T hε hεpow hTh w i
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    refine ⟨(h : F)⁻¹ • v, ?_⟩
    rw [map_smul, happly]
    have hterm : ∀ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • (T ^ k.val) v = v := by
      intro k
      rw [pow_apply_of_eigenvector hv, smul_smul, ← mul_pow, inv_mul_cancel₀ (pow_ne_zero i hε),
        one_pow, one_smul]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_const, Finset.card_univ, ZMod.card,
      ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hh, one_smul]

/-- **The Fourier projection scales by `(ε^i)^n` along the `T`-action** (proportionality engine).
`proj (T^n w) = (ε^i)^n • proj w`, since `proj` commutes with `T^n` (it is a polynomial in `T`) and
`proj w` is an `ε^i`-eigenvector. This makes `proj (b s)` constant-up-to-scalar along each
`σ`-orbit (via the monomial action `b (σ s) ∝ T (b s)`). -/
theorem sum_pow_smul_pow_comm (T : Module.End F W) {ε : F} (hε : ε ≠ 0) (hεpow : ε ^ h = 1)
    (hTh : T ^ h = 1) (w : W) (i n : ℕ) :
    (∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • (T ^ k.val) ((T ^ n) w))
      = (ε ^ i) ^ n • ∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • (T ^ k.val) w := by
  have hsum : (∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • (T ^ k.val) w)
      ∈ Module.End.eigenspace T (ε ^ i) :=
    sum_pow_smul_mem_eigenspace T hε hεpow hTh w i
  rw [Module.End.mem_eigenspace_iff] at hsum
  have hcomm : (∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • (T ^ k.val) ((T ^ n) w))
      = (T ^ n) (∑ k : ZMod h, ((ε ^ i)⁻¹ ^ k.val) • (T ^ k.val) w) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add, ← pow_add, add_comm]
  rw [hcomm, pow_apply_of_eigenvector hsum]

/-- **Each eigenspace of a cyclic shift is one-dimensional.** For `b : Basis (ZMod h) F W` and the
shift `T (b j) = b (j+1)`, and `ε` a primitive `h`-th root of unity,
`finrank (T.eigenspace (ε^{i})) = 1` for every `i : Fin h`. (The regular representation of `ZMod h`
splits into the `h` distinct characters, each with multiplicity one.) -/
theorem finrank_cyclicEigenspaceFin_cyclicShift (T : Module.End F W) (b : Basis (ZMod h) F W)
    {ε : F} (hε : IsPrimitiveRoot ε h)
    (hb : ∀ j, T (b j) = b (j + 1)) (i : Fin h) :
    finrank F (cyclicEigenspaceFin ε T i) = 1 := by
  haveI : FiniteDimensional F W := Module.Finite.of_basis b
  have hε0 : ε ≠ 0 := hε.ne_zero (NeZero.ne h)
  have hεpow : ε ^ h = 1 := hε.pow_eq_one
  -- explicit eigenvector for `ε^{j.1}`, for each `j`
  have hev : ∀ j : Fin h, cyclicEigenspaceFin ε T j ≠ ⊥ := by
    intro j
    rw [Submodule.ne_bot_iff]
    refine ⟨∑ l : ZMod h, ((ε ^ j.1)⁻¹ ^ l.val) • b l, ?_, ?_⟩
    · rw [mem_cyclicEigenspaceFin_iff]
      exact cyclicShift_hasEigenvector T b hε0 hεpow hb j.1
    · -- nonzero: its `0`-coordinate is `(ε^{j.1})⁻¹^0 = 1`
      intro hzero
      have hcoord : (b.repr (∑ l : ZMod h, ((ε ^ j.1)⁻¹ ^ l.val) • b l)) 0 = 1 := by
        rw [map_sum]
        simp only [map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
        rw [Finset.sum_eq_single (0 : ZMod h)]
        · simp
        · intro l _ hl; rw [if_neg hl]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      rw [hzero] at hcoord
      simp at hcoord
  -- the `h` eigenspaces are independent, with dimensions summing to `≤ dim W = h`
  have hindep := cyclicEigenspaceFin_iSupIndep (g := T) hε
  have hge : ∀ j : Fin h, 1 ≤ finrank F (cyclicEigenspaceFin ε T j) := fun j =>
    Submodule.one_le_finrank_iff.mpr (hev j)
  have hsumle : (∑ j : Fin h, finrank F (cyclicEigenspaceFin ε T j)) ≤ finrank F W := by
    rw [← finrank_iSup_of_iSupIndep (fun j : Fin h => cyclicEigenspaceFin ε T j) hindep]
    exact Submodule.finrank_le _
  have hWcard : finrank F W = h := by rw [finrank_eq_card_basis b, ZMod.card]
  have hcardeq : (∑ _j : Fin h, (1 : ℕ)) = h := by simp
  have hsumeq : (∑ _j : Fin h, (1 : ℕ)) = ∑ j : Fin h, finrank F (cyclicEigenspaceFin ε T j) := by
    refine le_antisymm (Finset.sum_le_sum fun j _ => hge j) ?_
    rw [hcardeq]; exact hsumle.trans_eq hWcard
  exact ((Finset.sum_eq_sum_iff_of_le fun k _ => hge k).mp hsumeq i (Finset.mem_univ i)).symm

end CyclicShift

end OddOrder.RepresentationTheory
