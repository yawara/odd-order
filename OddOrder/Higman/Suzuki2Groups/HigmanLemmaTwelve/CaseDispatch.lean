/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.PrescribedFactorCoordinates
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedTermValue
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SupportPinning
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types
import OddOrder.Higman.Suzuki2Groups.HigmanTypesCD

/-!
# Higman Lemma 12: case-dispatch normalizations

G. Higman, *Suzuki 2-groups*, pp. 90--92.  Higman's case split on the factor
automorphism pair `(θ, φ)` uses a normalization freedom before the exponent
arithmetic: `A(n, θ)` and `A(n, θ⁻¹)` are isomorphic (p. 91), so the
Frobenius exponent of a noncommutative factor may be assumed to lie in
`0 < r ≤ n/2`.

* `ringAutLinearEquiv` — a ring automorphism of a `ZMod 2`-algebra, viewed as
  a `ZMod 2`-linear equivalence.
* `NoncommutativeFactorCoordinateData.flip` — the `A(n, θ) ≅ A(n, θ⁻¹)`
  isomorphism at the coordinate level: compose the quotient coordinate with
  `θ`, leaving the prescribed ambient kernel coordinate `ePhi` untouched.
  The type-A parameters transform as `θ ↦ θ⁻¹`, `λ ↦ θ(λ)`.
* `NoncommutativeFactorCoordinateData.exists_flip_frobenius_le_half` — the
  resulting "we may suppose that `0 < r ≤ ½n`": every noncommutative factor
  admits coordinates (itself or its flip) whose `θ` is `Frob^r` with
  `0 < r`, `2r ≤ n`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uH

noncomputable section

local instance caseDispatchLayerCommGroup
    (H : Type uH) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance caseDispatchLayerModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-! ### Ring automorphisms as `ZMod 2`-linear equivalences -/

/-- A ring automorphism of a `ZMod 2`-module ring is `ZMod 2`-linear. -/
def ringAutLinearEquiv {F : Type*} [Ring F] [Module (ZMod 2) F]
    (theta : RingAut F) : F ≃ₗ[ZMod 2] F :=
  { theta.toAddEquiv with
    map_smul' := ZMod.map_smul theta.toRingHom.toAddMonoidHom }

@[simp] theorem ringAutLinearEquiv_apply {F : Type*} [Ring F]
    [Module (ZMod 2) F] (theta : RingAut F) (x : F) :
    ringAutLinearEquiv theta x = theta x := rfl

@[simp] theorem ringAutLinearEquiv_symm_apply {F : Type*} [Ring F]
    [Module (ZMod 2) F] (theta : RingAut F) (x : F) :
    (ringAutLinearEquiv theta).symm x = theta⁻¹ x := rfl

/-! ### The `A(n, θ) ≅ A(n, θ⁻¹)` flip -/

variable {P : Type uH} [Group P]
  {Y : Subgroup (MulAut P)}
  [IsMulCommutative ↑(frattini P)]
  [Module (ZMod 2) (Additive ↑(frattini P))]
  {S : Subgroup P}
  {hSinv : IsAInvariant Y.subtype S}
  {hPhiS : frattini P ≤ S}
  {c : Y} {n : Nat}
  {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
  {nu : GaloisField 2 n}

/-- **Higman p. 91, "`A(n, θ)` and `A(n, θ⁻¹)` are isomorphic."**  Flip a
noncommutative factor coordinate by composing the quotient coordinate with
`θ`; the prescribed ambient kernel coordinate is untouched.  The type-A
parameters transform as `θ ↦ θ⁻¹`, `λ ↦ θ(λ)`, and the source relation
`ν = λ θ(λ)` is preserved. -/
def NoncommutativeFactorCoordinateData.flip
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu where
  hK1 := data.hK1
  hterm := data.hterm
  hSq := data.hSq
  eKernel := data.eKernel
  eKernel_eq := data.eKernel_eq
  theta := data.theta⁻¹
  eQuot := data.eQuot.trans (ringAutLinearEquiv data.theta)
  lambda := data.theta data.lambda
  theta_ne_one := fun h => data.theta_ne_one (inv_eq_one.mp h)
  theta_order_odd := by
    rw [orderOf_inv]
    exact data.theta_order_odd
  kernel_compatible := data.kernel_compatible
  quotient_compatible := fun v => by
    simp only [LinearEquiv.trans_apply, ringAutLinearEquiv_apply,
      data.quotient_compatible v, map_mul]
  square_normal := fun beta => by
    have hcancel : data.theta (data.theta⁻¹ beta) = beta := by
      rw [← RingAut.mul_apply, mul_inv_cancel, RingAut.one_apply]
    have harg : (data.eQuot.trans (ringAutLinearEquiv data.theta)).symm beta
        = data.eQuot.symm (data.theta⁻¹ beta) := by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, ringAutLinearEquiv_apply, hcancel]
    rw [harg, data.square_normal, hcancel]
    exact mul_comm _ _
  kernel_eigenvalue_eq := by
    have hcancel : data.theta⁻¹ (data.theta data.lambda) = data.lambda := by
      rw [← RingAut.mul_apply, inv_mul_cancel, RingAut.one_apply]
    rw [hcancel, mul_comm]
    exact data.kernel_eigenvalue_eq

@[simp] theorem NoncommutativeFactorCoordinateData.flip_theta
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    data.flip.theta = data.theta⁻¹ := rfl

@[simp] theorem NoncommutativeFactorCoordinateData.flip_lambda
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    data.flip.lambda = data.theta data.lambda := rfl

@[simp] theorem NoncommutativeFactorCoordinateData.flip_eKernel
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    data.flip.eKernel = data.eKernel := rfl

/-! ### The `0 < r ≤ n/2` normalization -/

/-- The Frobenius exponent of a noncommutative factor automorphism is
nonzero: `θ = Frob^r ≠ 1` forces `r ≢ 0`. -/
theorem NoncommutativeFactorCoordinateData.frobenius_exponent_ne_zero
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
    {r : Fin n}
    (hr : data.theta = (frobeniusEquiv (GaloisField 2 n) 2) ^ (r : ℕ)) :
    (r : ℕ) ≠ 0 := by
  intro h0
  apply data.theta_ne_one
  rw [hr, h0, pow_zero]

/-- **Higman p. 91, "we may suppose that `0 < r ≤ ½n`."**  Every
noncommutative factor admits coordinates — itself or its flip — whose
automorphism is `Frob^r` with `0 < r` and `2r ≤ n`.  The flip realises
`A(n, θ) ≅ A(n, θ⁻¹)` without moving the prescribed ambient kernel
coordinate, so the two candidate coordinates share `ePhi` and `ν`. -/
theorem NoncommutativeFactorCoordinateData.exists_flip_frobenius_le_half
    (hn : n ≠ 0)
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    ∃ (data' : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu)
      (r : ℕ), 0 < r ∧ 2 * r ≤ n ∧
      data'.theta = (frobeniusEquiv (GaloisField 2 n) 2) ^ r := by
  obtain ⟨r0, hr0⟩ := exists_frobenius_pow_eq_of_ringAut n hn data.theta
  have hr0ne : (r0 : ℕ) ≠ 0 := data.frobenius_exponent_ne_zero hr0
  by_cases h2r : 2 * (r0 : ℕ) ≤ n
  · exact ⟨data, r0, Nat.pos_of_ne_zero hr0ne, h2r, hr0⟩
  · -- flip: `θ⁻¹ = Frob^(n - r₀)` with `2(n - r₀) ≤ n`
    have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
      simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn
    have hfrobn : (frobeniusEquiv (GaloisField 2 n) 2) ^ n = 1 := by
      have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
        orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard
      calc (frobeniusEquiv (GaloisField 2 n) 2) ^ n
          = (frobeniusEquiv (GaloisField 2 n) 2)
            ^ orderOf (frobeniusEquiv (GaloisField 2 n) 2) := by rw [horder]
        _ = 1 := pow_orderOf_eq_one _
    have hmul : (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - (r0 : ℕ))
        * (frobeniusEquiv (GaloisField 2 n) 2) ^ (r0 : ℕ) = 1 := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt r0.2)]
      exact hfrobn
    have hinv : data.theta⁻¹
        = (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - (r0 : ℕ)) := by
      rw [hr0]
      exact (eq_inv_of_mul_eq_one_left hmul).symm
    refine ⟨data.flip, n - (r0 : ℕ), ?_, ?_, ?_⟩
    · have := r0.2
      omega
    · have := r0.2
      omega
    · rw [data.flip_theta, hinv]

/-! ### Monomialization of the mixed term

From `M(λα, μβ) = ν M(α, β)` and `M ≠ 0`, the Frobenius coefficients of `M`
are supported on pairs with `λ^{2^i} μ^{2^j} = ν`; the support pinning of
`SupportPinning` then collapses the double sum to Higman's case-specific
monomials. -/

/-- Collapse a Frobenius double sum when every nonzero coefficient sits at the
single pair `(i₀, j₀)`. -/
theorem frobenius_double_sum_single {n : ℕ}
    (c : Fin n → Fin n → GaloisField 2 n) {i0 j0 : Fin n}
    (hpin : ∀ i j : Fin n, c i j ≠ 0 → i = i0 ∧ j = j0)
    (α β : GaloisField 2 n) :
    (∑ i : Fin n, ∑ j : Fin n,
      c i j • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) α *
        (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
      = c i0 j0 * (α ^ 2 ^ (i0 : ℕ) * β ^ 2 ^ (j0 : ℕ)) := by
  have hzero : ∀ i j : Fin n, ¬(i = i0 ∧ j = j0) → c i j = 0 := by
    intro i j hne
    by_contra hcne
    exact hne (hpin i j hcne)
  calc (∑ i : Fin n, ∑ j : Fin n,
      c i j • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) α *
        (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
      = ∑ j : Fin n, c i0 j • ((frobeniusEquiv (GaloisField 2 n) 2
          ^ (i0 : ℕ)) α * (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β) :=
        Finset.sum_eq_single i0
          (fun i _ hi => Finset.sum_eq_zero fun j _ => by
            rw [hzero i j (fun h => hi h.1), zero_smul])
          (fun h => absurd (Finset.mem_univ i0) h)
    _ = c i0 j0 • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i0 : ℕ)) α *
          (frobeniusEquiv (GaloisField 2 n) 2 ^ (j0 : ℕ)) β) :=
        Finset.sum_eq_single j0
          (fun j _ hj => by rw [hzero i0 j (fun h => hj h.2), zero_smul])
          (fun h => absurd (Finset.mem_univ j0) h)
    _ = c i0 j0 * (α ^ 2 ^ (i0 : ℕ) * β ^ 2 ^ (j0 : ℕ)) := by
        rw [smul_eq_mul, frobeniusEquiv_pow_apply, frobeniusEquiv_pow_apply]

/-- Collapse a Frobenius double sum when every nonzero coefficient sits at one
of the two pairs `(i₀, j₀)`, `(i₁, j₁)` with `i₀ ≠ i₁`. -/
theorem frobenius_double_sum_pair {n : ℕ}
    (c : Fin n → Fin n → GaloisField 2 n) {i0 j0 i1 j1 : Fin n}
    (hii : i0 ≠ i1)
    (hpin : ∀ i j : Fin n, c i j ≠ 0 →
      (i = i0 ∧ j = j0) ∨ (i = i1 ∧ j = j1))
    (α β : GaloisField 2 n) :
    (∑ i : Fin n, ∑ j : Fin n,
      c i j • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) α *
        (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
      = c i0 j0 * (α ^ 2 ^ (i0 : ℕ) * β ^ 2 ^ (j0 : ℕ))
        + c i1 j1 * (α ^ 2 ^ (i1 : ℕ) * β ^ 2 ^ (j1 : ℕ)) := by
  have hzero : ∀ i j : Fin n,
      ¬((i = i0 ∧ j = j0) ∨ (i = i1 ∧ j = j1)) → c i j = 0 := by
    intro i j hne
    by_contra hcne
    exact hne (hpin i j hcne)
  have hinner : ∀ i : Fin n, i ≠ i0 → i ≠ i1 →
      (∑ j : Fin n, c i j • ((frobeniusEquiv (GaloisField 2 n) 2
        ^ (i : ℕ)) α * (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
        = 0 := by
    intro i hi0 hi1
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hzero i j (fun h => h.elim (fun h' => hi0 h'.1) fun h' => hi1 h'.1),
      zero_smul]
  have hsubset : ∑ i : Fin n, ∑ j : Fin n,
      c i j • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) α *
        (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β)
      = ∑ i ∈ ({i0, i1} : Finset (Fin n)), ∑ j : Fin n,
        c i j • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) α *
          (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β) :=
    (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      push_neg at hi
      exact hinner i hi.1 hi.2).symm
  have hrow : ∀ (i2 j2 : Fin n), (∀ i j : Fin n, c i j ≠ 0 → i ≠ i2 → False) →
      True := fun _ _ _ => trivial
  rw [hsubset, Finset.sum_pair hii]
  have hleft : (∑ j : Fin n, c i0 j • ((frobeniusEquiv (GaloisField 2 n) 2
      ^ (i0 : ℕ)) α * (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
      = c i0 j0 * (α ^ 2 ^ (i0 : ℕ) * β ^ 2 ^ (j0 : ℕ)) := by
    calc (∑ j : Fin n, c i0 j • ((frobeniusEquiv (GaloisField 2 n) 2
        ^ (i0 : ℕ)) α * (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
        = c i0 j0 • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i0 : ℕ)) α *
            (frobeniusEquiv (GaloisField 2 n) 2 ^ (j0 : ℕ)) β) :=
          Finset.sum_eq_single j0
            (fun j _ hj => by
              rw [hzero i0 j ?_, zero_smul]
              rintro (⟨-, hj'⟩ | ⟨hi', -⟩)
              · exact hj hj'
              · exact hii (hi'.symm ▸ rfl)
            )
            (fun h => absurd (Finset.mem_univ j0) h)
      _ = c i0 j0 * (α ^ 2 ^ (i0 : ℕ) * β ^ 2 ^ (j0 : ℕ)) := by
          rw [smul_eq_mul, frobeniusEquiv_pow_apply, frobeniusEquiv_pow_apply]
  have hright : (∑ j : Fin n, c i1 j • ((frobeniusEquiv (GaloisField 2 n) 2
      ^ (i1 : ℕ)) α * (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
      = c i1 j1 * (α ^ 2 ^ (i1 : ℕ) * β ^ 2 ^ (j1 : ℕ)) := by
    calc (∑ j : Fin n, c i1 j • ((frobeniusEquiv (GaloisField 2 n) 2
        ^ (i1 : ℕ)) α * (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β))
        = c i1 j1 • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i1 : ℕ)) α *
            (frobeniusEquiv (GaloisField 2 n) 2 ^ (j1 : ℕ)) β) :=
          Finset.sum_eq_single j1
            (fun j _ hj => by
              rw [hzero i1 j ?_, zero_smul]
              rintro (⟨hi', -⟩ | ⟨-, hj'⟩)
              · exact hii (hi' ▸ rfl)
              · exact hj hj'
            )
            (fun h => absurd (Finset.mem_univ j1) h)
      _ = c i1 j1 * (α ^ 2 ^ (i1 : ℕ) * β ^ 2 ^ (j1 : ℕ)) := by
          rw [smul_eq_mul, frobeniusEquiv_pow_apply, frobeniusEquiv_pow_apply]
  rw [hleft, hright]

/-- **Support extraction from the mixed-term functional equation.**  A nonzero
`ZMod 2`-bilinear `M` with `M(λα, μβ) = ν M(α, β)` has a Frobenius
representation whose nonzero coefficients all sit on the eigenvalue equation
`λ^{2^i} μ^{2^j} = ν`, with at least one nonzero coefficient. -/
theorem exists_equivariant_frobenius_repr {n : ℕ} (hn : n ≠ 0)
    (M : GaloisField 2 n →ₗ[ZMod 2]
      (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (lam mu nu : GaloisField 2 n)
    (hequiv : ∀ α β : GaloisField 2 n, M (lam * α) (mu * β) = nu * M α β)
    (hM0 : ∃ α β : GaloisField 2 n, M α β ≠ 0) :
    ∃ c : Fin n → Fin n → GaloisField 2 n,
      (∀ α β : GaloisField 2 n, M α β = ∑ i : Fin n, ∑ j : Fin n,
        c i j • ((frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) α *
          (frobeniusEquiv (GaloisField 2 n) 2 ^ (j : ℕ)) β)) ∧
      (∀ i j : Fin n, c i j ≠ 0 →
        lam ^ 2 ^ (i : ℕ) * mu ^ 2 ^ (j : ℕ) = nu) ∧
      ∃ i j : Fin n, c i j ≠ 0 := by
  obtain ⟨c, hc, hcoeff⟩ := bilinear_equivariance_coeff n hn M lam mu nu hequiv
  refine ⟨c, hc, fun i j hne => ?_, ?_⟩
  · have h' : c i j * (lam ^ 2 ^ (i : ℕ) * mu ^ 2 ^ (j : ℕ))
        = c i j * nu := by
      rw [hcoeff i j]
      exact mul_comm _ _
    exact mul_left_cancel₀ hne h'
  · by_contra hall
    push_neg at hall
    obtain ⟨α, β, hαβ⟩ := hM0
    apply hαβ
    rw [hc α β]
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      rw [hall i j, zero_smul]

/-- **Higman p. 90, case `θ = φ = 1`: the mixed term is a single diagonal
monomial `c₀ αβ`.**  (`[x_i, y_j] = 0` for `i ≠ j`, read on the
`ν`-eigenline.) -/
theorem mixedTerm_monomial_of_theta_one {n : ℕ} (hn : 0 < n)
    (M : GaloisField 2 n →ₗ[ZMod 2]
      (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (lam nu : GaloisField 2 n)
    (hord : orderOf lam = 2 ^ n - 1)
    (hnu : lam ^ (1 + 2 ^ 0) = nu)
    (hequiv : ∀ α β : GaloisField 2 n, M (lam * α) (lam * β) = nu * M α β)
    (hM0 : ∃ α β : GaloisField 2 n, M α β ≠ 0) :
    ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
      ∀ α β : GaloisField 2 n, M α β = c0 * (α * β) := by
  obtain ⟨c, hc, hsupp, iw, jw, hw⟩ :=
    exists_equivariant_frobenius_repr (by omega) M lam lam nu hequiv hM0
  have hpin : ∀ i j : Fin n, c i j ≠ 0 →
      i = (⟨0, hn⟩ : Fin n) ∧ j = (⟨0, hn⟩ : Fin n) := by
    intro i j hcne
    have hpow : lam ^ 2 ^ (i : ℕ) * lam ^ 2 ^ (j : ℕ) = nu := hsupp i j hcne
    rcases higman_typeB_support_pinning (r := 0) hn i.isLt j.isLt
        hord hnu hpow with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact ⟨Fin.ext h1, Fin.ext h2⟩
  refine ⟨c ⟨0, hn⟩ ⟨0, hn⟩, ?_, fun α β => ?_⟩
  · obtain ⟨hie, hje⟩ := hpin iw jw hw
    have hce : c (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) = c iw jw := by
      rw [hie, hje]
    rw [hce]
    exact hw
  · rw [hc α β, frobenius_double_sum_single c hpin α β]
    norm_num

/-- **Higman p. 91, case `θ = φ ≠ 1`: the mixed term has at most the two
monomials `c₁ α β^{2^r} + c₂ α^{2^r} β`.**  (`[x_i, y_j] = 0` for
`|j - i| ≠ r`, read on the `ν`-eigenline; Higman's shear normalisation
`y₀ ↦ ρ x₀ + y₀` later removes one of the two.) -/
theorem mixedTerm_two_monomials_of_theta_eq {n r : ℕ}
    (hr0 : r ≠ 0) (hrn : r < n)
    (M : GaloisField 2 n →ₗ[ZMod 2]
      (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (lam nu : GaloisField 2 n)
    (hord : orderOf lam = 2 ^ n - 1)
    (hnu : lam ^ (1 + 2 ^ r) = nu)
    (hequiv : ∀ α β : GaloisField 2 n, M (lam * α) (lam * β) = nu * M α β)
    (hM0 : ∃ α β : GaloisField 2 n, M α β ≠ 0) :
    ∃ c1 c2 : GaloisField 2 n, ¬(c1 = 0 ∧ c2 = 0) ∧
      ∀ α β : GaloisField 2 n,
        M α β = c1 * (α * β ^ 2 ^ r) + c2 * (α ^ 2 ^ r * β) := by
  have hn : 0 < n := by omega
  obtain ⟨c, hc, hsupp, iw, jw, hw⟩ :=
    exists_equivariant_frobenius_repr (by omega) M lam lam nu hequiv hM0
  have hii : (⟨0, hn⟩ : Fin n) ≠ (⟨r, hrn⟩ : Fin n) := by
    intro h
    exact hr0 (congrArg Fin.val h).symm
  have hpin : ∀ i j : Fin n, c i j ≠ 0 →
      (i = (⟨0, hn⟩ : Fin n) ∧ j = (⟨r, hrn⟩ : Fin n)) ∨
      (i = (⟨r, hrn⟩ : Fin n) ∧ j = (⟨0, hn⟩ : Fin n)) := by
    intro i j hcne
    have hpow : lam ^ 2 ^ (i : ℕ) * lam ^ 2 ^ (j : ℕ) = nu := hsupp i j hcne
    rcases higman_typeB_support_pinning hrn i.isLt j.isLt
        hord hnu hpow with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
    · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
  refine ⟨c ⟨0, hn⟩ ⟨r, hrn⟩, c ⟨r, hrn⟩ ⟨0, hn⟩, ?_, fun α β => ?_⟩
  · rintro ⟨h1, h2⟩
    rcases hpin iw jw hw with ⟨hie, hje⟩ | ⟨hie, hje⟩
    · apply hw
      rw [hie, hje]
      exact h1
    · apply hw
      rw [hie, hje]
      exact h2
  · rw [hc α β, frobenius_double_sum_pair c hii hpin α β]
    norm_num

/-- **Higman p. 91, case `θ ≠ 1`, `φ = 1`: `2r + 1 = n` and the mixed term is
the single monomial `c₀ α^{2^{n-1}} β^{2^{r+1}}`** — the type-`C` pairing
`ε · (α^{1/2} · β^{2^{r+1}})` before the `ε`-normalisation. -/
theorem mixedTerm_monomial_typeC {n r : ℕ} (hr : 0 < r) (h2r : 2 * r ≤ n)
    (M : GaloisField 2 n →ₗ[ZMod 2]
      (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (lam mu nu : GaloisField 2 n)
    (hord : orderOf lam = 2 ^ n - 1)
    (hnu : lam ^ (1 + 2 ^ r) = nu)
    (hmu : mu ^ 2 = nu) (hmupow : mu ^ (2 ^ n - 1) = 1)
    (hequiv : ∀ α β : GaloisField 2 n, M (lam * α) (mu * β) = nu * M α β)
    (hM0 : ∃ α β : GaloisField 2 n, M α β ≠ 0) :
    2 * r + 1 = n ∧
    ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
      ∀ α β : GaloisField 2 n,
        M α β = c0 * (α ^ 2 ^ (n - 1) * β ^ 2 ^ (r + 1)) := by
  obtain ⟨c, hc, hsupp, iw, jw, hw⟩ :=
    exists_equivariant_frobenius_repr (by omega) M lam mu nu hequiv hM0
  obtain ⟨hn', -, -⟩ :=
    higman_typeC_support_pinning hr h2r iw.isLt jw.isLt hord hnu hmu hmupow
      (hsupp iw jw hw)
  have hi0lt : n - 1 < n := by omega
  have hj0lt : r + 1 < n := by omega
  have hpin : ∀ i j : Fin n, c i j ≠ 0 →
      i = (⟨n - 1, hi0lt⟩ : Fin n) ∧ j = (⟨r + 1, hj0lt⟩ : Fin n) := by
    intro i j hcne
    obtain ⟨-, hi', hj'⟩ :=
      higman_typeC_support_pinning hr h2r i.isLt j.isLt hord hnu hmu hmupow
        (hsupp i j hcne)
    exact ⟨Fin.ext hi', Fin.ext hj'⟩
  refine ⟨hn', c ⟨n - 1, hi0lt⟩ ⟨r + 1, hj0lt⟩, ?_, fun α β => ?_⟩
  · obtain ⟨hie, hje⟩ := hpin iw jw hw
    have hce : c (⟨n - 1, hi0lt⟩ : Fin n) (⟨r + 1, hj0lt⟩ : Fin n)
        = c iw jw := by
      rw [hie, hje]
    rw [hce]
    exact hw
  · rw [hc α β, frobenius_double_sum_single c hpin α β]

/-- Convert a `ZMod n` pin of a `Fin n` index into an exact value. -/
private theorem fin_val_eq_of_zmod_eq {n : ℕ} {i : Fin n} {a : ℕ}
    (h : ((i : ℕ) : ZMod n) = ((a : ℕ) : ZMod n)) : (i : ℕ) = a % n := by
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rwa [Nat.mod_eq_of_lt i.isLt] at hmod

/-- **Higman pp. 91--92, independent case: the mixed term is the single
monomial `c₀ α^{2^{3r}} β^{2^r}`** (or its mirror under `X ↔ Y`), together
with the type-`D` parameter facts `s ≡ 2r`, `5r ≡ 0 (mod n)`. -/
theorem mixedTerm_monomial_typeD {n r s : ℕ} (hn : 0 < n)
    (hr : (r : ZMod n) ≠ 0) (hs : (s : ZMod n) ≠ 0)
    (hrs : (r : ZMod n) + (s : ZMod n) ≠ 0)
    (hrs' : (r : ZMod n) ≠ (s : ZMod n))
    (M : GaloisField 2 n →ₗ[ZMod 2]
      (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (lam mu nu : GaloisField 2 n)
    (hord : orderOf nu = 2 ^ n - 1)
    (hlam : lam ^ (1 + 2 ^ r) = nu) (hmu : mu ^ (1 + 2 ^ s) = nu)
    (hequiv : ∀ α β : GaloisField 2 n, M (lam * α) (mu * β) = nu * M α β)
    (hM0 : ∃ α β : GaloisField 2 n, M α β ≠ 0) :
    ((s : ZMod n) = 2 * (r : ZMod n) ∧ 5 * (r : ZMod n) = 0 ∧
      ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
        ∀ α β : GaloisField 2 n,
          M α β = c0 * (α ^ 2 ^ (3 * r % n) * β ^ 2 ^ (r % n))) ∨
    ((r : ZMod n) = 2 * (s : ZMod n) ∧ 5 * (s : ZMod n) = 0 ∧
      ∃ c0 : GaloisField 2 n, c0 ≠ 0 ∧
        ∀ α β : GaloisField 2 n,
          M α β = c0 * (α ^ 2 ^ (s % n) * β ^ 2 ^ (3 * s % n))) := by
  obtain ⟨c, hc, hsupp, iw, jw, hw⟩ :=
    exists_equivariant_frobenius_repr (by omega) M lam mu nu hequiv hM0
  -- the two parameter branches are mutually exclusive
  have hexcl : ¬(((s : ZMod n) = 2 * (r : ZMod n) ∧ 5 * (r : ZMod n) = 0) ∧
      ((r : ZMod n) = 2 * (s : ZMod n) ∧ 5 * (s : ZMod n) = 0)) := by
    rintro ⟨⟨h1, h2⟩, ⟨h3, -⟩⟩
    apply hr
    have h3r : (3 : ZMod n) * (r : ZMod n) = 0 := by
      linear_combination -h3 - 2 * h1
    linear_combination 2 * h2 - 3 * h3r
  rcases higman_typeD_support_pinning hn hr hs hrs hrs' hord hlam hmu
      (hsupp iw jw hw) with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -⟩
  · -- branch `s ≡ 2r`, `5r ≡ 0`
    have hi0lt : 3 * r % n < n := Nat.mod_lt _ hn
    have hj0lt : r % n < n := Nat.mod_lt _ hn
    have hpin : ∀ i j : Fin n, c i j ≠ 0 →
        i = (⟨3 * r % n, hi0lt⟩ : Fin n) ∧ j = (⟨r % n, hj0lt⟩ : Fin n) := by
      intro i j hcne
      rcases higman_typeD_support_pinning hn hr hs hrs hrs' hord hlam hmu
          (hsupp i j hcne) with ⟨-, -, hi', hj'⟩ | ⟨h3, h4, -, -⟩
      · constructor
        · refine Fin.ext ?_
          refine fin_val_eq_of_zmod_eq (a := 3 * r) ?_
          push_cast
          exact hi'
        · refine Fin.ext ?_
          refine fin_val_eq_of_zmod_eq (a := r) ?_
          push_cast
          exact hj'
      · exact absurd ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ hexcl
    refine Or.inl ⟨h1, h2, c ⟨3 * r % n, hi0lt⟩ ⟨r % n, hj0lt⟩, ?_,
      fun α β => ?_⟩
    · obtain ⟨hie, hje⟩ := hpin iw jw hw
      have hce : c (⟨3 * r % n, hi0lt⟩ : Fin n) (⟨r % n, hj0lt⟩ : Fin n)
          = c iw jw := by
        rw [hie, hje]
      rw [hce]
      exact hw
    · rw [hc α β, frobenius_double_sum_single c hpin α β]
  · -- mirror branch `r ≡ 2s`, `5s ≡ 0`
    have hi0lt : s % n < n := Nat.mod_lt _ hn
    have hj0lt : 3 * s % n < n := Nat.mod_lt _ hn
    have hpin : ∀ i j : Fin n, c i j ≠ 0 →
        i = (⟨s % n, hi0lt⟩ : Fin n) ∧ j = (⟨3 * s % n, hj0lt⟩ : Fin n) := by
      intro i j hcne
      rcases higman_typeD_support_pinning hn hr hs hrs hrs' hord hlam hmu
          (hsupp i j hcne) with ⟨h3, h4, -, -⟩ | ⟨-, -, hi', hj'⟩
      · exact absurd ⟨⟨h3, h4⟩, ⟨h1, h2⟩⟩ hexcl
      · constructor
        · refine Fin.ext ?_
          refine fin_val_eq_of_zmod_eq (a := s) ?_
          push_cast
          exact hi'
        · refine Fin.ext ?_
          refine fin_val_eq_of_zmod_eq (a := 3 * s) ?_
          push_cast
          exact hj'
    refine Or.inr ⟨h1, h2, c ⟨s % n, hi0lt⟩ ⟨3 * s % n, hj0lt⟩, ?_,
      fun α β => ?_⟩
    · obtain ⟨hie, hje⟩ := hpin iw jw hw
      have hce : c (⟨s % n, hi0lt⟩ : Fin n) (⟨3 * s % n, hj0lt⟩ : Fin n)
          = c iw jw := by
        rw [hie, hje]
      rw [hce]
      exact hw
    · rw [hc α β, frobenius_double_sum_single c hpin α β]

/-! ### Higman p. 91: the type-B shear normalization -/

/-- **Higman p. 91, the shear `y₀ ↦ ρx₀ + y₀` and rescaling.**  Suppose the
ambient square form decomposes as
`Q(α, β) = α·θ(α) + β·θ(β) + c₁·α·θ(β) + c₂·θ(α)·β` over a finite field of
characteristic two, with `θ` of odd order, and `Q` vanishes only at the
origin (all involutions lie in `Φ(G)`).  Then the change of coordinates
`(α, β) ↦ (α + ρβ, tβ)` brings `Q` to the type-B normal form
`α·θ(α) + ε·α·θ(β) + β·θ(β)` with `ε ≠ 0` satisfying Higman's anisotropy
condition.  In characteristic two the shear with `ρ₀ = c₂` kills the
`θ(α)·β` monomial outright, the new `β`-square coefficient is `1 + c₁c₂`,
which is nonzero since otherwise "`ξ = 0` when `a = ρ`, so that `G` is not
a Suzuki 2-group" (p. 91), and the odd-order twisted norm `t·θ(t)` absorbs
it into the coordinate. -/
theorem exists_typeB_shear_normalization
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (theta : RingAut F) (htheta : Odd (orderOf theta))
    (c1 c2 : F) (Q : F → F → F)
    (hQ : ∀ α β, Q α β = α * theta α + β * theta β +
      (c1 * (α * theta β) + c2 * (theta α * β)))
    (haniso : ∀ α β, ¬(α = 0 ∧ β = 0) → Q α β ≠ 0) :
    ∃ ρ t ε : F, t ≠ 0 ∧ ε ≠ 0 ∧
      OddOrder.Peterfalvi.Appendices.Suzuki2Groups.IsTypeBEpsilon theta ε ∧
      ∀ α β, Q (α + ρ * β) (t * β) =
        α * theta α + ε * (α * theta β) + β * theta β := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  -- the sheared form: `Q (α + c₂β) β = αθα + (c₁ + θc₂)·αθβ + (1 + c₁c₂)·βθβ`
  have hshear : ∀ α β, Q (α + c2 * β) β =
      α * theta α + (c1 + theta c2) * (α * theta β) +
        (1 + c1 * c2) * (β * theta β) := by
    intro α β
    rw [hQ, map_add, map_mul]
    linear_combination (c2 * β * theta α + c2 * theta c2 * (β * theta β)) * h2
  -- the new `β`-square coefficient is nonzero: else `Q(c₂, 1) = 0`
  have hd : 1 + c1 * c2 ≠ 0 := by
    intro h0
    refine haniso (0 + c2 * 1) 1 (fun hc => one_ne_zero hc.2) ?_
    rw [hshear, h0]
    simp
  -- the surviving mixed coefficient is nonzero: else the twisted norm
  -- produces an isotropic vector `(u + c₂, 1)`
  have hc' : c1 + theta c2 ≠ 0 := by
    intro h0
    obtain ⟨u, -, hu⟩ := exists_ne_zero_mul_apply_eq_of_typeA theta htheta
      (1 + c1 * c2) hd
    refine haniso (u + c2 * 1) 1 (fun hc => one_ne_zero hc.2) ?_
    rw [hshear, h0, map_one]
    linear_combination hu + (1 + c1 * c2) * h2
  -- rescale `β` by the twisted-norm preimage of `(1 + c₁c₂)⁻¹`
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_mul_apply_eq_of_typeA theta htheta
    (1 + c1 * c2)⁻¹ (inv_ne_zero hd)
  have hθt : theta t ≠ 0 := fun h =>
    ht0 (theta.injective (h.trans (map_zero theta).symm))
  have hkey : (1 + c1 * c2) * (t * theta t) = 1 := by
    rw [ht]
    exact mul_inv_cancel₀ hd
  have hfinal : ∀ α β, Q (α + c2 * t * β) (t * β) =
      α * theta α + (c1 + theta c2) * theta t * (α * theta β) +
        β * theta β := by
    intro α β
    rw [mul_assoc c2 t β, hshear, map_mul]
    linear_combination (β * theta β) * hkey
  refine ⟨c2 * t, t, (c1 + theta c2) * theta t, ht0,
    mul_ne_zero hc' hθt, ?_, hfinal⟩
  intro a b ha hb
  rw [← hfinal a b]
  exact haniso _ _ (fun hc => mul_ne_zero ht0 hb hc.2)

/-- **The shear-and-rescale change of coordinates `(α, β) ↦ (α + ρβ, tβ)`**
as a `ZMod 2`-linear equivalence of `F × F`; in characteristic two it is its
own shear-inverse (up to the `t`-rescale).  Composed with the ambient product
coordinate, it realises Higman's replacement of `y₀` by a multiple of
`ρx₀ + y₀` (p. 91). -/
def shearRescaleLinearEquiv {n : ℕ} (ρ t : GaloisField 2 n) (ht : t ≠ 0) :
    (GaloisField 2 n × GaloisField 2 n) ≃ₗ[ZMod 2]
      (GaloisField 2 n × GaloisField 2 n) where
  toFun w := (w.1 + ρ * w.2, t * w.2)
  invFun w := (w.1 + ρ * t⁻¹ * w.2, t⁻¹ * w.2)
  map_add' w₁ w₂ := by
    apply Prod.ext <;> simp <;> ring
  map_smul' σ w := by
    apply Prod.ext <;> simp [smul_add, Algebra.mul_smul_comm]
  left_inv w := by
    have h2 : (2 : GaloisField 2 n) = 0 := CharTwo.two_eq_zero
    have hti : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
    apply Prod.ext
    · show w.1 + ρ * w.2 + ρ * t⁻¹ * (t * w.2) = w.1
      linear_combination (ρ * w.2) * hti + (ρ * w.2) * h2
    · show t⁻¹ * (t * w.2) = w.2
      rw [← mul_assoc, hti, one_mul]
  right_inv w := by
    have h2 : (2 : GaloisField 2 n) = 0 := CharTwo.two_eq_zero
    have hit : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    apply Prod.ext
    · show w.1 + ρ * t⁻¹ * w.2 + ρ * (t⁻¹ * w.2) = w.1
      linear_combination (ρ * t⁻¹ * w.2) * h2
    · show t * (t⁻¹ * w.2) = w.2
      rw [← mul_assoc, hit, one_mul]

@[simp]
theorem shearRescaleLinearEquiv_apply {n : ℕ} (ρ t : GaloisField 2 n)
    (ht : t ≠ 0) (w : GaloisField 2 n × GaloisField 2 n) :
    shearRescaleLinearEquiv ρ t ht w = (w.1 + ρ * w.2, t * w.2) :=
  rfl

/-! ### Higman pp. 91--92: the type-C and type-D `ε` conditions -/

/-- **Higman p. 90, the type-B `ε` (single-monomial case).**  Anisotropy of
the decomposed square form with the diagonal mixed monomial `c₀ · α · φ(β)`
is exactly Peterfalvi's condition on `ε = c₀` — only the order of the three
summands differs. -/
theorem isTypeBEpsilon_of_decomposed_aniso {n : ℕ}
    (phi : RingAut (GaloisField 2 n)) (c0 : GaloisField 2 n)
    (haniso : ∀ a b : GaloisField 2 n, a ≠ 0 → b ≠ 0 →
      a * phi a + b * phi b + c0 * (a * phi b) ≠ 0) :
    OddOrder.Peterfalvi.Appendices.Suzuki2Groups.IsTypeBEpsilon phi c0 := by
  intro a b ha hb h0
  exact haniso a b ha hb (by linear_combination h0)

/-- **Higman p. 91, the type-C `ε`.**  Over `GaloisField 2 n` with
`θ = Frob^r` and `2r + 1 = n`, anisotropy of the decomposed square form with
the type-C monomial mixed term is exactly Higman's condition on `ε = c₀`:
the monomial exponents `2^{n-1}`, `2^{r+1}` are the Frobenius powers
`Frob⁻¹` and `Frob·θ` of the type-C pairing. -/
theorem isTypeCEpsilon_of_decomposed_aniso {n r : ℕ}
    (h2r1 : 2 * r + 1 = n)
    (theta : RingAut (GaloisField 2 n))
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (c0 : GaloisField 2 n)
    (haniso : ∀ a b : GaloisField 2 n, a ≠ 0 → b ≠ 0 →
      a * theta a + b * b + c0 * (a ^ 2 ^ (n - 1) * b ^ 2 ^ (r + 1)) ≠ 0) :
    IsTypeCEpsilon theta c0 := by
  have hn : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn
  have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard
  have hfrobn : (frobeniusEquiv (GaloisField 2 n) 2) ^ n = 1 := by
    calc (frobeniusEquiv (GaloisField 2 n) 2) ^ n
        = (frobeniusEquiv (GaloisField 2 n) 2)
            ^ orderOf (frobeniusEquiv (GaloisField 2 n) 2) := by rw [horder]
      _ = 1 := pow_orderOf_eq_one _
  have hinv : (frobeniusEquiv (GaloisField 2 n) 2)⁻¹ =
      (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', show n - 1 + 1 = n from by omega]
    exact hfrobn
  intro a b ha hb
  have hinvapply : (frobeniusEquiv (GaloisField 2 n) 2)⁻¹ a =
      a ^ 2 ^ (n - 1) := by
    rw [hinv, frobeniusEquiv_pow_apply]
  have happly : (frobeniusEquiv (GaloisField 2 n) 2 * theta) b =
      b ^ 2 ^ (r + 1) := by
    rw [htheta, ← pow_succ', frobeniusEquiv_pow_apply]
  have hrw : a * theta a +
      c0 * ((frobeniusEquiv (GaloisField 2 n) 2)⁻¹ a *
        (frobeniusEquiv (GaloisField 2 n) 2 * theta) b) + b * b =
      a * theta a + b * b + c0 * (a ^ 2 ^ (n - 1) * b ^ 2 ^ (r + 1)) := by
    rw [hinvapply, happly]
    ring
  rw [hrw]
  exact haniso a b ha hb

/-- **Higman p. 92, the type-D `ε`.**  Over `GaloisField 2 n` with
`θ = Frob^r` (`r < n`), anisotropy of the decomposed square form with the
type-D monomial mixed term is exactly Higman's condition on `ε = c₀`: the
monomial exponents `2^{3r mod n}`, `2^{r mod n}` are the Frobenius powers
`θ³` and `θ` of the type-D pairing. -/
theorem isTypeDEpsilon_of_decomposed_aniso {n r : ℕ}
    (hn : n ≠ 0) (hrn : r < n)
    (theta : RingAut (GaloisField 2 n))
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (c0 : GaloisField 2 n)
    (haniso : ∀ a b : GaloisField 2 n, a ≠ 0 → b ≠ 0 →
      a * theta a + b * (theta ^ 2) b +
        c0 * (a ^ 2 ^ (3 * r % n) * b ^ 2 ^ (r % n)) ≠ 0) :
    IsTypeDEpsilon theta c0 := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn
  have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard
  have hfrobn : (frobeniusEquiv (GaloisField 2 n) 2) ^ n = 1 := by
    calc (frobeniusEquiv (GaloisField 2 n) 2) ^ n
        = (frobeniusEquiv (GaloisField 2 n) 2)
            ^ orderOf (frobeniusEquiv (GaloisField 2 n) 2) := by rw [horder]
      _ = 1 := pow_orderOf_eq_one _
  have hpow3 : theta ^ 3 = frobeniusEquiv (GaloisField 2 n) 2 ^ (3 * r % n) := by
    rw [htheta, ← pow_mul, Nat.mul_comm r 3,
      show 3 * r = n * (3 * r / n) + 3 * r % n from
        (Nat.div_add_mod (3 * r) n).symm,
      pow_add, pow_mul, hfrobn, one_pow, one_mul, Nat.div_add_mod]
  intro a b ha hb
  have h3 : (theta ^ 3) a = a ^ 2 ^ (3 * r % n) := by
    rw [hpow3, frobeniusEquiv_pow_apply]
  have h1 : theta b = b ^ 2 ^ (r % n) := by
    rw [htheta, frobeniusEquiv_pow_apply, Nat.mod_eq_of_lt hrn]
  have hrw : a * theta a + c0 * ((theta ^ 3) a * theta b) +
      b * (theta ^ 2) b =
      a * theta a + b * (theta ^ 2) b +
        c0 * (a ^ 2 ^ (3 * r % n) * b ^ 2 ^ (r % n)) := by
    rw [h3, h1]
    ring
  rw [hrw]
  exact haniso a b ha hb

end

end OddOrder.Higman.Suzuki2Groups
