/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialMonomial
import OddOrder.GroupTheory.RepresentationTheory.CyclicPermEigenCount

/-!
# Discharging the BG (2.11) keystone for the extraspecial setup

`OddOrder.GroupTheory.RepresentationTheory` shared module: connects the abstract orbit-count
keystone `CyclicPermEigen.finrank_eigenspace_fixed_succ` to the concrete Bender–Glauberman
Theorem 2.5 setup, producing the `dim E₀ = dim E_m + 1` input
(`hEdim` of `sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace` in `ExtraspecialThm25`).

The conjugation `c_x = cyclicEndConj T` acts on the Burnside basis `{ρ(out c)}` as a monomial
permutation (`cyclicEndConj_pow_burnsideBasisOfSection`), with permutation
`σ = quotientCenterCongr φ` of `P/Z`.  The identity coset `⟦1⟧` is the unique `σ`-fixed point
with `c_x(b ⟦1⟧) = b ⟦1⟧`
(its image is central, hence scalar, hence fixed by conjugation); every other `σ`-orbit is free
because `C_{P/Z}(xᵏ) = 1` (the hypothesis `hcent`).  So the abstract keystone applies verbatim.
-/

namespace OddOrder.RepresentationTheory

open Representation Module EigenspaceUnderCyclicAction

/-- A power of a multiplicative automorphism, viewed as a permutation, applies as the group power:
`(e.toEquiv ^ k) c = (e ^ k) c`. -/
theorem mulAut_toEquiv_pow_apply {M : Type*} [Group M] (e : MulAut M) (k : ℕ) (c : M) :
    ((e.toEquiv) ^ k) c = (e ^ k) c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
    rfl

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {P : Type*} [Group P] {V : Type*} [AddCommGroup V] [Module F V]

/-- **BG (2.11) keystone, for the extraspecial setup.** In the Theorem 2.5 situation — `ρ` a
faithful irreducible representation of `P` (nilpotency class `≤ 2`) over an algebraically closed
field with `char ∤ |P|`, an intertwiner `T` for an automorphism `φ` of `P` with `φ^h = 1`, `ε` a
primitive `h`-th root, `char ∤ h`, and `C_{P/Z}(xᵏ) = 1` (`hcent`: only the identity coset is fixed
by a nontrivial `σ`-power) — the conjugation eigenspaces satisfy `dim E₀ = dim E_m + 1` for `m ≠ 0`.
This is the `hEdim` input to `sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace`. -/
theorem finrank_cyclicEndConjEigenspaceFin_succ
    [Finite P] [Invertible (Nat.card P : F)] [FiniteDimensional F V]
    (ρ : Representation F P V) [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P)
    (φ : P ≃* P) (T : LinearMap.GeneralLinearGroup F V)
    (hint : ∀ p : P, (T : Module.End F V) * ρ p = ρ (φ p) * (T : Module.End F V))
    {h : ℕ} [NeZero h] (hφh : φ ^ h = 1)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hcent : ∀ k : ZMod h, k ≠ 0 → ∀ c : P ⧸ Subgroup.center P,
        ((quotientCenterCongr φ ^ k.val) c) = c → c = 1) :
    ∀ m : Fin h, m ≠ 0 →
      finrank F (cyclicEndConjEigenspaceFin ε T (0 : Fin h))
        = finrank F (cyclicEndConjEigenspaceFin ε T m) + 1 := by
  intro m hm
  set σ : Equiv.Perm (P ⧸ Subgroup.center P) := (quotientCenterCongr φ).toEquiv with hσdef
  -- σ-powers agree with the multiplicative-automorphism powers
  have hbridge : ∀ (k : ℕ) (c : P ⧸ Subgroup.center P), (σ ^ k) c = (quotientCenterCongr φ ^ k) c :=
    fun k c => mulAut_toEquiv_pow_apply (quotientCenterCongr φ) k c
  -- monomial action of the conjugation on the Burnside basis
  have hmon : ∀ (k : ℕ) (c : P ⧸ Subgroup.center P),
      ∃ a : F, ((cyclicEndConj T) ^ k) (burnsideBasis ρ hf hcl c)
        = a • burnsideBasis ρ hf hcl ((σ ^ k) c) := by
    intro k c
    obtain ⟨a, ha⟩ := cyclicEndConj_pow_burnsideBasisOfSection ρ hf hcl φ T hint
      Quotient.out (fun c => Quotient.out_eq' c) k c
    exact ⟨a, by rw [hbridge]; exact ha⟩
  -- `c_x^h = 1`
  have hTh : (cyclicEndConj T) ^ h = 1 := cyclicEndConj_pow_eq_one ρ φ T hint hφh
  -- `σ^h = 1`
  have hσh : σ ^ h = 1 := by
    ext c
    induction c using QuotientGroup.induction_on with
    | _ g => rw [hbridge, quotientCenterCongr_pow_mk, hφh]; rfl
  -- the identity coset is `σ`-fixed and its basis vector is conjugation-fixed (it is central)
  have hfixσ : σ (1 : P ⧸ Subgroup.center P) = 1 := by
    rw [hσdef]; exact map_one (quotientCenterCongr φ)
  have hc₀ : cyclicEndConj T (burnsideBasis ρ hf hcl 1) = burnsideBasis ρ hf hcl 1 := by
    have hmem : Quotient.out (1 : P ⧸ Subgroup.center P) ∈ Subgroup.center P := by
      have h1 : ((Quotient.out (1 : P ⧸ Subgroup.center P) : P) : P ⧸ Subgroup.center P) = 1 :=
        Quotient.out_eq' (1 : P ⧸ Subgroup.center P)
      rwa [QuotientGroup.eq_one_iff] at h1
    obtain ⟨s, hs⟩ := center_isScalar ρ hmem
    rw [burnsideBasis_apply, hs, map_smul]
    congr 1
    ext v
    rw [cyclicEndConj_apply]
    simp only [LinearMap.id_coe, id_eq]
    exact T.toLinearEquiv.apply_symm_apply v
  -- every other orbit is free
  have hfree : ∀ c : P ⧸ Subgroup.center P, c ≠ 1 → ∀ k : ZMod h, (σ ^ k.val) c = c → k = 0 := by
    intro c hc k hk
    by_contra hk0
    exact hc (hcent k hk0 c (by rw [← hbridge k.val c]; exact hk))
  -- `ε^m ≠ 1`
  have hmne : ε ^ (m : ℕ) ≠ 1 := fun hone => by
    have hdvd : h ∣ (m : ℕ) := (hprim.pow_eq_one_iff_dvd _).mp hone
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h0 => hm (Fin.ext h0))) hdvd
    omega
  exact CyclicPermEigen.finrank_eigenspace_fixed_succ (burnsideBasis ρ hf hcl) (cyclicEndConj T) σ
    hmon hσh hTh hprim hh hc₀ hfixσ hfree hmne

end OddOrder.RepresentationTheory
