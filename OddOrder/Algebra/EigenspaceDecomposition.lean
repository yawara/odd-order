/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.DirectSum.LinearMap
import OddOrder.Algebra.LagrangeInterpolationRing
import OddOrder.Algebra.ValuationRingFreeModule

/-!
# Diagonalisability from a split squarefree annihilating polynomial

An endomorphism `A` of a vector space over a field `F` is diagonalisable as soon as it is
annihilated by a polynomial that splits into *distinct* linear factors over `F`:

`aeval A (∏ ζ ∈ s, (X - C ζ)) = 0  ⟹  ⨆ ζ ∈ s, A.eigenspace ζ = ⊤`.

The proof is Lagrange interpolation: the basis polynomials `L_ζ` of the node set `s` sum to `1`
(`Lagrange.sum_basis`), so `v = ∑_{ζ ∈ s} L_ζ(A) v`, while `(X - C ζ) * L_ζ` is a constant
multiple of `∏_{η ∈ s} (X - C η)` and therefore kills `V`; hence `L_ζ(A) v` is a `ζ`-eigenvector.
No algebraic closure is needed — mathlib's `Module.End.IsSemisimple.iSup_eigenspace_eq_top`
assumes `IsAlgClosed`, which is exactly what one cannot have in modular representation theory,
where the coefficient field is a finite field chosen just large enough.

The application is `p`-regular elements in characteristic `p`: an element of order `m` prime to
`p` acts with `A ^ m = 1`, and over a field containing a primitive `m`-th root of unity
`X ^ m - 1` is precisely such a split squarefree annihilator (`iSup_eigenspace_eq_top_of_pow`).
That is what makes Brauer characters well defined.

## Main results

* `OddOrder.iSup_eigenspace_eq_top_of_separated` — the general statement, over a commutative
  ring whose node set has unit pairwise differences
* `OddOrder.iSup_eigenspace_eq_top_of_aeval_prod_eq_zero` — the field case
* `OddOrder.iSup_eigenspace_eq_top_of_pow` — the finite-order case
* `OddOrder.isInternal_eigenspace_of_pow` — the eigenspace decomposition is a direct sum
* `OddOrder.sum_finrank_eigenspace_of_pow` — the eigenspace dimensions add up to `dim V`
* `OddOrder.finrank_eigenspace_eq_quotient_add` — eigenspace dimensions are additive along an
  invariant subspace, eigenvalue by eigenvalue
* `OddOrder.trace_eq_sum_finrank_smul` — over a valuation ring, the trace is the sum of the
  eigenvalues weighted by the ranks of the eigen-submodules
-/

namespace OddOrder

open Polynomial Module.End

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-! ### The general statement, over any commutative ring with separated nodes -/

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open scoped Classical in
/-- **Diagonalisability from a split squarefree annihilator, over a commutative ring.**  If `A`
is killed by `∏_{ζ ∈ s} (X - ζ)` for a finite set `s` of scalars whose pairwise differences are
units, then `M` is spanned by the eigen-submodules of `A` at the members of `s`.

The node set that matters in modular representation theory is `μ_n(𝒪)` inside the coefficient
ring of a `p`-modular system: it is separated because distinct roots of unity have distinct
residues, even though `𝒪` is not a field. -/
theorem iSup_eigenspace_eq_top_of_separated {A : Module.End R M} {s : Finset R}
    (hs : SeparatedNodes s) (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) :
    ⨆ ζ ∈ s, A.eigenspace ζ = ⊤ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · -- The empty product is `1`, so `A` lives on the zero module and every submodule is `⊤`.
    simp only [Finset.prod_empty, map_one] at hA
    have hsub : Subsingleton M := by
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : M, z = 0 := fun z => by
        simpa using congrArg (fun T : Module.End R M => T z) hA
      rw [hx x, hx y]
    exact Subsingleton.elim _ _
  refine eq_top_iff.mpr fun v _ => ?_
  -- `∑_{ζ ∈ s} L_ζ = 1`, so `v` is the sum of the vectors `L_ζ(A) v`.
  have hv : v = ∑ ζ ∈ s, (aeval A (ringLagrangeBasis s ζ)) v := by
    have h := congrArg (fun q : R[X] => (aeval A q) v) (sum_ringLagrangeBasis hs hne)
    simpa [map_sum, LinearMap.sum_apply] using h.symm
  -- Each summand is a `ζ`-eigenvector, because `(X - ζ) · L_ζ` is a multiple of the annihilator.
  have hmem : ∀ ζ ∈ s, (aeval A (ringLagrangeBasis s ζ)) v ∈ ⨆ ζ ∈ s, A.eigenspace ζ := by
    intro ζ hζ
    refine Submodule.mem_iSup_of_mem ζ (Submodule.mem_iSup_of_mem hζ ?_)
    rw [mem_eigenspace_iff]
    have hkill : aeval A ((X - C ζ) * ringLagrangeBasis s ζ) = 0 := by
      rw [X_sub_C_mul_ringLagrangeBasis hζ, map_mul, hA, mul_zero]
    rw [map_mul, map_sub, aeval_X, aeval_C] at hkill
    have happ := congrArg (fun T : Module.End R M => T v) hkill
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      Module.algebraMap_end_apply] at happ
    exact sub_eq_zero.mp happ
  rw [hv]
  exact Submodule.sum_mem _ hmem

end CommRing

/-- Over a field every finite set of nodes is separated. -/
theorem separatedNodes_of_field (s : Finset F) : SeparatedNodes s :=
  fun _ _ _ _ hne => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)

/-- **Diagonalisability from a split squarefree annihilator** over a field: the special case of
`iSup_eigenspace_eq_top_of_separated` in which separatedness is automatic. -/
theorem iSup_eigenspace_eq_top_of_aeval_prod_eq_zero {A : Module.End F V} {s : Finset F}
    (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) :
    ⨆ ζ ∈ s, A.eigenspace ζ = ⊤ :=
  iSup_eigenspace_eq_top_of_separated (separatedNodes_of_field s) hA

/-- **The finite-order case.**  If `A ^ m = 1` and the base field contains a primitive `m`-th
root of unity, then `V` is spanned by the eigenspaces of `A` at the `m`-th roots of unity. -/
theorem iSup_eigenspace_eq_top_of_pow {A : Module.End F V} {m : ℕ} (hm : 0 < m)
    {ω : F} (hω : IsPrimitiveRoot ω m) (hA : A ^ m = 1) :
    ⨆ ζ ∈ nthRootsFinset m (1 : F), A.eigenspace ζ = ⊤ := by
  refine iSup_eigenspace_eq_top_of_aeval_prod_eq_zero ?_
  rw [← X_pow_sub_one_eq_prod hm hω]
  simp [hA]

/-- Over any field the eigenspaces of an endomorphism are independent, so the decomposition of
`iSup_eigenspace_eq_top_of_pow` is an internal direct sum. -/
theorem isInternal_eigenspace_of_pow [DecidableEq F] {A : Module.End F V} {m : ℕ} (hm : 0 < m)
    {ω : F} (hω : IsPrimitiveRoot ω m) (hA : A ^ m = 1) :
    DirectSum.IsInternal fun ζ : nthRootsFinset m (1 : F) => A.eigenspace (ζ : F) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨A.eigenspaces_iSupIndep.comp Subtype.val_injective, eq_top_iff.mpr ?_⟩
  rw [← iSup_eigenspace_eq_top_of_pow hm hω hA]
  exact iSup₂_le fun ζ hζ =>
    le_iSup (fun ζ : nthRootsFinset m (1 : F) => A.eigenspace (ζ : F)) ⟨ζ, hζ⟩

/-- **The eigenspace dimensions add up.**  This is the counting form of
`isInternal_eigenspace_of_pow`, and it is what makes a Brauer character take the value `dim V`
at the identity and reduce to the ordinary trace modulo the maximal ideal. -/
theorem sum_finrank_eigenspace_of_pow [FiniteDimensional F V]
    {A : Module.End F V} {m : ℕ} (hm : 0 < m) {ω : F} (hω : IsPrimitiveRoot ω m)
    (hA : A ^ m = 1) :
    ∑ ζ ∈ nthRootsFinset m (1 : F), Module.finrank F (A.eigenspace ζ) = Module.finrank F V := by
  classical
  have hint := isInternal_eigenspace_of_pow hm hω hA
  have he := LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun ζ : nthRootsFinset m (1 : F) => A.eigenspace (ζ : F))) hint
  rw [← he.finrank_eq, Module.finrank_directSum, Finset.univ_eq_attach]
  exact (Finset.sum_attach (nthRootsFinset m (1 : F))
    (fun ζ => Module.finrank F (A.eigenspace ζ))).symm

/-! ### Ranks and the trace, over a domain

Over a valuation ring — the case of interest is the coefficient ring `𝒪` of a `p`-modular
system — the eigen-summands of a finite module are again finite free, so the decomposition can be
read off in ranks and in the trace.  This is the `𝒪`-side of the comparison that defines the
decomposition matrix.  Valuation rings rather than principal ideal domains, because the splitting
system `𝓞_ℂ_[p]` has divisible value group; the freeness comes from local + Bézout instead of
from a PID structure theorem.
-/

section Domain

variable {R M : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]

/-- The eigen-decomposition of `iSup_eigenspace_eq_top_of_separated` is an internal direct
sum. -/
theorem isInternal_eigenspace_of_separated [DecidableEq R] {A : Module.End R M} {s : Finset R}
    (hs : SeparatedNodes s) (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) :
    DirectSum.IsInternal fun ζ : s => A.eigenspace (ζ : R) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨A.eigenspaces_iSupIndep.comp Subtype.val_injective, eq_top_iff.mpr ?_⟩
  rw [← iSup_eigenspace_eq_top_of_separated hs hA]
  exact iSup₂_le fun ζ hζ => le_iSup (fun ζ : s => A.eigenspace (ζ : R)) ⟨ζ, hζ⟩

variable [ValuationRing R] [Module.Finite R M]

omit [ValuationRing R] in
/-- **Each eigen-summand is finitely generated.**  It is a retract of `M`: the internal direct sum
identifies `M` with `⨁_ζ M_ζ`, and the coordinate projection onto `M_ζ` is surjective. -/
theorem finite_eigenspace_of_separated {A : Module.End R M} {s : Finset R}
    (hs : SeparatedNodes s) (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) (ζ : s) :
    Module.Finite R (A.eigenspace (ζ : R)) := by
  classical
  have he := LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun ζ : s => A.eigenspace (ζ : R))) (isInternal_eigenspace_of_separated hs hA)
  have := Module.Finite.equiv he.symm
  exact Module.Finite.of_surjective
    (DirectSum.component R s (fun ζ : s => A.eigenspace (ζ : R)) ζ) fun x =>
    ⟨DirectSum.lof R s (fun ζ : s => A.eigenspace (ζ : R)) ζ x, by simp⟩

/-- **Each eigen-summand is free.**  It is finitely generated by
`finite_eigenspace_of_separated` and torsion-free as a submodule of `M`; over a valuation ring —
which is Bézout, so torsion-free means flat, and local, so finite flat means free — that is
enough.  This replaces the classical appeal to "submodules of free modules over a PID are free",
which is unavailable for the splitting `p`-modular system `𝓞_ℂ_[p]`: its value group is divisible,
so it is not Noetherian. -/
theorem free_eigenspace_of_separated {A : Module.End R M} {s : Finset R}
    (hs : SeparatedNodes s) (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) (ζ : s) :
    Module.Free R (A.eigenspace (ζ : R)) := by
  have := finite_eigenspace_of_separated hs hA ζ
  exact free_of_isTorsionFree

/-- The ranks of the eigen-submodules add up to the rank of the module. -/
theorem sum_finrank_eigenspace_of_separated {A : Module.End R M} {s : Finset R}
    (hs : SeparatedNodes s) (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) :
    ∑ ζ ∈ s, Module.finrank R (A.eigenspace ζ) = Module.finrank R M := by
  classical
  have := fun ζ : s => finite_eigenspace_of_separated hs hA ζ
  have := fun ζ : s => free_eigenspace_of_separated hs hA ζ
  have he := LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun ζ : s => A.eigenspace (ζ : R))) (isInternal_eigenspace_of_separated hs hA)
  rw [← he.finrank_eq, Module.finrank_directSum, Finset.univ_eq_attach]
  exact (Finset.sum_attach s (fun ζ => Module.finrank R (A.eigenspace ζ))).symm

set_option backward.isDefEq.respectTransparency false in
/-- **The trace is the sum of the eigenvalues weighted by the ranks of the eigen-submodules.**
Over the coefficient ring of a `p`-modular system this is the statement that the trace of a
lattice endomorphism of order prime to `p` is literally the Brauer-character expression. -/
theorem trace_eq_sum_finrank_smul [Module.Free R M] {A : Module.End R M} {s : Finset R}
    (hs : SeparatedNodes s) (hA : aeval A (∏ η ∈ s, (X - C η)) = 0) :
    LinearMap.trace R M A = ∑ ζ ∈ s, Module.finrank R (A.eigenspace ζ) • ζ := by
  classical
  have := fun ζ : s => finite_eigenspace_of_separated hs hA ζ
  have := fun ζ : s => free_eigenspace_of_separated hs hA ζ
  have hmaps : ∀ ζ : s, Set.MapsTo A (A.eigenspace (ζ : R)) (A.eigenspace (ζ : R)) := by
    intro ζ v hv
    rw [SetLike.mem_coe, mem_eigenspace_iff] at hv ⊢
    rw [hv, map_smul, hv]
  have hrestrict : ∀ ζ : s, LinearMap.trace R _ (A.restrict (hmaps ζ))
      = Module.finrank R (A.eigenspace (ζ : R)) • (ζ : R) := by
    intro ζ
    have hid : A.restrict (hmaps ζ) = (ζ : R) • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      have hv := v.2
      rw [mem_eigenspace_iff] at hv
      simpa [LinearMap.restrict_apply] using hv
    rw [hid, map_smul, LinearMap.trace_id, smul_eq_mul, nsmul_eq_mul]
    exact mul_comm _ _
  rw [LinearMap.trace_eq_sum_trace_restrict (isInternal_eigenspace_of_separated hs hA) hmaps]
  simp only [hrestrict, Finset.univ_eq_attach]
  exact Finset.sum_attach s (fun ζ => Module.finrank R (A.eigenspace ζ) • ζ)

end Domain


/-! ### Invariant subspaces: the eigenspace dimensions are additive

For a diagonalisable `A` and an `A`-invariant subspace `W`, the eigenspace dimensions of `W`
and of `V ⧸ W` add up to those of `V` — *for each eigenvalue separately*.  The proof avoids
constructing the spectral projections: the obvious inequality holds for each `ζ`, and the three
total-dimension identities force all of them to be equalities at once.
-/

section Invariant

variable {A : Module.End F V} {W : Submodule F V} (hq : W ≤ W.comap A)
include hq

/-- Powers of a restricted endomorphism are the restrictions of its powers. -/
theorem coe_restrict_pow (m : ℕ) (w : W) :
    (((A.restrict hq) ^ m) w : V) = (A ^ m) (w : V) := by
  induction m generalizing w with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, LinearMap.coe_restrict_apply, pow_succ,
      Module.End.mul_apply]

theorem restrict_pow_eq_one {m : ℕ} (hA : A ^ m = 1) : (A.restrict hq) ^ m = 1 :=
  LinearMap.ext fun w => Subtype.ext (by rw [coe_restrict_pow hq, hA]; rfl)

/-- Powers of the endomorphism induced on the quotient are induced by the powers. -/
theorem mapQ_pow_apply (m : ℕ) (v : V) :
    ((W.mapQ W A hq) ^ m) (W.mkQ v) = W.mkQ ((A ^ m) v) := by
  induction m generalizing v with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      ← Submodule.mkQ_apply, ih, pow_succ, Module.End.mul_apply]

theorem mapQ_pow_eq_one {m : ℕ} (hA : A ^ m = 1) :
    (W.mapQ W A hq) ^ m = 1 := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨v, rfl⟩ := W.mkQ_surjective q
  rw [mapQ_pow_apply hq, hA]
  rfl

/-- The `ζ`-eigenspace of the restriction sits inside `V` as `V_ζ ⊓ W`. -/
theorem map_subtype_eigenspace_restrict (ζ : F) :
    Submodule.map W.subtype (Module.End.eigenspace (A.restrict hq) ζ)
      = Module.End.eigenspace A ζ ⊓ W := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_eigenspace_iff] at hw
    refine ⟨mem_eigenspace_iff.mpr ?_, w.2⟩
    have hcoe := congrArg (fun z : W => (z : V)) hw
    rwa [LinearMap.coe_restrict_apply] at hcoe
  · rintro ⟨hv, hvW⟩
    refine ⟨⟨v, hvW⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_eigenspace_iff]
    exact Subtype.ext (by rw [LinearMap.coe_restrict_apply]; exact mem_eigenspace_iff.mp hv)

theorem finrank_eigenspace_restrict (ζ : F) :
    Module.finrank F (Module.End.eigenspace (A.restrict hq) ζ)
      = Module.finrank F (Module.End.eigenspace A ζ ⊓ W : Submodule F V) := by
  rw [← map_subtype_eigenspace_restrict hq ζ]
  exact (Submodule.equivMapOfInjective _ W.injective_subtype _).finrank_eq

/-- Passing to the quotient can only lose the eigenvectors that already lay in `W`. -/
theorem finrank_eigenspace_le_quotient_add [FiniteDimensional F V] (ζ : F) :
    Module.finrank F (Module.End.eigenspace A ζ)
      ≤ Module.finrank F (Module.End.eigenspace (W.mapQ W A hq) ζ)
        + Module.finrank F (Module.End.eigenspace (A.restrict hq) ζ) := by
  classical
  set Aq := W.mapQ W A hq with hAq
  -- `mkQ` maps the `ζ`-eigenspace of `A` into that of the induced map …
  have hmaps : ∀ v ∈ Module.End.eigenspace A ζ, W.mkQ v ∈ Module.End.eigenspace Aq ζ := by
    intro v hv
    rw [mem_eigenspace_iff] at hv ⊢
    rw [hAq, Submodule.mkQ_apply, Submodule.mapQ_apply, hv]
    rfl
  let f : (Module.End.eigenspace A ζ) →ₗ[F] (Module.End.eigenspace Aq ζ) :=
    LinearMap.restrict W.mkQ hmaps
  -- … and its kernel consists of eigenvectors already in `W`.
  have hkerle : LinearMap.ker f
      ≤ Submodule.comap (Module.End.eigenspace A ζ).subtype
          (Module.End.eigenspace A ζ ⊓ W) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    refine Submodule.mem_comap.mpr ⟨v.2, ?_⟩
    have hz := congrArg (fun z : Module.End.eigenspace Aq ζ => (z : V ⧸ W)) hv
    simp only [f, LinearMap.coe_restrict_apply, Submodule.mkQ_apply,
      ZeroMemClass.coe_zero] at hz
    exact (Submodule.Quotient.mk_eq_zero W).mp hz
  have hkerrank : Module.finrank F (LinearMap.ker f)
      ≤ Module.finrank F (Module.End.eigenspace A ζ ⊓ W : Submodule F V) :=
    le_trans (Submodule.finrank_mono hkerle)
      (le_of_eq (Submodule.comapSubtypeEquivOfLe
        (inf_le_left : Module.End.eigenspace A ζ ⊓ W ≤ Module.End.eigenspace A ζ)).finrank_eq)
  have hle : Module.finrank F (LinearMap.range f)
      ≤ Module.finrank F (Module.End.eigenspace Aq ζ) := Submodule.finrank_le _
  calc Module.finrank F (Module.End.eigenspace A ζ)
      = Module.finrank F (LinearMap.range f) + Module.finrank F (LinearMap.ker f) :=
        (LinearMap.finrank_range_add_finrank_ker f).symm
    _ ≤ Module.finrank F (Module.End.eigenspace Aq ζ)
        + Module.finrank F (Module.End.eigenspace (A.restrict hq) ζ) := by
        rw [finrank_eigenspace_restrict hq ζ]
        exact Nat.add_le_add hle hkerrank

/-- **Eigenspace dimensions are additive in a short exact sequence** of diagonalisable
operators.  Equality for every `ζ` at once follows from the pointwise inequality plus the three
total-dimension counts. -/
theorem finrank_eigenspace_eq_quotient_add [FiniteDimensional F V] {m : ℕ} (hm : 0 < m)
    {ω : F} (hω : IsPrimitiveRoot ω m) (hA : A ^ m = 1) {ζ : F}
    (hζ : ζ ∈ nthRootsFinset m (1 : F)) :
    Module.finrank F (Module.End.eigenspace A ζ)
      = Module.finrank F (Module.End.eigenspace (W.mapQ W A hq) ζ)
        + Module.finrank F (Module.End.eigenspace (A.restrict hq) ζ) := by
  classical
  have hsum : ∑ η ∈ nthRootsFinset m (1 : F),
      Module.finrank F (Module.End.eigenspace A η)
        = ∑ η ∈ nthRootsFinset m (1 : F),
            (Module.finrank F
                (Module.End.eigenspace (W.mapQ W A hq) η)
              + Module.finrank F (Module.End.eigenspace (A.restrict hq) η)) := by
    rw [Finset.sum_add_distrib, sum_finrank_eigenspace_of_pow hm hω hA,
      sum_finrank_eigenspace_of_pow hm hω (mapQ_pow_eq_one hq hA),
      sum_finrank_eigenspace_of_pow hm hω (restrict_pow_eq_one hq hA),
      Submodule.finrank_quotient_add_finrank]
  exact (Finset.sum_eq_sum_iff_of_le
    (fun η _ => finrank_eigenspace_le_quotient_add hq η)).mp hsum ζ hζ

end Invariant

end OddOrder
