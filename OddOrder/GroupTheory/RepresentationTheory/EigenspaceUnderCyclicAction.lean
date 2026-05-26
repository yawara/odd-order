/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Eigenspaces under a Cyclic Action

`OddOrder.GroupTheory` shared module for Bender-Glauberman, Chapter I,
Proposition 2.4.

The proposition fixes an invertible linear transformation `g` of finite order
`h`, a primitive `h`-th root of unity `epsilon`, and writes
`V_i = {v | v * g = epsilon^i v}` and `n_i = dim V_i`.

This file starts the Lean package for that notation.  The first facts are the
periodicity facts and the first endomorphism-block definitions needed before
the direct-sum and block-matrix parts of Prop 2.4 can be stated cleanly.
-/

namespace OddOrder
namespace RepresentationTheory
namespace EigenspaceUnderCyclicAction

open Polynomial
open scoped Function

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private abbrev glInvEnd (g : LinearMap.GeneralLinearGroup F V) :
    Module.End F V :=
  g.toLinearEquiv.symm

/-- BG Prop 2.4 notation `V_i`: the `epsilon^i` eigenspace of `g`.

BG writes the action on the right (`v g = epsilon^i v`).  In Lean this is the
left action of the endomorphism `g`, so the condition is `g v = epsilon^i • v`.
-/
abbrev cyclicEigenspace (epsilon : F) (g : Module.End F V) (i : ℕ) :
    Submodule F V :=
  g.eigenspace (epsilon ^ i)

/-- BG Prop 2.4 notation `n_i = dim V_i`. -/
noncomputable abbrev cyclicEigenspaceDim (epsilon : F) (g : Module.End F V)
    (i : ℕ) : ℕ :=
  Module.finrank F (cyclicEigenspace epsilon g i)

/-- Fin-indexed version of `cyclicEigenspace`, for the sum over
`0 ≤ i ≤ h - 1` in BG Prop 2.4(a). -/
abbrev cyclicEigenspaceFin (epsilon : F) (g : Module.End F V) {h : ℕ}
    (i : Fin h) : Submodule F V :=
  cyclicEigenspace epsilon g i.1

/-- Fin-indexed version of `cyclicEigenspaceDim`. -/
noncomputable abbrev cyclicEigenspaceFinDim (epsilon : F) (g : Module.End F V)
    {h : ℕ} (i : Fin h) : ℕ :=
  cyclicEigenspaceDim epsilon g i.1

@[simp]
theorem mem_cyclicEigenspace_iff {epsilon : F} {g : Module.End F V}
    {i : ℕ} {v : V} :
    v ∈ cyclicEigenspace epsilon g i ↔ g v = (epsilon ^ i) • v := by
  simp [cyclicEigenspace]

@[simp]
theorem mem_cyclicEigenspaceFin_iff {epsilon : F} {g : Module.End F V}
    {h : ℕ} {i : Fin h} {v : V} :
    v ∈ cyclicEigenspaceFin epsilon g i ↔ g v = (epsilon ^ i.1) • v := by
  simp [cyclicEigenspaceFin]

/-- If `epsilon^h = 1`, then the BG eigenspaces are periodic with period `h`.

This is Prop 2.4(b)'s structural reason, stated before taking dimensions. -/
theorem cyclicEigenspace_add_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1) (i : ℕ) :
    cyclicEigenspace epsilon g (i + h) = cyclicEigenspace epsilon g i := by
  unfold cyclicEigenspace
  rw [pow_add, hepsilon, mul_one]

/-- Periodicity by any multiple of the period. -/
theorem cyclicEigenspace_add_mul_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1)
    (i k : ℕ) :
    cyclicEigenspace epsilon g (i + k * h) = cyclicEigenspace epsilon g i := by
  unfold cyclicEigenspace
  have hpow : epsilon ^ (k * h) = 1 := by
    rw [Nat.mul_comm, pow_mul, hepsilon, one_pow]
  rw [pow_add, hpow, mul_one]

/-- Primitive-root version of periodicity. -/
theorem cyclicEigenspace_add_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i : ℕ) :
    cyclicEigenspace epsilon g (i + h) = cyclicEigenspace epsilon g i :=
  cyclicEigenspace_add_period_of_pow_eq_one hepsilon.pow_eq_one i

/-- Primitive-root version of periodicity by a multiple of the period. -/
theorem cyclicEigenspace_add_mul_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i k : ℕ) :
    cyclicEigenspace epsilon g (i + k * h) = cyclicEigenspace epsilon g i :=
  cyclicEigenspace_add_mul_period_of_pow_eq_one hepsilon.pow_eq_one i k

/-- Dimension form of BG Prop 2.4(b): `n_{i+h} = n_i`. -/
theorem cyclicEigenspaceDim_add_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1) (i : ℕ) :
    cyclicEigenspaceDim epsilon g (i + h) = cyclicEigenspaceDim epsilon g i := by
  unfold cyclicEigenspaceDim
  rw [cyclicEigenspace_add_period_of_pow_eq_one hepsilon i]

/-- Dimension form of periodicity by any multiple of the period. -/
theorem cyclicEigenspaceDim_add_mul_period_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} (hepsilon : epsilon ^ h = 1) (i k : ℕ) :
    cyclicEigenspaceDim epsilon g (i + k * h) = cyclicEigenspaceDim epsilon g i := by
  unfold cyclicEigenspaceDim
  rw [cyclicEigenspace_add_mul_period_of_pow_eq_one hepsilon i k]

/-- Primitive-root dimension form of BG Prop 2.4(b). -/
theorem cyclicEigenspaceDim_add_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i : ℕ) :
    cyclicEigenspaceDim epsilon g (i + h) = cyclicEigenspaceDim epsilon g i :=
  cyclicEigenspaceDim_add_period_of_pow_eq_one hepsilon.pow_eq_one i

/-- Primitive-root dimension form of periodicity by any multiple of the period. -/
theorem cyclicEigenspaceDim_add_mul_period {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) (i k : ℕ) :
    cyclicEigenspaceDim epsilon g (i + k * h) = cyclicEigenspaceDim epsilon g i :=
  cyclicEigenspaceDim_add_mul_period_of_pow_eq_one hepsilon.pow_eq_one i k

/-! ### Finite eigenspace family -/

/-- The displayed finite family `V_i`, `0 ≤ i < h`, is independent when
`epsilon` is a primitive `h`-th root.

This is the directness part behind BG Prop 2.4(a).  The spanning part is a
separate diagonalization input; here we only use primitive-root injectivity of
the eigenvalues and mathlib's independence theorem for eigenspaces. -/
theorem cyclicEigenspaceFin_iSupIndep {epsilon : F} {g : Module.End F V}
    {h : ℕ} (hepsilon : IsPrimitiveRoot epsilon h) :
    iSupIndep fun i : Fin h => cyclicEigenspaceFin epsilon g i := by
  have hinj : Function.Injective fun i : Fin h => epsilon ^ i.1 := by
    intro i j hij
    exact Fin.ext (hepsilon.pow_inj i.2 j.2 hij)
  simpa [cyclicEigenspaceFin, cyclicEigenspace, Function.comp_def] using
    (g.eigenspaces_iSupIndep.comp hinj)

/-! ### Endomorphism blocks `E_i` and `E_{i,t}` -/

/-- BG Prop 2.4 conjugation action on `E = End_F(V)`.

BG writes vectors and endomorphisms on the right and defines
`e^g = g^{-1} e g`.  Since the rest of this Lean file uses left actions, the
corresponding operator on endomorphisms is `e ↦ g * e * g⁻¹`. -/
def cyclicEndConj (g : LinearMap.GeneralLinearGroup F V) :
    Module.End F (Module.End F V) where
  toFun e := (g : Module.End F V) * e * glInvEnd g
  map_add' e f := by
    ext v
    simp [Module.End.mul_apply, map_add]
  map_smul' a e := by
    ext v
    simp [Module.End.mul_apply]

@[simp]
theorem cyclicEndConj_apply (g : LinearMap.GeneralLinearGroup F V)
    (e : Module.End F V) (v : V) :
    cyclicEndConj g e v = (g : Module.End F V) (e (glInvEnd g v)) := by
  rfl

/-- BG Prop 2.4 notation `E_i`: the `epsilon^i` eigenspace for the
conjugation action on `End_F(V)`. -/
abbrev cyclicEndConjEigenspace (epsilon : F)
    (g : LinearMap.GeneralLinearGroup F V) (i : ℕ) :
    Submodule F (Module.End F V) :=
  cyclicEigenspace epsilon (cyclicEndConj g) i

/-- Fin-indexed version of `cyclicEndConjEigenspace`. -/
abbrev cyclicEndConjEigenspaceFin (epsilon : F)
    (g : LinearMap.GeneralLinearGroup F V) {h : ℕ} (i : Fin h) :
    Submodule F (Module.End F V) :=
  cyclicEndConjEigenspace epsilon g i.1

/-- The displayed finite family `⋃_{0≤i<h} V_i` from BG Prop 2.4. -/
def cyclicEigenspaceFinUnion (epsilon : F) (g : Module.End F V) (h : ℕ) :
    Set V :=
  {v | ∃ i : Fin h, v ∈ cyclicEigenspaceFin epsilon g i}

/-- The set-level span of the displayed finite union is the supremum of the
finite eigenspace family.

Earlier block calculations use `span (⋃ V_i) = ⊤` because they prove equality
of endomorphisms by checking the displayed eigenvectors.  Direct-sum work uses
`⨆ i, V_i = ⊤`.  This lemma keeps those two Prop 2.4(a) inputs aligned. -/
theorem span_cyclicEigenspaceFinUnion_eq_iSup (epsilon : F) (g : Module.End F V)
    (h : ℕ) :
    Submodule.span F (cyclicEigenspaceFinUnion epsilon g h) =
      ⨆ i : Fin h, cyclicEigenspaceFin epsilon g i := by
  rw [Submodule.iSup_eq_span]
  congr 1
  ext v
  simp [cyclicEigenspaceFinUnion]

/-- Top-span form and `iSup` form of BG Prop 2.4(a)'s spanning input are
equivalent. -/
theorem span_cyclicEigenspaceFinUnion_eq_top_iff (epsilon : F) (g : Module.End F V)
    (h : ℕ) :
    Submodule.span F (cyclicEigenspaceFinUnion epsilon g h) = ⊤ ↔
      (⨆ i : Fin h, cyclicEigenspaceFin epsilon g i) = ⊤ := by
  rw [span_cyclicEigenspaceFinUnion_eq_iSup]

/-- A finite-order operator has no eigenvalues outside the cyclic group generated
by a primitive root with the same period.

This is the spectrum-classification bridge used in BG Prop 2.4(a): after
diagonalization supplies spanning by all eigenspaces, finite order and the
primitive root restrict the relevant eigenvalues to the displayed finite list
`epsilon^0, ..., epsilon^(h-1)`. -/
theorem eigenvalue_eq_power_of_primitiveRoot_of_pow_eq_one {epsilon : F}
    {g : Module.End F V} {h : ℕ} [NeZero h]
    (hepsilon : IsPrimitiveRoot epsilon h) (hgpow : g ^ h = 1)
    {mu : F} (hmu : g.HasEigenvalue mu) :
    ∃ i : Fin h, mu = epsilon ^ i.1 := by
  rcases hmu.exists_hasEigenvector with ⟨v, hv⟩
  have hpow_apply := hv.pow_apply h
  have hmu_pow_smul : (mu ^ h) • v = v := by
    rw [hgpow] at hpow_apply
    simpa using hpow_apply.symm
  have hmu_pow_eq_one : mu ^ h = 1 := by
    have hzero : (mu ^ h - 1) • v = 0 := by
      rw [sub_smul, one_smul, hmu_pow_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv.2)
  rcases hepsilon.eq_pow_of_pow_eq_one hmu_pow_eq_one with ⟨i, hi, hpow⟩
  exact ⟨⟨i, hi⟩, hpow.symm⟩

/-- If all eigenspaces of `g` span `V`, and every actual eigenvalue is among the
displayed powers of `epsilon`, then the BG finite family `V_i` spans `V`.

This isolates the finite-index bookkeeping from the heavier diagonalization
input needed for Prop 2.4(a). -/
theorem cyclicEigenspaceFin_iSup_eq_top_of_iSup_eigenspace_eq_top
    {epsilon : F} {g : Module.End F V} {h : ℕ}
    (hall : (⨆ mu : F, g.eigenspace mu) = ⊤)
    (hspectrum : ∀ mu : F, g.HasEigenvalue mu →
      ∃ i : Fin h, mu = epsilon ^ i.1) :
    (⨆ i : Fin h, cyclicEigenspaceFin epsilon g i) = ⊤ := by
  rw [← hall]
  refine le_antisymm ?_ ?_
  · exact iSup_le fun i => le_iSup (fun mu : F => g.eigenspace mu) (epsilon ^ i.1)
  · refine iSup_le fun mu => ?_
    by_cases hmu : g.HasEigenvalue mu
    · rcases hspectrum mu hmu with ⟨i, rfl⟩
      exact le_iSup (fun i : Fin h => cyclicEigenspaceFin epsilon g i) i
    · have hbot : g.eigenspace mu = ⊥ := by
        rw [← not_ne_iff]
        exact hmu
      rw [hbot]
      exact bot_le

/-- Finite-order version of the finite-family spanning bridge.

Once a separate diagonalization argument gives `⨆ mu, eigenspace g mu = ⊤`,
finite order plus a primitive root restricts that top span to the BG family
indexed by `Fin h`. -/
theorem cyclicEigenspaceFin_iSup_eq_top_of_iSup_eigenspace_eq_top_of_pow_eq_one
    {epsilon : F} {g : Module.End F V} {h : ℕ} [NeZero h]
    (hepsilon : IsPrimitiveRoot epsilon h) (hgpow : g ^ h = 1)
    (hall : (⨆ mu : F, g.eigenspace mu) = ⊤) :
    (⨆ i : Fin h, cyclicEigenspaceFin epsilon g i) = ⊤ :=
  cyclicEigenspaceFin_iSup_eq_top_of_iSup_eigenspace_eq_top hall fun _ hmu =>
    eigenvalue_eq_power_of_primitiveRoot_of_pow_eq_one hepsilon hgpow hmu

/-- Span form of the finite-order spanning bridge, matching the hypotheses used
by the block endomorphism calculations below. -/
theorem span_cyclicEigenspaceFinUnion_eq_top_of_iSup_eigenspace_eq_top_of_pow_eq_one
    {epsilon : F} {g : Module.End F V} {h : ℕ} [NeZero h]
    (hepsilon : IsPrimitiveRoot epsilon h) (hgpow : g ^ h = 1)
    (hall : (⨆ mu : F, g.eigenspace mu) = ⊤) :
    Submodule.span F (cyclicEigenspaceFinUnion epsilon g h) = ⊤ := by
  rw [span_cyclicEigenspaceFinUnion_eq_iSup]
  exact cyclicEigenspaceFin_iSup_eq_top_of_iSup_eigenspace_eq_top_of_pow_eq_one
    hepsilon hgpow hall

private theorem finset_sup_ker_aeval_eq_ker_aeval_prod_of_pairwise_coprime
    {ι : Type*} (s : Finset ι) (p : ι → Polynomial F)
    (g : Module.End F V)
    (hcop : (s : Set ι).Pairwise (IsCoprime on p)) :
    s.sup (fun i => LinearMap.ker (aeval g (p i))) =
      LinearMap.ker (aeval g (∏ i ∈ s, p i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sup_empty, Finset.prod_empty, map_one]
      exact (LinearMap.ker_eq_bot.mpr (by intro x y h; simpa using h)).symm
  | insert a s ha ih =>
      have hcop_s : (s : Set ι).Pairwise (IsCoprime on p) := by
        exact hcop.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
      have hcop_prod : IsCoprime (p a) (∏ i ∈ s, p i) := by
        exact IsCoprime.prod_right (fun i hi => hcop (Finset.mem_insert_self a s)
          (Finset.mem_insert_of_mem hi) (by intro hai; exact ha (hai ▸ hi)))
      rw [Finset.sup_insert, Finset.prod_insert ha, ih hcop_s]
      exact Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime g hcop_prod

private theorem ker_sub_algebraMap_pow_eq_cyclicEigenspace {epsilon : F}
    {g : Module.End F V} {i : ℕ} :
    LinearMap.ker (g - (algebraMap F (Module.End F V)) epsilon ^ i) =
      cyclicEigenspace epsilon g i := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    mem_cyclicEigenspace_iff]
  have hpow : (((algebraMap F (Module.End F V)) epsilon) ^ i) v =
      (epsilon ^ i) • v := by
    rw [← map_pow, Module.algebraMap_end_apply]
  rw [hpow]

private theorem ker_aeval_X_sub_C_eq_cyclicEigenspace {epsilon : F}
    {g : Module.End F V} {i : ℕ} :
    LinearMap.ker (aeval g (Polynomial.X - Polynomial.C (epsilon ^ i))) =
      cyclicEigenspace epsilon g i := by
  simpa [map_sub, aeval_X, aeval_C] using
    (ker_sub_algebraMap_pow_eq_cyclicEigenspace (epsilon := epsilon) (g := g) (i := i))

private theorem finset_sup_ker_X_sub_C_powers_eq_ker_X_pow_sub_one
    {epsilon : F} {g : Module.End F V} {h : ℕ} [NeZero h]
    (hepsilon : IsPrimitiveRoot epsilon h) :
    (Finset.univ : Finset (Fin h)).sup
        (fun i => LinearMap.ker (aeval g (Polynomial.X - Polynomial.C (epsilon ^ i.1)))) =
      LinearMap.ker (aeval g (Polynomial.X ^ h - Polynomial.C (1 : F))) := by
  classical
  have hinj : Function.Injective fun i : Fin h => epsilon ^ i.1 := by
    intro i j hij
    exact Fin.ext (hepsilon.pow_inj i.2 j.2 hij)
  have hcop : ((Finset.univ : Finset (Fin h)) : Set (Fin h)).Pairwise
      (IsCoprime on fun i : Fin h => Polynomial.X - Polynomial.C (epsilon ^ i.1 : F)) := by
    exact Polynomial.pairwise_coprime_X_sub_C hinj |>.set_pairwise _
  have hsup := finset_sup_ker_aeval_eq_ker_aeval_prod_of_pairwise_coprime
    (F := F) (V := V) (Finset.univ : Finset (Fin h))
    (fun i : Fin h => Polynomial.X - Polynomial.C (epsilon ^ i.1 : F)) g hcop
  have hprod :
      (∏ i : Fin h, (Polynomial.X - Polynomial.C (epsilon ^ i.1 : F))) =
        Polynomial.X ^ h - Polynomial.C (1 : F) := by
    calc
      (∏ i : Fin h, (Polynomial.X - Polynomial.C (epsilon ^ i.1 : F)))
          = ∏ i ∈ Finset.range h, (Polynomial.X - Polynomial.C (epsilon ^ i : F)) := by
            simpa using (Fin.prod_univ_eq_prod_range
              (fun i => Polynomial.X - Polynomial.C (epsilon ^ i : F)) h)
      _ = Polynomial.X ^ h - Polynomial.C (1 : F) := by
            simpa using (X_pow_sub_C_eq_prod hepsilon (NeZero.pos h) (one_pow h)).symm
  rw [hprod] at hsup
  simpa using hsup

/-- BG Prop 2.4(a)'s spanning input.

If `g` has finite order dividing `h` and `epsilon` is a primitive `h`-th root,
then the displayed finite family of eigenspaces `V_i`, `i : Fin h`, spans the
whole space.  The proof factors `X^h - 1` into the distinct linear factors
`X - epsilon^i` and uses coprime kernel decomposition for polynomial
functional calculus. -/
theorem cyclicEigenspaceFin_iSup_eq_top_of_pow_eq_one
    {epsilon : F} {g : Module.End F V} {h : ℕ} [NeZero h]
    (hepsilon : IsPrimitiveRoot epsilon h) (hgpow : g ^ h = 1) :
    (⨆ i : Fin h, cyclicEigenspaceFin epsilon g i) = ⊤ := by
  classical
  have hsup := finset_sup_ker_X_sub_C_powers_eq_ker_X_pow_sub_one
    (F := F) (V := V) (epsilon := epsilon) (g := g) (h := h) hepsilon
  rw [Finset.sup_univ_eq_iSup] at hsup
  have hker : LinearMap.ker (aeval g (Polynomial.X ^ h - Polynomial.C (1 : F))) = ⊤ := by
    have hae : aeval g (Polynomial.X ^ h - Polynomial.C (1 : F)) = 0 := by
      simp [hgpow]
    rw [hae, LinearMap.ker_zero]
  rw [hker] at hsup
  simpa [cyclicEigenspaceFin, ker_aeval_X_sub_C_eq_cyclicEigenspace,
    ker_sub_algebraMap_pow_eq_cyclicEigenspace] using hsup

/-- Span form of BG Prop 2.4(a)'s finite-order spanning input. -/
theorem span_cyclicEigenspaceFinUnion_eq_top_of_pow_eq_one
    {epsilon : F} {g : Module.End F V} {h : ℕ} [NeZero h]
    (hepsilon : IsPrimitiveRoot epsilon h) (hgpow : g ^ h = 1) :
    Submodule.span F (cyclicEigenspaceFinUnion epsilon g h) = ⊤ := by
  rw [span_cyclicEigenspaceFinUnion_eq_iSup]
  exact cyclicEigenspaceFin_iSup_eq_top_of_pow_eq_one hepsilon hgpow

/-- BG Prop 2.4(a), internal direct-sum form.

The finite displayed eigenspaces `V_0, ..., V_{h-1}` form an internal direct
sum decomposition of `V` when `g ^ h = 1` and `epsilon` is a primitive
`h`-th root.  This packages the independent-eigenspace and finite-order
spanning halves into mathlib's `DirectSum.IsInternal` API. -/
theorem cyclicEigenspaceFin_isInternal_of_pow_eq_one
    {epsilon : F} {g : Module.End F V} {h : ℕ} [NeZero h]
    (hepsilon : IsPrimitiveRoot epsilon h) (hgpow : g ^ h = 1) :
    DirectSum.IsInternal fun i : Fin h => cyclicEigenspaceFin epsilon g i := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (cyclicEigenspaceFin_iSupIndep (F := F) (V := V) (g := g) hepsilon)
    (cyclicEigenspaceFin_iSup_eq_top_of_pow_eq_one (F := F) (V := V) hepsilon hgpow)

/-- BG Prop 2.4 notation `E_{i,t}` over the finite index range
`0 ≤ i,t ≤ h - 1`.

An endomorphism in this block sends `V_i` into `V_t` and kills every other
`V_j` in the displayed finite family. -/
def cyclicHomBlockFin (epsilon : F) (g : Module.End F V) {h : ℕ}
    (i t : Fin h) : Submodule F (Module.End F V) where
  carrier :=
    {e | (∀ v : V, v ∈ cyclicEigenspaceFin epsilon g i →
          e v ∈ cyclicEigenspaceFin epsilon g t) ∧
      ∀ j : Fin h, j ≠ i → ∀ v : V,
        v ∈ cyclicEigenspaceFin epsilon g j → e v = 0}
  zero_mem' := by
    constructor
    · intro v hv
      simp
    · intro j hj v hv
      simp
  add_mem' := by
    intro e f he hf
    constructor
    · intro v hv
      exact (cyclicEigenspaceFin epsilon g t).add_mem (he.1 v hv) (hf.1 v hv)
    · intro j hj v hv
      rw [LinearMap.add_apply, he.2 j hj v hv, hf.2 j hj v hv, add_zero]
  smul_mem' := by
    intro a e he
    constructor
    · intro v hv
      exact (cyclicEigenspaceFin epsilon g t).smul_mem a (he.1 v hv)
    · intro j hj v hv
      rw [LinearMap.smul_apply, he.2 j hj v hv, smul_zero]

@[simp]
theorem mem_cyclicHomBlockFin_iff {epsilon : F} {g : Module.End F V}
    {h : ℕ} {i t : Fin h} {e : Module.End F V} :
    e ∈ cyclicHomBlockFin epsilon g i t ↔
      (∀ v : V, v ∈ cyclicEigenspaceFin epsilon g i →
        e v ∈ cyclicEigenspaceFin epsilon g t) ∧
      ∀ j : Fin h, j ≠ i → ∀ v : V,
        v ∈ cyclicEigenspaceFin epsilon g j → e v = 0 := by
  rfl

private theorem inv_mem_cyclicEigenspaceFin {epsilon : F}
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} {i : Fin h} {v : V}
    (hv : v ∈ cyclicEigenspaceFin epsilon (g : Module.End F V) i) :
    glInvEnd g v ∈
      cyclicEigenspaceFin epsilon (g : Module.End F V) i := by
  rw [mem_cyclicEigenspaceFin_iff] at hv ⊢
  have hleft :
      (g : Module.End F V) (glInvEnd g v) = v := by
    change g.toLinearEquiv (g.toLinearEquiv.symm v) = v
    exact g.toLinearEquiv.apply_symm_apply v
  have hright :
      glInvEnd g ((g : Module.End F V) v) = v := by
    change g.toLinearEquiv.symm (g.toLinearEquiv v) = v
    exact g.toLinearEquiv.symm_apply_apply v
  have hv_apply :
      glInvEnd g ((g : Module.End F V) v) =
          (epsilon ^ i.1) • glInvEnd g v := by
    rw [hv]
    simp [glInvEnd]
  calc
    (g : Module.End F V) (glInvEnd g v) = v := by
      exact hleft
    _ = (epsilon ^ i.1) • glInvEnd g v := by
      exact hright.symm.trans hv_apply

private theorem smul_inv_mem_eq_of_mem_cyclicEigenspaceFin {epsilon : F}
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} {i : Fin h} {v : V}
    (hv : v ∈ cyclicEigenspaceFin epsilon (g : Module.End F V) i) :
    (epsilon ^ i.1) • glInvEnd g v = v := by
  rw [mem_cyclicEigenspaceFin_iff] at hv
  have hright :
      glInvEnd g ((g : Module.End F V) v) = v := by
    change g.toLinearEquiv.symm (g.toLinearEquiv v) = v
    exact g.toLinearEquiv.symm_apply_apply v
  have hv_apply :
      glInvEnd g ((g : Module.End F V) v) = (epsilon ^ i.1) • glInvEnd g v := by
    rw [hv]
    simp [glInvEnd]
  calc
    (epsilon ^ i.1) • glInvEnd g v
        = glInvEnd g ((g : Module.End F V) v) := by
          exact hv_apply.symm
    _ = v := by
      exact hright

/-- Conjugation preserves each finite BG block `E_{i,t}`. -/
theorem cyclicEndConj_mem_cyclicHomBlockFin {epsilon : F}
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} {i t : Fin h}
    {e : Module.End F V}
    (he : e ∈ cyclicHomBlockFin epsilon (g : Module.End F V) i t) :
    cyclicEndConj g e ∈ cyclicHomBlockFin epsilon (g : Module.End F V) i t := by
  rw [mem_cyclicHomBlockFin_iff] at he ⊢
  constructor
  · intro v hv
    have hv_mem := hv
    rw [mem_cyclicEigenspaceFin_iff] at hv
    have hinv :
        glInvEnd g v ∈
          cyclicEigenspaceFin epsilon (g : Module.End F V) i :=
      inv_mem_cyclicEigenspaceFin hv_mem
    have himage := he.1 (glInvEnd g v) hinv
    have himage_eq := mem_cyclicEigenspaceFin_iff.mp himage
    rw [cyclicEndConj_apply, himage_eq]
    exact (cyclicEigenspaceFin epsilon (g : Module.End F V) t).smul_mem _ himage
  · intro j hj v hv
    have hinv :
        glInvEnd g v ∈
          cyclicEigenspaceFin epsilon (g : Module.End F V) j :=
      inv_mem_cyclicEigenspaceFin hv
    rw [cyclicEndConj_apply,
      he.2 j hj (glInvEnd g v) hinv,
      map_zero]

/-- Pointwise scalar relation behind BG Prop 2.4(e).

If `e ∈ E_{i,t}` and `v ∈ V_i`, then conjugating `e` by `g` multiplies its
value on `v` by the ratio of the two eigenvalues.  This formulation avoids
division and is the most robust form over a field. -/
theorem smul_cyclicEndConj_apply_of_mem_cyclicHomBlockFin
    {epsilon : F} {g : LinearMap.GeneralLinearGroup F V} {h : ℕ}
    {i t : Fin h} {e : Module.End F V}
    (he : e ∈ cyclicHomBlockFin epsilon (g : Module.End F V) i t)
    {v : V} (hv : v ∈ cyclicEigenspaceFin epsilon (g : Module.End F V) i) :
    (epsilon ^ i.1) • cyclicEndConj g e v = (epsilon ^ t.1) • e v := by
  rw [mem_cyclicHomBlockFin_iff] at he
  have hinv :
      glInvEnd g v ∈
        cyclicEigenspaceFin epsilon (g : Module.End F V) i :=
    inv_mem_cyclicEigenspaceFin hv
  have hsource :
      (epsilon ^ i.1) • glInvEnd g v = v :=
    smul_inv_mem_eq_of_mem_cyclicEigenspaceFin hv
  have htarget := he.1 (glInvEnd g v) hinv
  rw [mem_cyclicEigenspaceFin_iff] at htarget
  have htarget_v := he.1 v hv
  rw [mem_cyclicEigenspaceFin_iff] at htarget_v
  calc
    (epsilon ^ i.1) • cyclicEndConj g e v
        = (g : Module.End F V)
            ((epsilon ^ i.1) •
              e (glInvEnd g v)) := by
          simp [cyclicEndConj_apply]
    _ = (g : Module.End F V) (e v) := by
          rw [← map_smul, hsource]
    _ = (epsilon ^ t.1) • e v := htarget_v

/-- Map-level scalar relation for a block endomorphism, assuming the displayed
eigenspaces span `V`.

This is the theorem-facing form of the calculation used in BG Prop 2.4(e);
later direct-sum work can provide the `span` hypothesis from Prop 2.4(a). -/
theorem smul_cyclicEndConj_eq_of_mem_cyclicHomBlockFin_of_span
    {epsilon : F} {g : LinearMap.GeneralLinearGroup F V} {h : ℕ}
    {i t : Fin h} {e : Module.End F V}
    (hspan : Submodule.span F
      (cyclicEigenspaceFinUnion epsilon (g : Module.End F V) h) = ⊤)
    (he : e ∈ cyclicHomBlockFin epsilon (g : Module.End F V) i t) :
    (epsilon ^ i.1) • cyclicEndConj g e = (epsilon ^ t.1) • e := by
  rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ hspan]
  intro v
  rcases v.2 with ⟨j, hvj⟩
  by_cases hji : j = i
  · subst hji
    exact smul_cyclicEndConj_apply_of_mem_cyclicHomBlockFin he hvj
  · rw [mem_cyclicHomBlockFin_iff] at he
    have hconj := (mem_cyclicHomBlockFin_iff.mp
      (cyclicEndConj_mem_cyclicHomBlockFin he)).2 j hji v hvj
    have hezero := he.2 j hji v hvj
    simp [hconj, hezero]

/-- Division form of `smul_cyclicEndConj_eq_of_mem_cyclicHomBlockFin_of_span`.

This is convenient when later identifying the ratio with `epsilon^(t-i)`, or
with the corresponding residue class modulo the period. -/
theorem cyclicEndConj_eq_smul_ratio_of_mem_cyclicHomBlockFin_of_span
    {epsilon : F} (hepsilon_ne_zero : epsilon ≠ 0)
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ}
    {i t : Fin h} {e : Module.End F V}
    (hspan : Submodule.span F
      (cyclicEigenspaceFinUnion epsilon (g : Module.End F V) h) = ⊤)
    (he : e ∈ cyclicHomBlockFin epsilon (g : Module.End F V) i t) :
    cyclicEndConj g e = ((epsilon ^ t.1) / (epsilon ^ i.1)) • e := by
  have hscalar :=
    smul_cyclicEndConj_eq_of_mem_cyclicHomBlockFin_of_span
      (g := g) (i := i) (t := t) hspan he
  have hi : epsilon ^ i.1 ≠ 0 := pow_ne_zero _ hepsilon_ne_zero
  calc
    cyclicEndConj g e
        = (epsilon ^ i.1)⁻¹ • ((epsilon ^ i.1) • cyclicEndConj g e) := by
          rw [smul_smul, inv_mul_cancel₀ hi, one_smul]
    _ = (epsilon ^ i.1)⁻¹ • ((epsilon ^ t.1) • e) := by
          rw [hscalar]
    _ = ((epsilon ^ t.1) / (epsilon ^ i.1)) • e := by
          rw [smul_smul, div_eq_mul_inv, mul_comm]

/-- Inclusion form of BG Prop 2.4(e), with the modular arithmetic separated.

If the scalar ratio attached to a block `E_{i,t}` is already identified with
`epsilon^m`, then the block lies in the `m`-th conjugation eigenspace.  Later
Prop 2.4 work can supply the congruence calculation `m ≡ t - i (mod h)`. -/
theorem cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_ratio
    {epsilon : F} (hepsilon_ne_zero : epsilon ≠ 0)
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} {i t : Fin h} {m : ℕ}
    (hspan : Submodule.span F
      (cyclicEigenspaceFinUnion epsilon (g : Module.End F V) h) = ⊤)
    (hratio : (epsilon ^ t.1) / (epsilon ^ i.1) = epsilon ^ m) :
    cyclicHomBlockFin epsilon (g : Module.End F V) i t ≤
      cyclicEndConjEigenspace epsilon g m := by
  intro e he
  rw [mem_cyclicEigenspace_iff]
  rw [cyclicEndConj_eq_smul_ratio_of_mem_cyclicHomBlockFin_of_span
    hepsilon_ne_zero hspan he, hratio]

/-- Modular-index form of BG Prop 2.4(e).

If `i + m ≡ t (mod h)`, then the scalar ratio on `E_{i,t}` is `epsilon^m`,
so the block lies in the `m`-th eigenspace for conjugation.  This is the
finite-index bookkeeping needed to turn the pointwise calculation into BG's
`E_{i,t} ⊆ E_{t-i}` statement. -/
theorem cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_modEq
    {epsilon : F} (hepsilon_ne_zero : epsilon ≠ 0)
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} {i t : Fin h} {m : ℕ}
    (hspan : Submodule.span F
      (cyclicEigenspaceFinUnion epsilon (g : Module.End F V) h) = ⊤)
    (hperiod : epsilon ^ h = 1) (hmod : i.1 + m ≡ t.1 [MOD h]) :
    cyclicHomBlockFin epsilon (g : Module.End F V) i t ≤
      cyclicEndConjEigenspace epsilon g m := by
  refine cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_ratio
    hepsilon_ne_zero hspan ?_
  have hi : epsilon ^ i.1 ≠ 0 := pow_ne_zero _ hepsilon_ne_zero
  have hpow : epsilon ^ (i.1 + m) = epsilon ^ t.1 :=
    pow_eq_pow_of_modEq hmod hperiod
  have hmul : epsilon ^ i.1 * epsilon ^ m = epsilon ^ t.1 := by
    simpa [pow_add] using hpow
  calc
    (epsilon ^ t.1) / (epsilon ^ i.1)
        = (epsilon ^ i.1 * epsilon ^ m) * (epsilon ^ i.1)⁻¹ := by
          rw [hmul, div_eq_mul_inv]
    _ = epsilon ^ m := by
          rw [mul_assoc, mul_comm (epsilon ^ m) ((epsilon ^ i.1)⁻¹), ← mul_assoc,
            mul_inv_cancel₀ hi, one_mul]

/-- Non-wrapping form of BG Prop 2.4(e): if `t = i + m` inside the displayed
finite index range, then `E_{i,t}` lies in `E_m`.

The full BG statement uses indices modulo `h`; this lemma isolates the linear
algebra from the later modular-index bookkeeping. -/
theorem cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_eq_add
    {epsilon : F} (hepsilon_ne_zero : epsilon ≠ 0)
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} {i t : Fin h} {m : ℕ}
    (hspan : Submodule.span F
      (cyclicEigenspaceFinUnion epsilon (g : Module.End F V) h) = ⊤)
    (ht : t.1 = i.1 + m) :
    cyclicHomBlockFin epsilon (g : Module.End F V) i t ≤
      cyclicEndConjEigenspace epsilon g m := by
  refine cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_ratio
    hepsilon_ne_zero hspan ?_
  have hi : epsilon ^ i.1 ≠ 0 := pow_ne_zero _ hepsilon_ne_zero
  rw [ht, pow_add, div_eq_mul_inv, mul_assoc,
    mul_comm (epsilon ^ m) ((epsilon ^ i.1)⁻¹), ← mul_assoc,
    mul_inv_cancel₀ hi, one_mul]

end EigenspaceUnderCyclicAction
end RepresentationTheory
end OddOrder
