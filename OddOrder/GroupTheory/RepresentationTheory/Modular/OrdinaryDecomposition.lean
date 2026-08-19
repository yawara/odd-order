/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockOfSimpleModule
import OddOrder.Algebra.TraceIsCompl
import OddOrder.GroupTheory.MaschkeComplement
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockRepresentation
import OddOrder.GroupTheory.RepresentationTheory.Modular.MinimalSubrepresentation

/-!
# Every ordinary character decomposes into irreducible ones

The characteristic-zero counterpart of `BrauerDecomposition`.  A splitting `π : KG → ∏ M_{n_i}(K)`
whose kernel is the Jacobson radical — for `K` of characteristic `0` that radical is `0`, so `π`
is a Wedderburn isomorphism and the index set is `Irr(G)` — makes every finite-dimensional
representation's character a non-negative integer combination of the `n_i`-dimensional ones.

The induction is on dimension, exactly as on the modular side, but with one simplification: since
`|G|` is invertible, Maschke gives an **invariant complement** of the minimal invariant subspace
(`exists_isCompl_invariant`), so the trace splits by
`trace_eq_add_trace_restrict_of_isCompl` and no trace additivity along a short exact sequence is
needed.

As on the modular side the induction also delivers **block-diagonality**: a constituent that
actually occurs has the same central character as the whole representation, whenever the centre
acts by a scalar.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_ordinaryCharacter_eq` — a simple representation
  is one of the `n_i`-dimensional ones
* `OddOrder.RepresentationTheory.Modular.exists_ordinary_decomposition_of_finrank_le`
* `OddOrder.RepresentationTheory.Modular.exists_ordinary_decomposition`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

variable {K G : Type*} [Field K] [Group G] {ι : Type*} {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

/-! ### A simple representation is one of the blocks -/

section Simple

variable {V : Type*} [AddCommGroup V] [Module K V]

set_option linter.unusedFintypeInType false in
/-- **A simple representation has one of the irreducible ordinary characters**, and its central
character is read off at the *same* index — the pairing that makes block-diagonality work. -/
theorem exists_ordinaryCharacter_eq (ρ : Representation K G V)
    [IsSimpleModule (MonoidAlgebra K G) ρ.asModule]
    {π : MonoidAlgebra K G →+* ∀ j, Matrix (nn j) (nn j) K} (hπ : Function.Surjective π)
    (hlin : ∀ (c : K) (a : MonoidAlgebra K G), π (c • a) = c • π a)
    (hker : RingHom.ker π ≤ Module.annihilator (MonoidAlgebra K G) ρ.asModule) :
    ∃ i : ι, (∀ g : G, LinearMap.trace K V (ρ g)
        = LinearMap.trace K (nn i → K) (blockRepresentation π i g)) ∧
      ∀ {z : Subalgebra.center K (MonoidAlgebra K G)} {c : K},
        (∀ m : ρ.asModule, (z : MonoidAlgebra K G) • m
          = (algebraMap K (MonoidAlgebra K G) c) • m) →
        c = MatrixModule.centralCharacterAlg π i hπ hlin z := by
  obtain ⟨i, ⟨e⟩⟩ := MatrixModule.exists_linearEquiv_blockModule (nn := nn) hπ hker
  let := MatrixModule.blockModule nn π i
  have := MatrixModule.isScalarTower_blockModule (nn := nn) hlin i
  refine ⟨i, fun g => ?_, fun {z c} hzc => ?_⟩
  · set f : V ≃ₗ[K] (nn i → K) :=
      (ρ.asModuleEquiv.symm).trans (e.restrictScalars K) with hf
    have hint : ∀ (g : G) (v : V), f ((ρ g) v) = (blockRepresentation π i g) (f v) := by
      intro g v
      have h1 : ρ.asModuleEquiv.symm ((ρ g) v)
          = (single g (1 : K)) • ρ.asModuleEquiv.symm v :=
        Representation.asModuleEquiv_symm_map_rho ρ g v
      simp only [hf, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1]
      rw [e.map_smul]
      rfl
    have hconj : blockRepresentation π i g = f.conj (ρ g) := by
      refine LinearMap.ext fun v => ?_
      have hv := hint g (f.symm v)
      rw [LinearEquiv.apply_symm_apply] at hv
      simpa [LinearEquiv.conj_apply] using hv.symm
    rw [hconj, LinearMap.trace_conj']
  · refine MatrixModule.eq_centralCharacterAlg_of_forall_smul_eq π i hπ hlin fun v => ?_
    have hv := congrArg e (hzc (e.symm v))
    rw [map_smul, map_smul, e.apply_symm_apply] at hv
    rw [hv, algebraMap_smul]

end Simple

/-! ### The decomposition -/

section Decomposition

variable [Finite G] [NeZero (Nat.card G : K)]
variable {π : MonoidAlgebra K G →+* ∀ j, Matrix (nn j) (nn j) K} (hπ : Function.Surjective π)
  (hlin : ∀ (c : K) (a : MonoidAlgebra K G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra K G))
include hπ hlin hkerJ

/-- **Every ordinary character is a non-negative integer combination of the irreducible ones**,
together with block-diagonality. -/
theorem exists_ordinary_decomposition_of_finrank_le (m : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (ρ : Representation K G V),
      Module.finrank K V ≤ m →
      ∃ d : ι → ℕ, (∀ g : G, LinearMap.trace K V (ρ g)
          = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g)) ∧
        ∀ (i : ι) {z : Subalgebra.center K (MonoidAlgebra K G)} {c : K}, d i ≠ 0 →
          ρ.asAlgebraHom (z : MonoidAlgebra K G) = c • LinearMap.id →
          c = MatrixModule.centralCharacterAlg π i hπ hlin z := by
  classical
  induction m with
  | zero =>
    intro V _ _ _ ρ hm
    have : Subsingleton V := Module.finrank_zero_iff.mp (Nat.le_zero.mp hm)
    refine ⟨0, fun g => ?_, ?_⟩
    · rw [show ρ g = 0 from Subsingleton.elim _ _, map_zero]
      simp
    · intro i z c hi _
      exact absurd rfl hi
  | succ m ih =>
    intro V _ _ _ ρ hm
    rcases subsingleton_or_nontrivial V with _ | _
    · refine ⟨0, fun g => ?_, ?_⟩
      · rw [show ρ g = 0 from Subsingleton.elim _ _, map_zero]
        simp
      · intro i z c hi _
        exact absurd rfl hi
    obtain ⟨W, hWinv, hWne, hWmin⟩ := exists_minimal_invariant ρ
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
    have := isSimpleModule_subrepresentation_of_minimal ρ hWinv hWne hWmin
    obtain ⟨i, hi, hic⟩ := exists_ordinaryCharacter_eq (nn := nn)
      (ρ.subrepresentation W hWinv) hπ hlin
      (hkerJ ▸ IsSemisimpleModule.jacobson_le_annihilator _ _)
    obtain ⟨W', hW'inv, hcompl⟩ :=
      OddOrder.GroupTheory.exists_isCompl_invariant ρ W fun g _ hv => hWinv g hv
    have hW'le : ∀ g : G, W' ≤ W'.comap (ρ g) := fun g _ hv => hW'inv g hv
    have hrank : Module.finrank K W + Module.finrank K W' = Module.finrank K V :=
      Submodule.finrank_add_eq_of_isCompl hcompl
    have hWpos : 0 < Module.finrank K W := Module.finrank_pos
    obtain ⟨d, hd, hdc⟩ := ih (ρ.subrepresentation W' hW'le) (by omega)
    refine ⟨d + Pi.single i 1, fun g => ?_, ?_⟩
    · have h1 : LinearMap.trace K W ((ρ g).restrict (fun _ hv => hWinv g hv))
          = LinearMap.trace K (nn i → K) (blockRepresentation π i g) := hi g
      have h2 : LinearMap.trace K W' ((ρ g).restrict (fun _ hv => hW'inv g hv))
          = ∑ j, (d j : K) * LinearMap.trace K (nn j → K) (blockRepresentation π j g) := hd g
      rw [trace_eq_add_trace_restrict_of_isCompl hcompl (fun _ hv => hWinv g hv)
        (fun _ hv => hW'inv g hv), h1, h2]
      have hsingle : ∑ j, (((Pi.single i 1 : ι → ℕ) j : ℕ) : K) *
          LinearMap.trace K (nn j → K) (blockRepresentation π j g)
          = LinearMap.trace K (nn i → K) (blockRepresentation π i g) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · intro hmem
          exact absurd (Finset.mem_univ i) hmem
      simp only [Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, hsingle]
      exact add_comm _ _
    · intro j z c hj hz
      rcases Nat.eq_zero_or_pos (d j) with hdj | hdj
      · have hji : j = i := by
          by_contra hne
          rw [Pi.add_apply, hdj, Pi.single_eq_of_ne hne] at hj
          exact hj rfl
        subst hji
        refine hic fun mm => ?_
        apply (ρ.subrepresentation W hWinv).asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul,
          subrepresentation_asAlgebraHom_eq_smul ρ hWinv hz, AlgHom.commutes]
        simp
      · refine hdc j hdj.ne' (LinearMap.ext fun v => ?_)
        exact subrepresentation_asAlgebraHom_eq_smul ρ hW'le hz v

/-- **The decomposition of an ordinary character into irreducible ones.** -/
theorem exists_ordinary_decomposition {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K G V) :
    ∃ d : ι → ℕ, (∀ g : G, LinearMap.trace K V (ρ g)
        = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g)) ∧
      ∀ (i : ι) {z : Subalgebra.center K (MonoidAlgebra K G)} {c : K}, d i ≠ 0 →
        ρ.asAlgebraHom (z : MonoidAlgebra K G) = c • LinearMap.id →
        c = MatrixModule.centralCharacterAlg π i hπ hlin z :=
  exists_ordinary_decomposition_of_finrank_le hπ hlin hkerJ _ ρ le_rfl

/-! ### The decomposition at the level of the group algebra

Navarro (5.2) evaluates `χ` not at a group element but at `f_b x y ∈ 𝒪H`, so the decomposition
has to hold for every element of the group algebra.  Both sides are `K`-linear and agree on the
monomials, so this is an induction. -/

omit hπ hlin hkerJ [∀ i, Nonempty (nn i)] [Finite G] [NeZero (Nat.card G : K)] in
/-- **The decomposition holds on all of `KG`, not just on `G`.**  Applied to `a = f_b · g` this is
what lets a block idempotent be inserted into a character value: it acts on the `i`-th constituent
by the scalar `ω_i(f_b)`, which is `1` for `i ∈ Irr(b)` and `0` otherwise. -/
theorem trace_asAlgebraHom_eq_sum {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K G V} {d : ι → ℕ}
    (hd : ∀ g : G, LinearMap.trace K V (ρ g)
      = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g))
    (a : MonoidAlgebra K G) :
    LinearMap.trace K V (ρ.asAlgebraHom a)
      = ∑ i, (d i : K)
          * LinearMap.trace K (nn i → K) ((blockRepresentation π i).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, hu, hv, mul_add]
    rw [Finset.sum_add_distrib]
  | single g r =>
    rw [Representation.asAlgebraHom_single, map_smul, hd g, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, smul_eq_mul]
    ring

omit hkerJ [Finite G] [NeZero (Nat.card G : K)] in
/-- **A central element scales each term of the decomposition by its central character.**  With
`z = f_b` this is the step that makes a block idempotent select the constituents in `b`: the
scalar `ω_i(f_b)` is an idempotent of `K`, hence `0` or `1`. -/
theorem trace_asAlgebraHom_center_mul {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K G V} {d : ι → ℕ}
    (hd : ∀ g : G, LinearMap.trace K V (ρ g)
      = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g))
    (z : Subalgebra.center K (MonoidAlgebra K G)) (a : MonoidAlgebra K G) :
    LinearMap.trace K V (ρ.asAlgebraHom ((z : MonoidAlgebra K G) * a))
      = ∑ i, (d i : K) * MatrixModule.centralCharacterAlg π i hπ hlin z
          * LinearMap.trace K (nn i → K) ((blockRepresentation π i).asAlgebraHom a) := by
  rw [trace_asAlgebraHom_eq_sum hd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, blockRepresentation_asAlgebraHom_center hπ hlin i z, smul_mul_assoc,
    show (LinearMap.id : (nn i → K) →ₗ[K] (nn i → K))
      * (blockRepresentation π i).asAlgebraHom a = (blockRepresentation π i).asAlgebraHom a from
      one_mul _,
    map_smul, smul_eq_mul]
  ring

omit hkerJ [Finite G] [NeZero (Nat.card G : K)] in
/-- **Two central factors scale each term twice.**  Navarro (5.2) needs exactly this shape: `f_b`
picks out the constituents in `b` and `x ∈ Z(H)` contributes the scalar `χ_i(x)/χ_i(1)`. -/
theorem trace_asAlgebraHom_center_center_mul {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K G V} {d : ι → ℕ}
    (hd : ∀ g : G, LinearMap.trace K V (ρ g)
      = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g))
    (z w : Subalgebra.center K (MonoidAlgebra K G)) (g : G) :
    LinearMap.trace K V
        (ρ.asAlgebraHom ((z : MonoidAlgebra K G) * ((w : MonoidAlgebra K G) * single g 1)))
      = ∑ i, (d i : K) * MatrixModule.centralCharacterAlg π i hπ hlin z
          * MatrixModule.centralCharacterAlg π i hπ hlin w
          * LinearMap.trace K (nn i → K) (blockRepresentation π i g) := by
  rw [trace_asAlgebraHom_center_mul hπ hlin hd z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, blockRepresentation_asAlgebraHom_center hπ hlin i w, smul_mul_assoc,
    show (LinearMap.id : (nn i → K) →ₗ[K] (nn i → K))
      * (blockRepresentation π i).asAlgebraHom (single g 1)
      = (blockRepresentation π i).asAlgebraHom (single g 1) from one_mul _,
    map_smul, smul_eq_mul, Representation.asAlgebraHom_single_one]
  ring

omit hkerJ [Finite G] [NeZero (Nat.card G : K)] [Fintype ι] in
/-- **A central idempotent has central character `0` or `1`.**  This is what makes `f_b` select a
sub-sum: over a field the only idempotents are the trivial ones. -/
theorem centralCharacterAlg_eq_zero_or_one_of_isIdempotentElem (i : ι)
    {f : Subalgebra.center K (MonoidAlgebra K G)} (hf : IsIdempotentElem f) :
    MatrixModule.centralCharacterAlg π i hπ hlin f = 0 ∨
      MatrixModule.centralCharacterAlg π i hπ hlin f = 1 := by
  have h := congrArg (MatrixModule.centralCharacterAlg π i hπ hlin) hf
  rw [map_mul] at h
  set c := MatrixModule.centralCharacterAlg π i hπ hlin f with hc
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (sub_eq_zero.mp h1)

open scoped Classical in
omit hkerJ [Finite G] [NeZero (Nat.card G : K)] in
/-- **A block idempotent restricts the decomposition to its own block.**  Since `ω_i(f)` is `0`
or `1`, inserting `f` deletes every term outside `{i | ω_i(f) = 1}` — which for `f = f_b` is
`Irr(b)`.  This is the shape Navarro (5.2) consumes. -/
theorem trace_asAlgebraHom_blockIdempotent_mul {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K G V} {d : ι → ℕ}
    (hd : ∀ g : G, LinearMap.trace K V (ρ g)
      = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g))
    {f : Subalgebra.center K (MonoidAlgebra K G)} (hf : IsIdempotentElem f)
    (a : MonoidAlgebra K G) :
    LinearMap.trace K V (ρ.asAlgebraHom ((f : MonoidAlgebra K G) * a))
      = ∑ i ∈ Finset.univ.filter
          (fun i => MatrixModule.centralCharacterAlg π i hπ hlin f = 1),
        (d i : K)
          * LinearMap.trace K (nn i → K) ((blockRepresentation π i).asAlgebraHom a) := by
  classical
  rw [trace_asAlgebraHom_center_mul hπ hlin hd]
  have hfilter := Finset.sum_filter_of_ne (s := (Finset.univ : Finset ι))
    (p := fun i => MatrixModule.centralCharacterAlg π i hπ hlin f = 1)
    (f := fun i => (d i : K) * MatrixModule.centralCharacterAlg π i hπ hlin f
      * LinearMap.trace K (nn i → K) ((blockRepresentation π i).asAlgebraHom a))
    (fun i _ hne => by
      rcases centralCharacterAlg_eq_zero_or_one_of_isIdempotentElem hπ hlin i hf with h0 | h1
      · exact absurd (by rw [h0, mul_zero, zero_mul]) hne
      · exact h1)
  rw [← hfilter]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2, mul_one]

end Decomposition

end OddOrder.RepresentationTheory.Modular
