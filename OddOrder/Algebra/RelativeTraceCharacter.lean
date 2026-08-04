/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Trace
import OddOrder.Algebra.GroupAlgebraConjugation

/-!
# Characters of relative traces

A representation `ψ : R[G] →ₐ[R] E` composed with a *symmetric* additive map `τ : E →+ M`
(`τ (x * y) = τ (y * x)`, the abstract shape of a trace) produces a **class function**
`τ ∘ ψ` on `R[G]`: it is unchanged by the conjugation action of `G`.  Combined with
`OddOrder.GAlgebra.map_relTrace` this gives

`τ (ψ (Tr^H_K a)) = [H : K] • τ (ψ a)`,

so an element of the relative trace ideal `R[G]^H_K` has its character divisible by `[H : K]`.

Applied to a block idempotent `f_B = Tr^G_D(a)` with `D` a defect group, and to a representation
in the block `B` — where `f_B` acts as the identity — this reads

`χ(1) = [G : D] · τ(ψ a)`,

which is **the height inequality**: `[G : D]` divides the degree of every ordinary irreducible
character in `B`.  Over a `p`-modular system `[G : D]` has `p`-part `p^{ν(|G|) - d(B)}`, so
`ν(χ(1)) ≥ ν(|G|) - d(B)` and the *height* `ν(χ(1)) - ν(|G|) + d(B)` is a non-negative integer.

Everything here is over an arbitrary commutative ring: no valuation, no characteristic
assumption, and no finiteness of the module is used before the final step.

## Main results

* `OddOrder.GroupAlgebra.symmMap_comp_conj` — `τ ∘ ψ` is invariant under conjugation
* `OddOrder.GroupAlgebra.symmMap_relTrace` — `τ (ψ (Tr^H_K a)) = [H : K] • τ (ψ a)`
* `OddOrder.GroupAlgebra.relIndex_dvd_finrank` — `[H : K] ∣ χ(1)` for `f ∈ R[G]^H_K` acting as `1`
* `OddOrder.GroupAlgebra.index_dvd_finrank` — the `H = ⊤` case, the height inequality
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

open scoped OddOrder.Conjugation

variable {R : Type*} [CommRing R] {G : Type*} [Group G]
variable {E : Type*} [Ring E] [Algebra R E] {M : Type*} [AddCommMonoid M]

/-- **A symmetric additive map applied to a representation is a class function.**  Conjugation in
`R[G]` becomes conjugation by the unit `ψ (single g 1)` in `E`, which `τ` cannot see. -/
theorem symmMap_comp_conj (ψ : MonoidAlgebra R G →ₐ[R] E) (τ : E →+ M)
    (hτ : ∀ x y : E, τ (x * y) = τ (y * x)) (g : G) (a : MonoidAlgebra R G) :
    τ (ψ (g • a)) = τ (ψ a) := by
  have hvu : ψ (single g⁻¹ (1 : R)) * ψ (single g (1 : R)) = 1 := by
    rw [← map_mul, single_mul_single, one_mul, inv_mul_cancel, ← MonoidAlgebra.one_def, map_one]
  rw [smul_eq_conj, map_mul ψ, map_mul ψ, hτ, ← mul_assoc, hvu, one_mul]

variable [Finite G]

/-- **The character of a relative trace is the index times the character.** -/
theorem symmMap_relTrace (ψ : MonoidAlgebra R G →ₐ[R] E) (τ : E →+ M)
    (hτ : ∀ x y : E, τ (x * y) = τ (y * x)) (K H : Subgroup G) (a : MonoidAlgebra R G) :
    τ (ψ (GAlgebra.relTrace K H a)) = (K.relIndex H) • τ (ψ a) :=
  GAlgebra.map_relTrace (τ.comp (ψ : MonoidAlgebra R G →+* E).toAddMonoidHom)
    (symmMap_comp_conj ψ τ hτ) K H a

variable {L : Type*} [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]

/-- **The height inequality.**  If `f` lies in the relative trace ideal `R[G]^H_K` and acts as the
identity in a representation `ψ` on a finite free module `L`, then `[H : K]` divides the degree
`χ(1) = rank L`.

For `f = f_B` a block idempotent, `K = D` a defect group and `H = ⊤` this is Brauer's inequality
`ν(χ(1)) ≥ ν(|G|) - d(B)`; see `index_dvd_finrank`. -/
theorem relIndex_dvd_finrank (ψ : MonoidAlgebra R G →ₐ[R] Module.End R L)
    {K H : Subgroup G} {f : MonoidAlgebra R G} (hf : f ∈ GAlgebra.relTraceIdeal K H)
    (hψ : ψ f = 1) : ((K.relIndex H : ℕ) : R) ∣ (Module.finrank R L : R) := by
  obtain ⟨a, -, rfl⟩ := hf
  refine ⟨LinearMap.trace R L (ψ a), ?_⟩
  have h := symmMap_relTrace ψ (LinearMap.trace R L).toAddMonoidHom
    (LinearMap.trace_mul_comm R) K H a
  simp only [LinearMap.toAddMonoidHom_coe] at h
  rw [hψ, LinearMap.trace_one] at h
  rw [h, nsmul_eq_mul]

/-- **The height inequality**, in the form used for blocks: `[G : D]` divides `χ(1)` when the
`G`-relative trace ideal `R[G]^G_D` contains an element acting as the identity. -/
theorem index_dvd_finrank (ψ : MonoidAlgebra R G →ₐ[R] Module.End R L)
    {D : Subgroup G} {f : MonoidAlgebra R G} (hf : f ∈ GAlgebra.relTraceIdeal D ⊤)
    (hψ : ψ f = 1) : ((D.index : ℕ) : R) ∣ (Module.finrank R L : R) := by
  rw [← Subgroup.relIndex_top_right]
  exact relIndex_dvd_finrank ψ hf hψ

end OddOrder.GroupAlgebra
