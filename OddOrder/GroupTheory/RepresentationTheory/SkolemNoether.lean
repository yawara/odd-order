/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Skolem–Noether for the endomorphism algebra of a finite-dimensional vector space

`OddOrder.GroupTheory.RepresentationTheory` shared module.  A `k`-algebra automorphism of
`End k W₀` (`W₀` a finite-dimensional vector space over a field `k`) is *inner*: it is conjugation
by a `k`-linear automorphism of `W₀`.  This is the matrix Skolem–Noether theorem (mathlib lacks a
general Skolem–Noether), specialised to the only shape **Bender–Glauberman Proposition 2.2(a)**
needs: the consequence that an automorphism whose fixed subalgebra is just the scalars forces
`finrank k W₀ ≤ 1` (the *multiplicity one* step that finishes `V_P` irreducible).

The argument is the standard one.  `End k W₀` is a simple Artinian ring, so all its simple modules
are isomorphic (`nonempty_linearEquiv_of_isSimpleModule`, from `IsSimpleRing.isIsotypic`).  Twisting
the standard module `W₀` by the automorphism `θ` gives another simple module, hence one isomorphic
to `W₀`; the isomorphism is a `k`-linear bijection `u` with `θ f = u ∘ f ∘ u⁻¹` for all `f`.  When
the fixed subalgebra of `θ` is the scalars, `u` (which `θ` fixes) is itself a scalar, so `θ = id`,
so `End k W₀` is the scalars, so `(finrank k W₀)² ≤ 1`.

## Main statements

* `nonempty_linearEquiv_of_isSimpleModule` — any two simple modules over a simple Artinian ring are
  isomorphic.
-/

namespace OddOrder.RepresentationTheory

open Module

section SimpleArtinian

/-- **All simple modules over a simple Artinian ring are isomorphic.**  Each simple module is
isomorphic to a minimal left ideal (`exists_linearEquiv_ideal_of_isSimpleModule`), and the simple
left ideals are mutually isomorphic because the ring, as a module over itself, is isotypic
(`IsSimpleRing.isIsotypic`). -/
theorem nonempty_linearEquiv_of_isSimpleModule
    {E : Type*} [Ring E] [IsSimpleRing E] [IsArtinianRing E]
    {A B : Type*} [AddCommGroup A] [Module E A] [IsSimpleModule E A]
    [AddCommGroup B] [Module E B] [IsSimpleModule E B] :
    Nonempty (A ≃ₗ[E] B) := by
  obtain ⟨I, ⟨eA⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule E A
  obtain ⟨J, ⟨eB⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule E B
  haveI : IsSimpleModule E I := IsSimpleModule.congr eA.symm
  haveI : IsSimpleModule E J := IsSimpleModule.congr eB.symm
  obtain ⟨eIJ⟩ := IsSimpleRing.isIsotypic E E I J
  exact ⟨eA.trans (eIJ.symm.trans eB.symm)⟩

end SimpleArtinian

section Twist

variable {k W₀ : Type*} [Field k] [AddCommGroup W₀] [Module k W₀]

/-- `W₀` carrying the `End k W₀`-module structure twisted by an algebra automorphism `θ`:
`f • w = θ f w`.  A type synonym so this twisted action does not clash with the standard one. -/
def EndTwist (_θ : End k W₀ ≃ₐ[k] End k W₀) : Type _ := W₀

namespace EndTwist

instance (θ : End k W₀ ≃ₐ[k] End k W₀) : AddCommGroup (EndTwist θ) :=
  inferInstanceAs (AddCommGroup W₀)

instance (θ : End k W₀ ≃ₐ[k] End k W₀) : Module k (EndTwist θ) :=
  inferInstanceAs (Module k W₀)

/-- The twisted `End k W₀`-action: `f` acts as `θ f`. -/
noncomputable instance instModuleEnd (θ : End k W₀ ≃ₐ[k] End k W₀) :
    Module (End k W₀) (EndTwist θ) :=
  Module.compHom (M := W₀) θ.toRingEquiv.toRingHom

theorem smul_def (θ : End k W₀ ≃ₐ[k] End k W₀) (f : End k W₀) (x : EndTwist θ) :
    f • x = (θ f) (show W₀ from x) := rfl

/-- Twisting by an automorphism preserves simplicity: the identity `EndTwist θ → W₀` is a
`θ`-semilinear bijection, so it transports the submodule lattice (and hence `IsSimpleOrder`). -/
theorem isSimpleModule (θ : End k W₀ ≃ₐ[k] End k W₀) [IsSimpleModule (End k W₀) W₀] :
    IsSimpleModule (End k W₀) (EndTwist θ) := by
  haveI : RingHomSurjective (θ.toRingEquiv.toRingHom) := ⟨θ.surjective⟩
  -- the identity, as a `θ`-semilinear bijection `EndTwist θ → W₀`
  let g : EndTwist θ →ₛₗ[θ.toRingEquiv.toRingHom] W₀ :=
    { toFun := fun x => (show W₀ from x)
      map_add' := fun _ _ => rfl
      map_smul' := fun f x => by
        change (show W₀ from f • x) = (θ f) • (show W₀ from x)
        rw [EndTwist.smul_def]; rfl }
  exact (g.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

end EndTwist

end Twist

section SkolemNoether

variable {k W₀ : Type*} [Field k] [AddCommGroup W₀] [Module k W₀] [FiniteDimensional k W₀]

/-- **Matrix Skolem–Noether, scalar-fixed form.**  If a `k`-algebra automorphism `θ` of `End k W₀`
(with `W₀` finite-dimensional over the field `k`) fixes *only* the scalar endomorphisms, then
`finrank k W₀ ≤ 1`.

This is the multiplicity-one engine of **Bender–Glauberman Proposition 2.2(a)**.  Skolem–Noether
(`End k W₀` is a simple Artinian ring, so its standard module `W₀` is the unique simple module up to
isomorphism — `nonempty_linearEquiv_of_isSimpleModule`) makes `θ` inner: the isomorphism `W₀ ≃ₗ`
(twist of `W₀` by `θ`) is conjugation by some `u ∈ GL(W₀)` with `θ = u.conjAlgEquiv k`.  Then `θ`
fixes `u` itself, so `u` is a scalar, so `θ = id`, so *every* endomorphism is fixed hence scalar;
`finrank k (End k W₀) = (finrank k W₀)² ≤ 1`. -/
theorem finrank_le_one_of_aut_fixedScalar
    (θ : End k W₀ ≃ₐ[k] End k W₀)
    (hfix : ∀ f : End k W₀, θ f = f → ∃ c : k, algebraMap k (End k W₀) c = f) :
    Module.finrank k W₀ ≤ 1 := by
  rcases subsingleton_or_nontrivial W₀ with _ | hnt
  · simp
  · -- `End k W₀` is simple Artinian (transport to a matrix ring over the field `k`).
    haveI : NeZero (Module.finrank k W₀) := ⟨Module.finrank_pos.ne'⟩
    haveI : Nonempty (Fin (Module.finrank k W₀)) := ⟨⟨0, Module.finrank_pos⟩⟩
    haveI : IsSimpleRing (End k W₀) :=
      IsSimpleRing.of_ringEquiv (algEquivMatrix (Module.finBasis k W₀)).symm.toRingEquiv
        inferInstance
    haveI : IsArtinianRing (End k W₀) := IsArtinianRing.of_finite k (End k W₀)
    haveI : IsSimpleModule (End k W₀) W₀ := inferInstance
    haveI : IsSimpleModule (End k W₀) (EndTwist θ) := EndTwist.isSimpleModule θ
    -- Skolem–Noether: `W₀ ≅ EndTwist θ` as `End k W₀`-modules.
    obtain ⟨e⟩ := nonempty_linearEquiv_of_isSimpleModule
      (E := End k W₀) (A := W₀) (B := EndTwist θ)
    -- `e` intertwines the standard and twisted actions: `e (f w) = θ f (e w)`.
    have key : ∀ (f : End k W₀) (w : W₀), (e (f • w) : W₀) = (θ f) (e w : W₀) := by
      intro f w
      have h := e.map_smul f w
      rwa [EndTwist.smul_def] at h
    -- package `e` as a `k`-linear automorphism `u` of `W₀`.
    set uMap : W₀ →ₗ[k] W₀ :=
      { toFun := fun w => (e w : W₀)
        map_add' := fun a b => map_add e a b
        map_smul' := fun c w => by
          have h := key (algebraMap k (End k W₀) c) w
          rw [θ.commutes] at h
          simpa [Module.algebraMap_end_apply] using h } with huMap
    have hubij : Function.Bijective uMap := e.bijective
    set u : W₀ ≃ₗ[k] W₀ := LinearEquiv.ofBijective uMap hubij with hu
    -- intertwining relation in terms of `u` (definitionally `e`).
    have keyU : ∀ (f : End k W₀) (w : W₀), u (f w) = (θ f) (u w) := fun f w => key f w
    -- `θ = u.conjAlgEquiv k`.
    have hθ : θ = u.conjAlgEquiv k := by
      refine AlgEquiv.ext fun f => LinearMap.ext fun w => ?_
      rw [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      change (θ f) w = u (f (u.symm w))
      rw [keyU f (u.symm w), u.apply_symm_apply]
    -- `θ` fixes `u` (conjugation by `u` fixes `u`), so `u` is a scalar `c • id`.
    have hu_fix : θ (u : W₀ →ₗ[k] W₀) = (u : W₀ →ₗ[k] W₀) := by
      rw [hθ, LinearEquiv.conjAlgEquiv_apply]
      refine LinearMap.ext fun w => ?_
      simp
    obtain ⟨c, hc⟩ := hfix (u : W₀ →ₗ[k] W₀) hu_fix
    have hcu : (u : W₀ →ₗ[k] W₀) = algebraMap k (End k W₀) c := hc.symm
    have h2 : ∀ v, u v = c • v := fun v => by
      have := congrArg (fun g : End k W₀ => g v) hcu
      simpa [Module.algebraMap_end_apply] using this
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨w, hw⟩ := exists_ne (0 : W₀)
      exact hw (u.injective (by rw [map_zero, h2 w, zero_smul]))
    -- hence `θ = id`: conjugation by the scalar `c • id` is trivial.
    have hθid : ∀ f : End k W₀, θ f = f := by
      intro f
      rw [hθ, LinearEquiv.conjAlgEquiv_apply]
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change u (f (u.symm w)) = f w
      have h3 : u.symm w = c⁻¹ • w := by
        apply u.injective
        rw [u.apply_symm_apply, h2, smul_smul, mul_inv_cancel₀ hc0, one_smul]
      rw [h3, map_smul, h2, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    -- every endomorphism is scalar, so `finrank (End k W₀) ≤ 1`, so `(finrank W₀)² ≤ 1`.
    have hsurj : Function.Surjective (Algebra.linearMap k (End k W₀)) := fun f =>
      hfix f (hθid f)
    have hle : Module.finrank k (End k W₀) ≤ 1 := by
      have := LinearMap.finrank_le_finrank_of_surjective hsurj
      simpa using this
    rw [Module.finrank_linearMap] at hle
    nlinarith [Module.finrank_pos (R := k) (M := W₀), hle]

end SkolemNoether

end OddOrder.RepresentationTheory
