/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Conjugation permutes the simple constituents of a restriction (general field)

`OddOrder.GroupTheory.RepresentationTheory` shared module: the field-agnostic, module-theoretic
core of Clifford's theorem, the first ingredient of **Bender–Glauberman Proposition 2.2(a)**
(`V_P` irreducible, the algebraically-closed Clifford step of Theorem 2.5).

For a representation `ρ : Representation k G V` over an arbitrary field `k`, a normal subgroup
`H ⊴ G`, and `g : G`, conjugation by `g` (realised by the `k`-linear bijection `ρ g`) sends every
simple `k[H]`-submodule of the restriction `(ρ.comp H.subtype).asModule` to another simple
`k[H]`-submodule.  This is normality at the module level: `ρ g` intertwines the `H`-action up to
the conjugation twist `h ↦ g h g⁻¹`, so it is *semilinear* over the induced ring automorphism of
`k[H]`, and a semilinear bijection transports simplicity across the submodule lattice.

This mirrors the `ℂ`-specialised development in `Clifford.lean` (`conjBySimpleSemilinear`,
`isSimpleModule_map_conjBySimpleSemilinear`) but works over **any field `k`** — required because
BG Theorem 2.5 base-changes to the algebraic closure `F*`, whose characteristic is unconstrained.
No irreducibility of `ρ` and no algebraic closedness is needed here: `ρ g` is always a bijection.

## Main statements

* `conjNormalMulAut` — the automorphism `h ↦ g h g⁻¹` of a normal subgroup `H`.
* `conjMonoidAlgRingHom` — the induced ring automorphism of `k[H]`.
* `conjSemilinearEnd` — `ρ g`, packaged as a `conjMonoidAlgRingHom`-semilinear endomorphism of
  the restricted module.
* `isSimpleModule_map_conjSemilinearEnd` — the image of a simple `k[H]`-submodule under `ρ g` is
  again a simple `k[H]`-submodule.
-/

namespace OddOrder.RepresentationTheory

open Representation
open scoped MonoidAlgebra

variable {G : Type*} [Group G]

/-- The automorphism `h ↦ g h g⁻¹` of a normal subgroup `H` induced by conjugation by `g ∈ G`. -/
noncomputable def conjNormalMulAut (H : Subgroup G) [H.Normal] (g : G) : H ≃* H :=
  (MulEquiv.subgroupMap (MulAut.conj g) H).trans
    (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g H))

@[simp]
theorem conjNormalMulAut_apply_coe (H : Subgroup G) [H.Normal] (g : G) (h : H) :
    (conjNormalMulAut H g h : G) = g * (h : G) * g⁻¹ := rfl

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

section ConjBySimple

variable (ρ : Representation k G V) (H : Subgroup G) [hH : H.Normal]

/-- The restriction `Res^G_H ρ`, packaged as a `Representation k ↥H V` (rather than the bare
`MonoidHom` `ρ.comp H.subtype`) so that its `k[H]`-module `asModule` is available.  A reducible
abbreviation, so the `k[H]`-module instance is found by unfolding to `(ρ.comp H.subtype).asModule`.

(Distinct name from `Representation.restrictRep` in the `ℂ`-pinned `Clifford.lean`.) -/
abbrev resRep : Representation k ↥H V := ρ.comp H.subtype

omit hH in
@[simp] theorem resRep_apply (h : ↥H) : resRep ρ H h = ρ (h : G) := rfl

variable {H}

/-- The ring automorphism of `k[H]` induced by conjugation `h ↦ g h g⁻¹` on the normal subgroup
`H`.  On generators it sends `single h c` to `single (g h g⁻¹) c`. -/
noncomputable def conjMonoidAlgRingHom (g : G) : k[↥H] →+* k[↥H] :=
  MonoidAlgebra.mapDomainRingHom k (conjNormalMulAut H g).toMonoidHom

theorem conjMonoidAlgRingHom_single (g : G) (h : ↥H) (c : k) :
    conjMonoidAlgRingHom (k := k) (H := H) g (MonoidAlgebra.single h c) =
      MonoidAlgebra.single (conjNormalMulAut H g h) c := by
  simp [conjMonoidAlgRingHom]

theorem conjMonoidAlgRingHom_surjective (g : G) :
    Function.Surjective (conjMonoidAlgRingHom (k := k) (H := H) g) :=
  (MonoidAlgebra.mapDomainRingEquiv k (conjNormalMulAut H g)).surjective

instance conjMonoidAlgRingHom_isSurjective (g : G) :
    RingHomSurjective (conjMonoidAlgRingHom (k := k) (H := H) g) :=
  ⟨conjMonoidAlgRingHom_surjective (k := k) (H := H) g⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `k`-linear bijection `ρ g`, packaged as a `conjMonoidAlgRingHom g`-semilinear endomorphism
of the restricted module `(resRep ρ H).asModule`.

This is the module-theoretic incarnation of normality: for `h ∈ H`, the standard `k[H]`-action on
the image satisfies `h • (ρ g v) = ρ g (ρ (g⁻¹ h g) v)`, i.e. `ρ g` intertwines the `H`-action up
to the conjugation twist `conjMonoidAlgRingHom g`. -/
noncomputable def conjSemilinearEnd (g : G) :
    (resRep ρ H).asModule →ₛₗ[conjMonoidAlgRingHom (k := k) (H := H) g]
      (resRep ρ H).asModule where
  toFun v := (show (resRep ρ H).asModule from ρ g v)
  map_add' v w := by simp
  map_smul' s v := by
    induction s using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
        change ρ g ((x + y) • v) = _
        rw [add_smul, map_add, map_add, add_smul]
        exact congrArg₂ (· + ·) hx hy
    | single h c =>
        have hHh : (conjNormalMulAut H g h : G) = g * (h : G) * g⁻¹ := rfl
        rw [conjMonoidAlgRingHom_single]
        change ρ g (MonoidAlgebra.single h c • v) =
          MonoidAlgebra.single (conjNormalMulAut H g h) c •
            (show (resRep ρ H).asModule from ρ g v)
        rw [Representation.single_smul, Representation.single_smul, resRep_apply,
          resRep_apply, map_smul]
        congr 1
        change ρ g (ρ (h : G) v) = ρ ((conjNormalMulAut H g h : G)) (ρ g v)
        rw [hHh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group

@[simp] theorem conjSemilinearEnd_apply (g : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ g v = (show (resRep ρ H).asModule from ρ g v) :=
  rfl

theorem conjSemilinearEnd_bijective (g : G) :
    Function.Bijective (conjSemilinearEnd (H := H) ρ g) :=
  ρ.apply_bijective g

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the image submodule `N.map (conjSemilinearEnd ρ g)` is exactly being of the form
`ρ g v` for `v ∈ N`: the image is, as a set, the `ρ g`-translate of `N`, carrying the standard
`k[H]`-action `h • w = ρ (h : G) w`. -/
theorem mem_map_conjSemilinearEnd (g : G)
    (N : Submodule k[↥H] (resRep ρ H).asModule) (w : (resRep ρ H).asModule) :
    w ∈ N.map (conjSemilinearEnd (H := H) ρ g) ↔
      ∃ v ∈ N, (show (resRep ρ H).asModule from ρ g v) = w := by
  simp only [Submodule.mem_map, conjSemilinearEnd_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Conjugation permutes simple constituents** (module core of Clifford's theorem; the first
ingredient of BG Prop 2.2(a)).  For `ρ : Representation k G V` over any field `k`, `H ⊴ G`, a simple
`k[H]`-submodule `N` of the restriction `(resRep ρ H).asModule`, and any `g : G`, the image of
`N` under `ρ g` is again a simple `k[H]`-submodule.

The image is `N.map (conjSemilinearEnd ρ g)`, with `h • (ρ g v) = ρ g (ρ (g⁻¹ h g) v)` (normality of
`H`).  Simplicity is transported across the semilinear bijection `ρ g` via the order isomorphism of
submodule lattices it induces (`Submodule.orderIsoMapComapOfBijective`), as `IsSimpleModule` is
equivalent to the submodule being an atom (`isSimpleModule_iff_isAtom`).

No irreducibility of `ρ` and no algebraic closedness is needed: `ρ g` is always a bijection. -/
theorem isSimpleModule_map_conjSemilinearEnd
    (g : G) (N : Submodule k[↥H] (resRep ρ H).asModule)
    [IsSimpleModule k[↥H] N] :
    IsSimpleModule k[↥H]
      (N.map (conjSemilinearEnd (H := H) ρ g) :
        Submodule k[↥H] (resRep ρ H).asModule) := by
  have hatomN : IsAtom N := IsSimpleModule.isAtom
  have hmap : (Submodule.orderIsoMapComapOfBijective
      (conjSemilinearEnd (H := H) ρ g)
      (conjSemilinearEnd_bijective (H := H) ρ g)) N =
      N.map (conjSemilinearEnd (H := H) ρ g) := rfl
  rw [isSimpleModule_iff_isAtom, ← hmap]
  exact (OrderIso.isAtom_iff _ N).mpr hatomN

/-- **The final step of BG Prop 2.2(a).** If `ρ` is irreducible and `W` is a nonzero
`k[H]`-submodule of the restriction `(resRep ρ H).asModule` that is `G`-invariant (stable under
every `ρ g`, expressed via `conjSemilinearEnd`), then `W = ⊤`.  A `G`-invariant `k[H]`-submodule is
the carrier of a
`Subrepresentation ρ`, so irreducibility (`IsSimpleOrder (Subrepresentation ρ)`) forces it to be `⊥`
or `⊤`; nonzero rules out `⊥`. -/
theorem eq_top_of_forall_map_conjSemilinearEnd_le
    [ρ.IsIrreducible] (W : Submodule k[↥H] (resRep ρ H).asModule) (hW : W ≠ ⊥)
    (hinv : ∀ g : G, W.map (conjSemilinearEnd (H := H) ρ g) ≤ W) :
    W = ⊤ := by
  -- `W`, being `G`-invariant, is the carrier of a `Subrepresentation ρ`
  let Wρ : Subrepresentation ρ :=
    { toSubmodule := W.restrictScalars k
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : v ∈ W := hv
        have : (show (resRep ρ H).asModule from ρ g v) ∈ W :=
          hinv g (Submodule.mem_map_of_mem hv')
        exact this }
  rcases IsSimpleOrder.eq_bot_or_eq_top Wρ with hbot | htop
  · -- `Wρ = ⊥` forces `W = ⊥`, contradicting `hW`
    have h0 : W.restrictScalars k = ⊥ := congrArg Subrepresentation.toSubmodule hbot
    refine absurd (eq_bot_iff.mpr fun v hv => ?_) hW
    have hv' : v ∈ W.restrictScalars k := hv
    rw [h0] at hv'
    simpa using hv'
  · -- `Wρ = ⊤` gives `W = ⊤`
    have h1 : W.restrictScalars k = ⊤ := congrArg Subrepresentation.toSubmodule htop
    refine eq_top_iff.mpr fun v _ => ?_
    have hv' : v ∈ W.restrictScalars k := h1 ▸ Submodule.mem_top
    exact hv'

end ConjBySimple

end OddOrder.RepresentationTheory
