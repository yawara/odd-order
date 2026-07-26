/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# The scalar character of a line (a `1`-dimensional `𝔽_p`-representation)

The σ-theory foundation (issue 9000, step 2) for the *non-Galois* branch of Peterfalvi (9.7)(a).
The `psi` embedding of `PFsection9.v:442` is built from the **block scalar characters** `φ_w`, one
for each imprimitivity block `H1^w` (an `𝔽_p`-line permuted by `W₁`).  Each `φ_w` is the character
by which `U` acts on the line `H1^w`.

This file supplies the **generic extraction** underlying every such `φ_w`: any action of a group `U`
on a `1`-dimensional `𝔽_p`-space `V` is by scalars, since every endomorphism of a line is a
homothety (`𝔽_p ≃+* End_{𝔽_p}(V)`), so `U` maps to `𝔽_p^×`:

* `lineScalarChar ρ hdim : U →* (ZMod p)ˣ` — the scalar character;
* `lineScalarChar_smul` — its defining property `ρ u x = φ u • x`;
* `card_dvd_sub_one_of_faithful_line` — a faithful line action embeds `U ↪ 𝔽_p^×`, so `|U| ∣ p − 1`.

The block engine `SemilinearImprimitiveBound.card_le_pow_of_block_scalars` consumes a family of such
characters `φ : Fin (n+1) → (Ū →* (ZMod p)ˣ)`; this file is the bridge from the imprimitive
`𝔽_p`-module decomposition (each block a line) to that family.  It also generalizes the private
homothety extraction of `ExtraspecialSinger` (route B, `|K| ∣ p − 1`).
-/

namespace OddOrder.RepresentationTheory

variable {p : ℕ} [Fact p.Prime] {U V : Type*} [Group U] [AddCommGroup V] [Module (ZMod p) V]

/-- **Homotheties of a line**: the ring isomorphism `𝔽_p ≃+* End_{𝔽_p}(V)` for a `1`-dimensional
`𝔽_p`-space `V`.  Every endomorphism of a line is a scalar
(`LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one`), so the algebra map `𝔽_p → End V` (injective
because `𝔽_p` is a field and `End V` is nontrivial) is also surjective, hence a ring isomorphism. -/
noncomputable def lineEndEquiv (hdim : Module.finrank (ZMod p) V = 1) :
    ZMod p ≃+* Module.End (ZMod p) V :=
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  RingEquiv.ofBijective (algebraMap (ZMod p) (Module.End (ZMod p) V))
    ⟨(algebraMap (ZMod p) (Module.End (ZMod p) V)).injective, fun u => by
      obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim u
      exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc, Module.End.one_eq_id]⟩⟩

@[simp] theorem lineEndEquiv_apply (hdim : Module.finrank (ZMod p) V = 1) (c : ZMod p) :
    lineEndEquiv (V := V) hdim c = algebraMap (ZMod p) (Module.End (ZMod p) V) c := rfl

/-- **The scalar character of a line** (the generic `φ_w` of Peterfalvi (9.7)(a)'s `psi`): a group
`U` acting on a `1`-dimensional `𝔽_p`-space `V` acts by scalars, giving `φ : U →* 𝔽_p^×`.

Composes the units functor of the homothety isomorphism `(𝔽_p)ˣ ≃ End(V)ˣ` (via `lineEndEquiv`) with
`ρ` viewed as a hom into `End(V)ˣ` (`ρ u` is invertible as `u` is a group element). -/
noncomputable def lineScalarChar (ρ : Representation (ZMod p) U V)
    (hdim : Module.finrank (ZMod p) V = 1) : U →* (ZMod p)ˣ :=
  (Units.map (lineEndEquiv (V := V) hdim).symm.toMulEquiv.toMonoidHom).comp
    (MonoidHom.toHomUnits ρ)

/-- **Defining property of the scalar character**: `U` acts on the line `V` through
`lineScalarChar`, i.e. `ρ u x = φ u • x`.  This turns the abstract character `φ` back into the
concrete scalar action, e.g. to discharge the "no global scalar" hypothesis of the block engine. -/
theorem lineScalarChar_smul (ρ : Representation (ZMod p) U V)
    (hdim : Module.finrank (ZMod p) V = 1) (u : U) (x : V) :
    ρ u x = (lineScalarChar ρ hdim u : ZMod p) • x := by
  have hval : ((lineScalarChar ρ hdim u : (ZMod p)ˣ) : ZMod p)
      = (lineEndEquiv (V := V) hdim).symm (ρ u) := by
    simp only [lineScalarChar, MonoidHom.comp_apply, Units.coe_map, MulEquiv.coe_toMonoidHom,
      MonoidHom.coe_toHomUnits]
    rfl
  have key : (lineEndEquiv (V := V) hdim) (lineScalarChar ρ hdim u : ZMod p) = ρ u := by
    rw [hval, RingEquiv.apply_symm_apply]
  calc (ρ u) x
      = (lineEndEquiv (V := V) hdim) (lineScalarChar ρ hdim u : ZMod p) x := by rw [key]
    _ = algebraMap (ZMod p) (Module.End (ZMod p) V) (lineScalarChar ρ hdim u : ZMod p) x := by
        rw [lineEndEquiv_apply]
    _ = (lineScalarChar ρ hdim u : ZMod p) • x := by rw [Module.algebraMap_end_apply]

/-- **Kernel of the scalar character = pointwise stabilizer of the line**: `φ u = 1` iff `u` fixes
`V` pointwise.  For an order-`p` block this is exactly "`u` fixes a nontrivial character of the
block iff `u` centralizes the block" — the free action of `𝔽_p^×` on the line — so it discharges the
order-`p` stabilizer/centralizer identifications of Peterfalvi (9.5)/(9.8) (Coq `inertia_irr_prime`,
`PFsection9.v:948`). -/
theorem lineScalarChar_eq_one_iff (ρ : Representation (ZMod p) U V)
    (hdim : Module.finrank (ZMod p) V = 1) (u : U) :
    lineScalarChar ρ hdim u = 1 ↔ ∀ x : V, ρ u x = x := by
  constructor
  · intro h x
    rw [lineScalarChar_smul ρ hdim u x, h, Units.val_one, one_smul]
  · intro h
    haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hsx : ((lineScalarChar ρ hdim u : ZMod p) - 1) • x = 0 := by
      rw [sub_smul, one_smul, ← lineScalarChar_smul ρ hdim u x, h x, sub_self]
    rcases smul_eq_zero.mp hsx with hc | hx0
    · have hval : (lineScalarChar ρ hdim u : ZMod p) = 1 := sub_eq_zero.mp hc
      exact Units.ext (by rw [hval, Units.val_one])
    · exact absurd hx0 hx

/-- **Transport of the scalar character along an equivariant isomorphism of lines.**  If a linear
isomorphism `e : V ≃ₗ W` intertwines `ρ` with `ρ'` up to a reindexing `σ` of the acting group
(`e (ρ u x) = ρ' (σ u) (e x)`), then the two scalar characters agree: `φ_V u = φ_W (σ u)`.

This is what makes Peterfalvi (9.7)(a)'s constant `a` independent of the block.  The blocks are the
`W₁`-translates `H_i = H₁^{w_i}`; translation by `w_i` is such an isomorphism, with `σ` the
conjugation automorphism `u ↦ w_i⁻¹ u w_i` of `U`.  Hence `im φ_{H_i} = im φ_{H₁}` for every `i`,
and the common order is the book's `a = |U : C_U(H₁)|` (issue 0152). -/
theorem lineScalarChar_comp_of_equivariant {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) U V) (ρ' : Representation (ZMod p) U W)
    (hdim : Module.finrank (ZMod p) V = 1) (hdim' : Module.finrank (ZMod p) W = 1)
    (e : V ≃ₗ[ZMod p] W) (σ : U →* U)
    (he : ∀ (u : U) (x : V), e (ρ u x) = ρ' (σ u) (e x)) (u : U) :
    lineScalarChar ρ hdim u = lineScalarChar ρ' hdim' (σ u) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hex : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
  have h1 : ρ' (σ u) (e x) = (lineScalarChar ρ hdim u : ZMod p) • e x := by
    rw [← he u x, lineScalarChar_smul ρ hdim u x, map_smul]
  have h2 : ρ' (σ u) (e x) = (lineScalarChar ρ' hdim' (σ u) : ZMod p) • e x :=
    lineScalarChar_smul ρ' hdim' (σ u) (e x)
  have hsub : ((lineScalarChar ρ hdim u : ZMod p)
      - (lineScalarChar ρ' hdim' (σ u) : ZMod p)) • e x = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  rcases smul_eq_zero.mp hsub with hc | h0
  · exact Units.ext (sub_eq_zero.mp hc)
  · exact absurd h0 hex

/-- **The block-scalar image does not depend on the block.**  Under an equivariant isomorphism of
lines whose reindexing `σ` is onto (conjugation by a group element is), the two scalar characters
have the same range.

This is Peterfalvi (9.7)(a)'s "`U/C_U(H_i)` is cyclic of order `a` **for all `i`**": the common
range is a subgroup of the cyclic group `𝔽_p^×`, so it is cyclic, and its order `a` divides
`p − 1`.  Feeding this common range to `card_dvd_blockScalarOrder_pow_of_blocks` gives the book's
`|U| ∣ a^{q−1}` in place of the coarser `|U| ∣ (p−1)^{q−1}` (issue 0152). -/
theorem lineScalarChar_range_eq_of_equivariant {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) U V) (ρ' : Representation (ZMod p) U W)
    (hdim : Module.finrank (ZMod p) V = 1) (hdim' : Module.finrank (ZMod p) W = 1)
    (e : V ≃ₗ[ZMod p] W) (σ : U →* U) (hσ : Function.Surjective σ)
    (he : ∀ (u : U) (x : V), e (ρ u x) = ρ' (σ u) (e x)) :
    (lineScalarChar ρ hdim).range = (lineScalarChar ρ' hdim').range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    exact ⟨σ u, (lineScalarChar_comp_of_equivariant ρ ρ' hdim hdim' e σ he u).symm⟩
  · rintro _ ⟨w, rfl⟩
    obtain ⟨u, rfl⟩ := hσ w
    exact ⟨u, lineScalarChar_comp_of_equivariant ρ ρ' hdim hdim' e σ he u⟩

/-- The scalar character of a **faithful** line action is injective: distinct group elements act by
distinct scalars.  (`ρ` injective and `ρ u x = φ u • x` force `φ` injective.) -/
theorem lineScalarChar_injective (ρ : Representation (ZMod p) U V)
    (hdim : Module.finrank (ZMod p) V = 1) (hfaith : Function.Injective ρ) :
    Function.Injective (lineScalarChar ρ hdim) := by
  intro a b hab
  apply hfaith
  refine LinearMap.ext fun x => ?_
  rw [lineScalarChar_smul ρ hdim a x, lineScalarChar_smul ρ hdim b x, hab]

/-- **Faithful line bound** (the split-torus case of Peterfalvi (9.7), generalizing
`ExtraspecialSinger`'s route B): a finite group acting faithfully on a `1`-dimensional `𝔽_p`-space
embeds into `𝔽_p^×`, so `|U| ∣ p − 1`. -/
theorem card_dvd_sub_one_of_faithful_line [Finite U] (ρ : Representation (ZMod p) U V)
    (hdim : Module.finrank (ZMod p) V = 1) (hfaith : Function.Injective ρ) :
    Nat.card U ∣ p - 1 :=
  calc Nat.card U = Nat.card (lineScalarChar ρ hdim).range :=
        Nat.card_congr (MonoidHom.ofInjective (lineScalarChar_injective ρ hdim hfaith)).toEquiv
    _ ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]

/-- **An `𝔽_p`-module of cardinality `p` is a line** (`finrank = 1`).  The bridge from the
concrete "block has order `p`" that a caller (e.g. the Pf (9.7)(a) imprimitive block decomposition)
has, to the `finrank = 1` hypothesis of `lineScalarChar`. -/
theorem finrank_eq_one_of_card_eq_prime {p : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (hcard : Nat.card V = p) :
    Module.finrank (ZMod p) V = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcardZ : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hpow : Nat.card V = Nat.card (ZMod p) ^ Module.finrank (ZMod p) V :=
    Module.natCard_eq_pow_finrank
  rw [hcard, hcardZ] at hpow
  have h1 : p ^ 1 = p ^ Module.finrank (ZMod p) V := by rw [pow_one]; exact hpow
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm

end OddOrder.RepresentationTheory
