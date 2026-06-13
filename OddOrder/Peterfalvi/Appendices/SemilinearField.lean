/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.RingTheory.LittleWedderburn

/-!
# Peterfalvi, Appendix I (= Appendix B), Proposition 2 — the field structure

(Peterfalvi, *Character Theory for the Odd Order Theorem*, Appendix I, pp. 135-136.)

**Proposition 2.** Let `U` act faithfully on an elementary abelian group `E` of order `pⁿ`,
and let `T ⊴ U` be a *cyclic normal* subgroup acting *irreducibly* on `E`.
* (a) `F = 𝔽_p[T] ⊆ End(E)` is a field with `pⁿ` elements, and `E` is `1`-dimensional over `F`.
* (b) `U` is a group of semilinear maps of this `F`-line; for `s ∈ E^#`, `C_U(s)` embeds into
  `Aut(F)` (the field automorphisms).

This file establishes the *core* of part (a), stated over an abstract finite simple module `M`
over the group algebra `k[T]` of a commutative group `T` over a finite field `k` (so as to keep
the `k[T]`-module instances honest — see `notes/peterfalvi/appendices.md` session 5 for the
instance gotchas that force this abstraction).  The endomorphism ring `D = End_{k[T]}(M)` is:

* a **field** (Schur's Lemma `⟹` division ring, finite `⟹` Wedderburn), `endField`;
* over which `M` is **simple**, `isSimpleModule_end` — because the `k[T]`-scalar maps land in
  `D` (commutativity, via `LinearMap.lsmul`), so every `D`-submodule is a `k[T]`-submodule;
* hence `M` is `1`-dimensional, `finrank_end_eq_one`, and `|D| = |M|`, `natCard_end_eq`.

The bridge from the textbook data `(E, φ : U →* MulAut E, T)` to this core (building
`M := ρ.asModule` for `ρ = (mulAutToEnd E p).comp φ|_T`) and part (b) are developed separately.
-/

namespace OddOrder.Peterfalvi.Appendices.Huppert

open scoped Classical

section Prop2Core

variable {k : Type*} [CommRing k] {T : Type*} [CommGroup T] [Finite T]
  {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra k T) M] [Finite M]

/-- `End_{k[T]}(M)` is finite (it injects into the finite function space `M → M`). -/
instance : Finite (Module.End (MonoidAlgebra k T) M) :=
  Finite.of_injective _ DFunLike.coe_injective

variable [IsSimpleModule (MonoidAlgebra k T) M]

/-- **Schur + Wedderburn**: the endomorphism ring of a finite simple `k[T]`-module is a field.
(Schur makes it a division ring, `Module.End` instance; finite division rings are fields,
`littleWedderburn`.)  The instance is also found automatically; this names it. -/
noncomputable def endField : Field (Module.End (MonoidAlgebra k T) M) := inferInstance

/-- `M` is simple as a module over `D = End_{k[T]}(M)`.

Because `k[T]` is commutative, each scalar map `m ↦ r • m` (`r ∈ k[T]`) is `k[T]`-linear, i.e.
lies in `D` (`LinearMap.lsmul`).  Hence every `D`-submodule of `M` is closed under the
`k[T]`-action, i.e. is a `k[T]`-submodule; as `M` is `k[T]`-simple, it has no proper nonzero
`D`-submodules either. -/
theorem isSimpleModule_end :
    IsSimpleModule (Module.End (MonoidAlgebra k T) M) M := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial (MonoidAlgebra k T) M
  refine { eq_bot_or_eq_top := fun N => ?_ }
  -- the carrier of the `D`-submodule `N` is a `k[T]`-submodule
  let N' : Submodule (MonoidAlgebra k T) M :=
    { carrier := (N : Set M)
      add_mem' := fun ha hb => N.add_mem ha hb
      zero_mem' := N.zero_mem
      smul_mem' := fun r m hm => by
        have h : (LinearMap.lsmul (MonoidAlgebra k T) M r) • m ∈ N := N.smul_mem _ hm
        rwa [Module.End.smul_def, LinearMap.lsmul_apply] at h }
  have hmem : ∀ x, x ∈ N ↔ x ∈ N' := fun _ => Iff.rfl
  rcases eq_bot_or_eq_top N' with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    exact fun x hx => h x ((hmem x).mp hx)
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    exact fun x => (hmem x).mpr (h x)

/-- `M` is `1`-dimensional over the field `D = End_{k[T]}(M)` (`isSimpleModule_end` + the
classification of simple modules over a division ring). -/
theorem finrank_end_eq_one :
    Module.finrank (Module.End (MonoidAlgebra k T) M) M = 1 :=
  isSimpleModule_iff_finrank_eq_one.mp isSimpleModule_end

/-- `|End_{k[T]}(M)| = |M|`: as `M` is a `1`-dimensional `D`-space, `|M| = |D|¹`. -/
theorem natCard_end_eq :
    Nat.card (Module.End (MonoidAlgebra k T) M) = Nat.card M := by
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype (Module.End (MonoidAlgebra k T) M) := Fintype.ofFinite _
  have h : Fintype.card M =
      Fintype.card (Module.End (MonoidAlgebra k T) M) ^
        Module.finrank (Module.End (MonoidAlgebra k T) M) M :=
    Module.card_eq_pow_finrank
  rw [finrank_end_eq_one, pow_one] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h.symm

end Prop2Core

end OddOrder.Peterfalvi.Appendices.Huppert
