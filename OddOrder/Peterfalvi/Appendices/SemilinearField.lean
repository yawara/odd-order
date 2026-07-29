/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke
import OddOrder.Algebra.SemilinearFixedPoint
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
the `k[T]`-module instances honest — see `notes/peterfalvi/appendices.md (削除済, git履歴)` session 5 for
the
instance gotchas that force this abstraction).  The endomorphism ring `D = End_{k[T]}(M)` is:

* a **field** (Schur's Lemma `⟹` division ring, finite `⟹` Wedderburn), `endField`;
* over which `M` is **simple**, `isSimpleModule_end` — because the `k[T]`-scalar maps land in
  `D` (commutativity, via `LinearMap.lsmul`), so every `D`-submodule is a `k[T]`-submodule;
* hence `M` is `1`-dimensional, `finrank_end_eq_one`, and `|D| = |M|`, `natCard_end_eq`.

The bridge from the textbook data `(E, φ : U →* MulAut E, T)` to this core (building
`M := ρ.asModule` for `ρ = (mulAutToEnd E p).comp φ|_T`) and part (b) are developed separately.
-/

namespace OddOrder.Peterfalvi.Appendices.Huppert

section Prop2Core

variable {k : Type*} [CommRing k] {T : Type*} [CommGroup T] [Finite T]
  {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra k T) M] [Finite M]

omit [Finite T] in
/-- `End_{k[T]}(M)` is finite (it injects into the finite function space `M → M`).

⚠ Deliberately **not** a global instance: an unconstrained
`Finite (Module.End (MonoidAlgebra k T) M)`
instance interferes with `Representation.asModule` `Module`-synthesis when `[IsIrreducible ρ]` is in
scope (the Schur→Wedderburn chain pulls it into unrelated searches).  Provided locally via `haveI`
in the theorems that need the field structure. -/
theorem finite_end : Finite (Module.End (MonoidAlgebra k T) M) :=
  Finite.of_injective _ DFunLike.coe_injective

variable [IsSimpleModule (MonoidAlgebra k T) M]

open scoped Classical in
/-- **Schur + Wedderburn**: the endomorphism ring of a finite simple `k[T]`-module is a field.
(Schur makes it a division ring, `Module.End` instance; finite division rings are fields,
`littleWedderburn`.) -/
@[reducible]
noncomputable def endField : Field (Module.End (MonoidAlgebra k T) M) :=
  haveI := finite_end (k := k) (T := T) (M := M); inferInstance

omit [Finite T] in
omit [Finite M] in
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

omit [Finite T] in
omit [Finite M] in
open scoped Classical in
/-- `M` is `1`-dimensional over the field `D = End_{k[T]}(M)` (`isSimpleModule_end` + the
classification of simple modules over a division ring). -/
theorem finrank_end_eq_one :
    Module.finrank (Module.End (MonoidAlgebra k T) M) M = 1 :=
  isSimpleModule_iff_finrank_eq_one.mp isSimpleModule_end

omit [Finite T] in
open scoped Classical in
/-- `|End_{k[T]}(M)| = |M|`: as `M` is a `1`-dimensional `D`-space, `|M| = |D|¹`. -/
theorem natCard_end_eq :
    Nat.card (Module.End (MonoidAlgebra k T) M) = Nat.card M := by
  haveI := finite_end (k := k) (T := T) (M := M)
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

section Prop2Bridge

open OddOrder.GroupTheory OddOrder.BG.Ch1_Preliminary OddOrder.Isaacs.Ch03

open scoped Classical in
/-- **Peterfalvi, Appendix I, Proposition 2(a)** (textbook form).  Let the commutative group `T`
act on the elementary abelian `p`-group `E`, *irreducibly* (every `T`-invariant subgroup of `E`
is `⊥` or `⊤`).  Then there is a finite field `F` acting on `E` (written additively) over which
`E` is a `1`-dimensional vector space, and `|F| = |E|` (so `F ≅ 𝔽_{pⁿ}` where `|E| = pⁿ`).

Concretely `F = 𝔽_p[T] = End_{𝔽_p[T]}(E)`.  The proof builds the `𝔽_p[T]`-module structure on
`Additive E` directly via `Module.compHom` (avoiding the `Representation.asModule` wrapper, whose
`Module` instance is fragile in argument position), translates `T`-invariant subgroups to
`𝔽_p[T]`-submodules to get `IsSimpleModule`, and applies the abstract core. -/
theorem exists_field_of_irreducible.{u} {p : ℕ} [Fact p.Prime] {E : Type u} [CommGroup E]
    [Finite E] [Nontrivial E] (hE : IsElementaryAbelian p E) {T : Type*} [CommGroup T] [Finite T]
    (ψ : T →* MulAut E)
    (hirr : ∀ U : Subgroup E, IsAInvariant ψ U → U = ⊥ ∨ U = ⊤) :
    ∃ (F : Type u) (_ : Field F) (_ : Module F (Additive E)) (_ : Finite F),
      Module.finrank F (Additive E) = 1 ∧ Nat.card F = Nat.card E := by
  haveI hEcomm : IsMulCommutative E := ⟨⟨mul_comm⟩⟩
  have hpsmul : ∀ x : Additive E, (p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hE.pow_eq_one x.toMul
  haveI : Module (ZMod p) (Additive E) := AddCommGroup.zmodModule hpsmul
  let ρ : Representation (ZMod p) T (Additive E) := (mulAutToEnd E p).comp ψ
  letI instKT : Module (MonoidAlgebra (ZMod p) T) (Additive E) :=
    Module.compHom (Additive E) ρ.asAlgebraHom.toRingHom
  have key : ∀ (t : T) (x : Additive E),
      (MonoidAlgebra.of (ZMod p) T t) • x = Additive.ofMul ((ψ t) (Additive.toMul x)) := by
    intro t x
    rw [show (MonoidAlgebra.of (ZMod p) T t) • x
          = ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) T t) x from rfl,
        Representation.asAlgebraHom_of]
    rfl
  haveI hsimp : IsSimpleModule (MonoidAlgebra (ZMod p) T) (Additive E) := by
    haveI : Nontrivial (Additive E) := inferInstanceAs (Nontrivial (Additive E))
    refine { eq_bot_or_eq_top := fun N => ?_ }
    let H : Subgroup E :=
      { carrier := {e : E | Additive.ofMul e ∈ N}
        one_mem' := by change Additive.ofMul (1 : E) ∈ N; rw [ofMul_one]; exact N.zero_mem
        mul_mem' := fun {a b} ha hb => by
          change Additive.ofMul (a * b) ∈ N
          rw [ofMul_mul]; exact N.add_mem ha hb
        inv_mem' := fun {a} ha => by
          change Additive.ofMul a⁻¹ ∈ N
          rw [ofMul_inv]; exact N.neg_mem ha }
    have hHinv : IsAInvariant ψ H := by
      rw [isAInvariant_iff_smul_mem]
      intro t a ha
      change Additive.ofMul ((ψ t) a) ∈ N
      have hmem : (MonoidAlgebra.of (ZMod p) T t) • (Additive.ofMul a) ∈ N :=
        N.smul_mem _ (show Additive.ofMul a ∈ N from ha)
      rw [key t (Additive.ofMul a)] at hmem
      exact hmem
    rcases hirr H hHinv with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxH : Additive.toMul x ∈ H := hx
      rw [h, Subgroup.mem_bot] at hxH
      change Additive.ofMul (Additive.toMul x) = 0
      rw [hxH, ofMul_one]
    · right
      rw [Submodule.eq_top_iff']
      intro x
      exact (by rw [h]; exact Subgroup.mem_top _ : Additive.toMul x ∈ H)
  refine ⟨Module.End (MonoidAlgebra (ZMod p) T) (Additive E),
    endField, Module.End.applyModule, finite_end, finrank_end_eq_one, ?_⟩
  exact natCard_end_eq.trans (Nat.card_congr Additive.toMul)

open scoped Classical in
/-- **Peterfalvi, Appendix I, Proposition 2(a)+(b)** (textbook form, with semilinearity).
In addition to the field `F` of part (a), every `g : MulAut E` that *normalizes* the `T`-action —
i.e. `ψ (c t) = g · ψ t · g⁻¹` for some `c : T ≃* T` — acts `F`-semilinearly on `E` (written
additively): there is a field automorphism `σ : F ≃+* F` with `g(a • x) = σ(a) • g(x)` for all
`a ∈ F`, `x ∈ E`.  (`σ` is conjugation by `g` on `F = End_{𝔽_p[T]}(E)`; that conjugation lands
back in `F` because `g` normalizes `T`.)  This is the input Appendix II (Near-Fields) uses to
produce the field automorphisms `σ_y`. -/
theorem exists_field_semilinear.{u} {p : ℕ} [Fact p.Prime] {E : Type u} [CommGroup E] [Finite E]
    [Nontrivial E] (hE : IsElementaryAbelian p E) {T : Type*} [CommGroup T] [Finite T]
    (ψ : T →* MulAut E)
    (hirr : ∀ U : Subgroup E, IsAInvariant ψ U → U = ⊥ ∨ U = ⊤) :
    ∃ (F : Type u) (_ : Field F) (_ : Module F (Additive E)) (_ : Finite F),
      Module.finrank F (Additive E) = 1 ∧ Nat.card F = Nat.card E ∧
      ∀ (g : MulAut E) (c : T ≃* T), (∀ t, ψ (c t) = g * ψ t * g⁻¹) →
        ∃ σ : F ≃+* F, ∀ (a : F) (x : Additive E),
          (MulEquiv.toAdditive g) (a • x) = σ a • (MulEquiv.toAdditive g) x := by
  haveI hEcomm : IsMulCommutative E := ⟨⟨mul_comm⟩⟩
  have hpsmul : ∀ x : Additive E, (p : ℕ) • x = 0 := by
    intro x; apply Additive.toMul.injective; rw [toMul_nsmul, toMul_zero]
    exact hE.pow_eq_one x.toMul
  haveI : Module (ZMod p) (Additive E) := AddCommGroup.zmodModule hpsmul
  let ρ : Representation (ZMod p) T (Additive E) := (mulAutToEnd E p).comp ψ
  letI instKT : Module (MonoidAlgebra (ZMod p) T) (Additive E) :=
    Module.compHom (Additive E) ρ.asAlgebraHom.toRingHom
  have key : ∀ (t : T) (x : Additive E),
      (MonoidAlgebra.of (ZMod p) T t) • x = Additive.ofMul ((ψ t) (Additive.toMul x)) := by
    intro t x
    rw [show (MonoidAlgebra.of (ZMod p) T t) • x
          = ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) T t) x from rfl,
        Representation.asAlgebraHom_of]
    rfl
  haveI hsimp : IsSimpleModule (MonoidAlgebra (ZMod p) T) (Additive E) := by
    haveI : Nontrivial (Additive E) := inferInstanceAs (Nontrivial (Additive E))
    refine { eq_bot_or_eq_top := fun N => ?_ }
    let H : Subgroup E :=
      { carrier := {e : E | Additive.ofMul e ∈ N}
        one_mem' := by change Additive.ofMul (1 : E) ∈ N; rw [ofMul_one]; exact N.zero_mem
        mul_mem' := fun {a b} ha hb => by
          change Additive.ofMul (a * b) ∈ N
          rw [ofMul_mul]; exact N.add_mem ha hb
        inv_mem' := fun {a} ha => by
          change Additive.ofMul a⁻¹ ∈ N
          rw [ofMul_inv]; exact N.neg_mem ha }
    have hHinv : IsAInvariant ψ H := by
      rw [isAInvariant_iff_smul_mem]
      intro t a ha
      change Additive.ofMul ((ψ t) a) ∈ N
      have hmem : (MonoidAlgebra.of (ZMod p) T t) • (Additive.ofMul a) ∈ N :=
        N.smul_mem _ (show Additive.ofMul a ∈ N from ha)
      rw [key t (Additive.ofMul a)] at hmem
      exact hmem
    rcases hirr H hHinv with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxH : Additive.toMul x ∈ H := hx
      rw [h, Subgroup.mem_bot] at hxH
      change Additive.ofMul (Additive.toMul x) = 0
      rw [hxH, ofMul_one]
    · right
      rw [Submodule.eq_top_iff']
      intro x
      exact (by rw [h]; exact Subgroup.mem_top _ : Additive.toMul x ∈ H)
  refine ⟨Module.End (MonoidAlgebra (ZMod p) T) (Additive E), endField, Module.End.applyModule,
    finite_end, finrank_end_eq_one, natCard_end_eq.trans (Nat.card_congr Additive.toMul),
    fun g c hc => ?_⟩
  -- per-`g` field automorphism `σ_g` (conjugation by `g`) and `F`-semilinearity
  let uLin : Additive E ≃ₗ[ZMod p] Additive E :=
    (MulEquiv.toAdditive g).toLinearEquiv
      (fun a x => ZMod.map_smul (MulEquiv.toAdditive g).toAddMonoidHom a x)
  let τ : MonoidAlgebra (ZMod p) T ≃ₐ[ZMod p] MonoidAlgebra (ZMod p) T :=
    MonoidAlgebra.domCongr (ZMod p) (ZMod p) c
  have hu_eq : ∀ t, g * ψ t = ψ (c t) * g := by intro t; rw [hc t]; group
  have hsemi : ∀ (r : MonoidAlgebra (ZMod p) T) (x : Additive E),
      uLin (r • x) = (τ r) • (uLin x) := by
    intro r
    refine MonoidAlgebra.induction_on
      (p := fun r => ∀ x : Additive E, uLin (r • x) = (τ r) • (uLin x))
      r (fun t x => ?_) (fun a b ha hb x => ?_) (fun s a ha x => ?_)
    · have e1 : (MonoidAlgebra.of (ZMod p) T t) • x = (mulAutToEnd E p (ψ t)) x := by
        change ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) T t) x = _
        rw [Representation.asAlgebraHom_of]; rfl
      have e2 : τ (MonoidAlgebra.of (ZMod p) T t) = MonoidAlgebra.of (ZMod p) T (c t) := by
        change MonoidAlgebra.domCongr (ZMod p) (ZMod p) c (MonoidAlgebra.of (ZMod p) T t) = _
        rw [show MonoidAlgebra.of (ZMod p) T t = MonoidAlgebra.single t 1 from rfl,
          MonoidAlgebra.domCongr_single]; rfl
      have e3 : (MonoidAlgebra.of (ZMod p) T (c t)) • (uLin x)
          = (mulAutToEnd E p (ψ (c t))) (uLin x) := by
        change ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) T (c t)) (uLin x) = _
        rw [Representation.asAlgebraHom_of]; rfl
      rw [e1, e2, e3]
      change mulAutToEnd E p g ((mulAutToEnd E p (ψ t)) x)
        = (mulAutToEnd E p (ψ (c t))) (mulAutToEnd E p g x)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hu_eq t]
    · rw [add_smul, map_add, ha, hb, map_add, add_smul]
    · rw [smul_assoc, map_smul, ha, map_smul, smul_assoc]
  let τRing : MonoidAlgebra (ZMod p) T ≃+* MonoidAlgebra (ZMod p) T := τ.toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv τRing
  haveI := RingHomInvPair.of_ringEquiv τRing.symm
  let eSL : Additive E ≃ₛₗ[(τRing : MonoidAlgebra (ZMod p) T →+* MonoidAlgebra (ZMod p) T)]
      Additive E :=
    { toFun := uLin, map_add' := uLin.map_add, map_smul' := fun r x => hsemi r x,
      invFun := uLin.symm, left_inv := uLin.left_inv, right_inv := uLin.right_inv }
  refine ⟨eSL.conjRingEquiv, fun a x => ?_⟩
  change uLin (a • x) = eSL.conjRingEquiv a • uLin x
  rw [Module.End.smul_def, Module.End.smul_def, LinearEquiv.conjRingEquiv_apply_apply]
  change uLin (a x) = uLin (a (uLin.symm (uLin x)))
  rw [LinearEquiv.symm_apply_apply]

open scoped Classical in
/-- **Peterfalvi, Appendix I, Proposition 2(a)+(b)**, with the scalar
realization of `T` retained.  The old `exists_field_semilinear` theorem remains
unchanged; this stronger result is the interface required by Part II, Ch. I
§2, Proposition 3. -/
theorem exists_field_semilinear_with_scalar.{u} {p : ℕ} [Fact p.Prime]
    {E : Type u} [CommGroup E] [Finite E] [Nontrivial E]
    (hE : IsElementaryAbelian p E) {T : Type*} [CommGroup T] [Finite T]
    (ψ : T →* MulAut E)
    (hirr : ∀ U : Subgroup E, IsAInvariant ψ U → U = ⊥ ∨ U = ⊤) :
    ∃ (F : Type u) (_ : Field F) (_ : Module F (Additive E)) (_ : Finite F),
      Module.finrank F (Additive E) = 1 ∧ Nat.card F = Nat.card E ∧
      (∃ μ : T →* Fˣ, ∀ (t : T) (x : Additive E),
        (μ t : F) • x = Additive.ofMul ((ψ t) (Additive.toMul x))) ∧
      ∀ (g : MulAut E) (c : T ≃* T), (∀ t, ψ (c t) = g * ψ t * g⁻¹) →
        ∃ σ : F ≃+* F, ∀ (a : F) (x : Additive E),
          (MulEquiv.toAdditive g) (a • x) =
            σ a • (MulEquiv.toAdditive g) x := by
  haveI hEcomm : IsMulCommutative E := ⟨⟨mul_comm⟩⟩
  have hpsmul : ∀ x : Additive E, (p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hE.pow_eq_one x.toMul
  haveI : Module (ZMod p) (Additive E) := AddCommGroup.zmodModule hpsmul
  let ρ : Representation (ZMod p) T (Additive E) := (mulAutToEnd E p).comp ψ
  letI instKT : Module (MonoidAlgebra (ZMod p) T) (Additive E) :=
    Module.compHom (Additive E) ρ.asAlgebraHom.toRingHom
  have key : ∀ (t : T) (x : Additive E),
      (MonoidAlgebra.of (ZMod p) T t) • x =
        Additive.ofMul ((ψ t) (Additive.toMul x)) := by
    intro t x
    rw [show (MonoidAlgebra.of (ZMod p) T t) • x =
          ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) T t) x from rfl,
        Representation.asAlgebraHom_of]
    rfl
  haveI hsimp : IsSimpleModule (MonoidAlgebra (ZMod p) T) (Additive E) := by
    haveI : Nontrivial (Additive E) :=
      inferInstanceAs (Nontrivial (Additive E))
    refine { eq_bot_or_eq_top := fun N ↦ ?_ }
    let H : Subgroup E :=
      { carrier := {e : E | Additive.ofMul e ∈ N}
        one_mem' := by
          change Additive.ofMul (1 : E) ∈ N
          rw [ofMul_one]
          exact N.zero_mem
        mul_mem' := fun {a b} ha hb => by
          change Additive.ofMul (a * b) ∈ N
          rw [ofMul_mul]
          exact N.add_mem ha hb
        inv_mem' := fun {a} ha => by
          change Additive.ofMul a⁻¹ ∈ N
          rw [ofMul_inv]
          exact N.neg_mem ha }
    have hHinv : IsAInvariant ψ H := by
      rw [isAInvariant_iff_smul_mem]
      intro t a ha
      change Additive.ofMul ((ψ t) a) ∈ N
      have hmem :
          (MonoidAlgebra.of (ZMod p) T t) • (Additive.ofMul a) ∈ N :=
        N.smul_mem _ (show Additive.ofMul a ∈ N from ha)
      rw [key t (Additive.ofMul a)] at hmem
      exact hmem
    rcases hirr H hHinv with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxH : Additive.toMul x ∈ H := hx
      rw [h, Subgroup.mem_bot] at hxH
      change Additive.ofMul (Additive.toMul x) = 0
      rw [hxH, ofMul_one]
    · right
      rw [Submodule.eq_top_iff']
      intro x
      exact (by rw [h]; exact Subgroup.mem_top _ : Additive.toMul x ∈ H)
  let μ : T →* (Module.End (MonoidAlgebra (ZMod p) T) (Additive E))ˣ :=
    (Units.map (Algebra.lsmul (MonoidAlgebra (ZMod p) T)
      (MonoidAlgebra (ZMod p) T) (Additive E)).toMonoidHom).comp
      (MonoidAlgebra.of (ZMod p) T).toHomUnits
  refine ⟨Module.End (MonoidAlgebra (ZMod p) T) (Additive E), endField,
    Module.End.applyModule, finite_end, finrank_end_eq_one,
    natCard_end_eq.trans (Nat.card_congr Additive.toMul),
    ⟨μ, ?_⟩, fun g c hc => ?_⟩
  · intro t x
    change (MonoidAlgebra.of (ZMod p) T t) • x = _
    exact key t x
  · let uLin : Additive E ≃ₗ[ZMod p] Additive E :=
      (MulEquiv.toAdditive g).toLinearEquiv
        (fun a x =>
          ZMod.map_smul (MulEquiv.toAdditive g).toAddMonoidHom a x)
    let τ : MonoidAlgebra (ZMod p) T ≃ₐ[ZMod p]
        MonoidAlgebra (ZMod p) T :=
      MonoidAlgebra.domCongr (ZMod p) (ZMod p) c
    have hu_eq : ∀ t, g * ψ t = ψ (c t) * g := by
      intro t
      rw [hc t]
      group
    have hsemi : ∀ (r : MonoidAlgebra (ZMod p) T) (x : Additive E),
        uLin (r • x) = (τ r) • (uLin x) := by
      intro r
      refine MonoidAlgebra.induction_on
        (p := fun r => ∀ x : Additive E, uLin (r • x) = (τ r) • (uLin x))
        r (fun t x => ?_) (fun a b ha hb x => ?_)
        (fun s a ha x => ?_)
      · have e1 : (MonoidAlgebra.of (ZMod p) T t) • x =
            (mulAutToEnd E p (ψ t)) x := by
          change ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) T t) x = _
          rw [Representation.asAlgebraHom_of]
          rfl
        have e2 : τ (MonoidAlgebra.of (ZMod p) T t) =
            MonoidAlgebra.of (ZMod p) T (c t) := by
          change MonoidAlgebra.domCongr (ZMod p) (ZMod p) c
            (MonoidAlgebra.of (ZMod p) T t) = _
          rw [show MonoidAlgebra.of (ZMod p) T t =
              MonoidAlgebra.single t 1 from rfl,
            MonoidAlgebra.domCongr_single]
          rfl
        have e3 : (MonoidAlgebra.of (ZMod p) T (c t)) • (uLin x) =
            (mulAutToEnd E p (ψ (c t))) (uLin x) := by
          change ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) T (c t))
            (uLin x) = _
          rw [Representation.asAlgebraHom_of]
          rfl
        rw [e1, e2, e3]
        change mulAutToEnd E p g ((mulAutToEnd E p (ψ t)) x) =
          (mulAutToEnd E p (ψ (c t))) (mulAutToEnd E p g x)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply,
          ← map_mul, ← map_mul, hu_eq t]
      · rw [add_smul, map_add, ha, hb, map_add, add_smul]
      · rw [smul_assoc, map_smul, ha, map_smul, smul_assoc]
    let τRing : MonoidAlgebra (ZMod p) T ≃+*
        MonoidAlgebra (ZMod p) T := τ.toRingEquiv
    haveI := RingHomInvPair.of_ringEquiv τRing
    haveI := RingHomInvPair.of_ringEquiv τRing.symm
    let eSL : Additive E
        ≃ₛₗ[(τRing : MonoidAlgebra (ZMod p) T →+*
          MonoidAlgebra (ZMod p) T)] Additive E :=
      { toFun := uLin
        map_add' := uLin.map_add
        map_smul' := fun r x => hsemi r x
        invFun := uLin.symm
        left_inv := uLin.left_inv
        right_inv := uLin.right_inv }
    refine ⟨eSL.conjRingEquiv, fun a x => ?_⟩
    change uLin (a • x) = eSL.conjRingEquiv a • uLin x
    rw [Module.End.smul_def, Module.End.smul_def,
      LinearEquiv.conjRingEquiv_apply_apply]
    change uLin (a x) = uLin (a (uLin.symm (uLin x)))
    rw [LinearEquiv.symm_apply_apply]

end Prop2Bridge

universe u v w

section Prop2Companion

variable {F : Type u} {E : Type v} {U : Type w}
variable [Field F] [CommGroup E] [Module F (Additive E)] [Group U]

private lemma additive_ofMul_ne_zero {s : E} (hs : s ≠ 1) :
    Additive.ofMul s ≠ 0 := by
  intro h
  apply hs
  apply Additive.ofMul.injective
  simpa using h

private lemma ringAut_eq_of_semilinear
    {g : Additive E ≃+ Additive E} {s : Additive E} (hs : s ≠ 0)
    {c d : F ≃+* F}
    (hc : ∀ a : F, g (a • s) = c a • g s)
    (hd : ∀ a : F, g (a • s) = d a • g s) : c = d := by
  ext a
  have hgs : g s ≠ 0 := by simpa using g.injective.ne hs
  apply smul_left_injective F hgs
  exact (hc a).symm.trans (hd a)

/-- **Peterfalvi, Appendix I, Proposition 2(b)** (coherent semilinear companion).
If every element of U is semilinear for some field automorphism, then those uniquely determined
automorphisms assemble into a group homomorphism from U to the field automorphism group.
The nonidentity point supplies the nonzero vector needed for uniqueness. -/
theorem exists_semilinear_companion
    (rho : U →* MulAut E) (s : E) (hs : s ≠ 1)
    (hsemi : ∀ u : U, ∃ c : F ≃+* F, ∀ (a : F) (x : Additive E),
      (MulEquiv.toAdditive (rho u)) (a • x) =
        c a • (MulEquiv.toAdditive (rho u)) x) :
    ∃ companion : U →* (F ≃+* F), ∀ (u : U) (a : F) (x : Additive E),
      (MulEquiv.toAdditive (rho u)) (a • x) =
        companion u a • (MulEquiv.toAdditive (rho u)) x := by
  let c : U → (F ≃+* F) := fun u ↦ Classical.choose (hsemi u)
  have hc (u : U) : ∀ (a : F) (x : Additive E),
      (MulEquiv.toAdditive (rho u)) (a • x) =
        c u a • (MulEquiv.toAdditive (rho u)) x :=
    Classical.choose_spec (hsemi u)
  have hs0 : Additive.ofMul s ≠ 0 := additive_ofMul_ne_zero hs
  have cone : c 1 = 1 := by
    apply ringAut_eq_of_semilinear (g := MulEquiv.toAdditive (rho 1)) hs0
    · exact fun a ↦ hc 1 a (Additive.ofMul s)
    · intro a
      simp
  have cmul (u v : U) : c (u * v) = c u * c v := by
    apply ringAut_eq_of_semilinear (g := MulEquiv.toAdditive (rho (u * v))) hs0
    · exact fun a ↦ hc (u * v) a (Additive.ofMul s)
    · intro a
      rw [map_mul]
      change (MulEquiv.toAdditive (rho u))
          ((MulEquiv.toAdditive (rho v)) (a • Additive.ofMul s)) = _
      rw [hc v a (Additive.ofMul s)]
      rw [hc u (c v a) ((MulEquiv.toAdditive (rho v)) (Additive.ofMul s))]
      rfl
  let companion : U →* (F ≃+* F) :=
    { toFun := c
      map_one' := cone
      map_mul' := cmul }
  exact ⟨companion, hc⟩

/-- **Peterfalvi, Appendix I, Proposition 2(b)** (point-stabilizer embedding).
On a one-dimensional F-space, a faithful group of semilinear maps fixing a nonzero point embeds
into the field automorphism group: a trivial companion fixes every scalar multiple of the point,
hence fixes the whole space.  Together with MonoidHom.ofInjective this identifies the point
stabilizer with a subgroup of RingAut F, exactly as in the textbook. -/
theorem exists_injective_semilinear_companion
    (rho : U →* MulAut E) (s : E) (hs : s ≠ 1)
    (hdim : Module.finrank F (Additive E) = 1)
    (hfix : ∀ u : U, rho u s = s) (hrho : Function.Injective rho)
    (hsemi : ∀ u : U, ∃ c : F ≃+* F, ∀ (a : F) (x : Additive E),
      (MulEquiv.toAdditive (rho u)) (a • x) =
        c a • (MulEquiv.toAdditive (rho u)) x) :
    ∃ companion : U →* (F ≃+* F), Function.Injective companion ∧
      ∀ (u : U) (a : F) (x : Additive E),
        (MulEquiv.toAdditive (rho u)) (a • x) =
          companion u a • (MulEquiv.toAdditive (rho u)) x := by
  obtain ⟨companion, hcompanion⟩ := exists_semilinear_companion rho s hs hsemi
  refine ⟨companion, ?_, hcompanion⟩
  apply (injective_iff_map_eq_one companion).2
  intro u hu
  apply hrho
  have hs0 : Additive.ofMul s ≠ 0 := additive_ofMul_ne_zero hs
  have hfixA : (MulEquiv.toAdditive (rho u)) (Additive.ofMul s) = Additive.ofMul s := hfix u
  have hrho_one : rho u = 1 := by
    ext x
    apply Additive.ofMul.injective
    change (MulEquiv.toAdditive (rho u)) (Additive.ofMul x) = Additive.ofMul x
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hs0 (Additive.ofMul x)
    rw [← ha, hcompanion u a (Additive.ofMul s), hu, hfixA]
    rfl
  simpa using hrho_one

end Prop2Companion

section Prop2FixedPoint

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03

/-- **An operator of prime order that moves the acting group has a non-trivial
fixed point.**

Peterfalvi, Part II, Ch. III §1, Proposition, p. 117: the conclusion
`C_{S/Q₀}(P) ≠ 1` that the book extracts from "`[K, P] ⋊ P` is a Frobenius
group".  That route needs `|P|` prime to `|K|`, which Chapter III does not
supply (and which genuinely fails there); the present statement replaces it and
needs no coprimality at all.

`T` acts irreducibly on the elementary abelian `E`, so by Proposition 2(a)+(b)
(`exists_field_semilinear_with_scalar`) `E` is a line over a finite field `F`
with `T` acting through scalars `μ : T →* Fˣ`, and the normalizing operator `g`
is `σ`-semilinear for a `σ ∈ Aut F` with `μ ∘ c = σ ∘ μ`.  The hypothesis
`ψ (c t₀) ≠ ψ t₀` says exactly `σ ≠ 1` — without it the statement is false, `g`
being multiplication by a scalar `≠ 1`.  Hilbert's Theorem 90
(`OddOrder.exists_ne_zero_fixed_of_semilinear`) then supplies the fixed
vector. -/
theorem exists_ne_one_fixed_of_prime_pow_eq_one {p₀ : ℕ} [Fact p₀.Prime]
    {E : Type u} [CommGroup E] [Finite E] [Nontrivial E]
    (hE : IsElementaryAbelian p₀ E) {T : Type*} [CommGroup T] [Finite T]
    (ψ : T →* MulAut E)
    (hirr : ∀ U : Subgroup E, IsAInvariant ψ U → U = ⊥ ∨ U = ⊤)
    {g : MulAut E} {c : T ≃* T} (hc : ∀ t, ψ (c t) = g * ψ t * g⁻¹)
    {t₀ : T} (ht₀ : ψ (c t₀) ≠ ψ t₀)
    {p : ℕ} (hp : p.Prime) (hgp : g ^ p = 1) :
    ∃ e : E, e ≠ 1 ∧ g e = e := by
  classical
  obtain ⟨F, instF, instMod, instFin, hdim, -, ⟨μ, hμ⟩, hsemi⟩ :=
    exists_field_semilinear_with_scalar hE ψ hirr
  letI : Field F := instF
  letI : Module F (Additive E) := instMod
  letI : Finite F := instFin
  obtain ⟨σ, hσ⟩ := hsemi g c hc
  set g' : Additive E ≃+ Additive E := MulEquiv.toAdditive g with hg'
  have hg'apply : ∀ x : Additive E, g' x = Additive.ofMul (g (Additive.toMul x)) :=
    fun _ => rfl
  have hg'symm : ∀ x : Additive E,
      g'.symm x = Additive.ofMul (g⁻¹ (Additive.toMul x)) := fun _ => rfl
  -- a non-zero vector
  obtain ⟨e₁, he₁⟩ := exists_ne (1 : E)
  have he₀ : (Additive.ofMul e₁ : Additive E) ≠ 0 := fun h =>
    he₁ (by simpa using congrArg Additive.toMul h)
  have hinj : Function.Injective (fun a : F => a • (Additive.ofMul e₁ : Additive E)) :=
    smul_left_injective F he₀
  have hμ' : ∀ (t : T) (e : E), ((μ t : F)) • (Additive.ofMul e : Additive E)
      = Additive.ofMul ((ψ t) e) := fun t e => hμ t (Additive.ofMul e)
  -- the twist on `F` matches the twist `c` on `T`: `μ ∘ c = σ ∘ μ`
  have hμc : ∀ t : T, (μ (c t) : F) = σ (μ t) := by
    intro t
    refine hinj ?_
    have hlhs : ((μ (c t) : F)) • (Additive.ofMul e₁ : Additive E)
        = Additive.ofMul (g ((ψ t) (g⁻¹ e₁))) := by
      rw [hμ' (c t) e₁, hc t]
      rfl
    have hrhs : (σ (μ t)) • (Additive.ofMul e₁ : Additive E)
        = Additive.ofMul (g ((ψ t) (g⁻¹ e₁))) := by
      have h1 := hσ (μ t) (Additive.ofMul (g⁻¹ e₁))
      have h2 : g' (Additive.ofMul (g⁻¹ e₁)) = (Additive.ofMul e₁ : Additive E) := by
        rw [hg'apply]
        exact congrArg Additive.ofMul (by simp)
      rw [hμ' t (g⁻¹ e₁), h2] at h1
      exact h1.symm
    exact hlhs.trans hrhs.symm
  -- hence `σ ≠ 1`
  have hσne : σ ≠ 1 := by
    intro h1
    refine ht₀ (MulEquiv.ext fun e => ?_)
    have hunit : μ (c t₀) = μ t₀ := Units.ext (by rw [hμc t₀, h1]; rfl)
    have h2 := hμ' (c t₀) e
    rw [hunit, hμ' t₀ e] at h2
    exact Additive.ofMul.injective h2.symm
  -- the line is spanned by `e₁`
  have hspan : ∀ x : Additive E, ∃ a : F, a • (Additive.ofMul e₁ : Additive E) = x :=
    fun x => exists_smul_eq_of_finrank_eq_one hdim he₀ x
  -- `g' ^ p = id`
  have hiter : ∀ (n : ℕ) (x : Additive E),
      (g' : Additive E → Additive E)^[n] x = Additive.ofMul ((g ^ n) (Additive.toMul x)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, hg'apply, pow_succ']
      rfl
  have hg'p : ∀ x : Additive E, (g' : Additive E → Additive E)^[p] x = x := by
    intro x
    rw [hiter, hgp]
    rfl
  obtain ⟨x, hx0, hxfix⟩ :=
    OddOrder.exists_ne_zero_fixed_of_semilinear he₀ hspan g' σ hσ hp hg'p hσne
  refine ⟨Additive.toMul x, fun h => hx0 ?_, ?_⟩
  · exact Additive.toMul.injective (by simpa using h)
  · have := hxfix
    rw [hg'apply] at this
    exact congrArg Additive.toMul this

end Prop2FixedPoint

end OddOrder.Peterfalvi.Appendices.Huppert
