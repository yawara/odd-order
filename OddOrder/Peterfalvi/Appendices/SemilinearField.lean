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

open scoped Classical

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
/-- `M` is `1`-dimensional over the field `D = End_{k[T]}(M)` (`isSimpleModule_end` + the
classification of simple modules over a division ring). -/
theorem finrank_end_eq_one :
    Module.finrank (Module.End (MonoidAlgebra k T) M) M = 1 := by
  haveI := finite_end (k := k) (T := T) (M := M)
  exact isSimpleModule_iff_finrank_eq_one.mp isSimpleModule_end

omit [Finite T] in
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

end Prop2Bridge

end OddOrder.Peterfalvi.Appendices.Huppert
