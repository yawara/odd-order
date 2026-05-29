/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import OddOrder.GroupTheory.RepresentationTheory.CharacterCount

/-!
# Completeness of irreducible characters (work in progress)

Toward `|Irr G| = |ConjClasses G|`: the irreducible characters span the space of class
functions. The strategy (analytic / regular-representation route) attaches to a class
function `f` and a representation `ρ` the operator `T_ρ f = ∑_g f(g) • ρ(g) : End V`.

* `classFunctionOperator` — the operator `∑_g f(g) • ρ(g)`.
* `classFunctionOperator_comm` — because `f` is a class function, `T_ρ f` commutes with
  every `ρ(h)`, i.e. it is a `G`-intertwiner of `ρ`.

By Schur's lemma, on an irreducible `ρ` the intertwiner `T_ρ f` is a scalar, computable from
the inner product `(f, χ_ρ)`; if `f ⊥ Irr G` then this scalar is `0`, so `T_ρ f = 0` on every
irreducible and (by Maschke) on the regular representation, forcing `f = 0`. Hence the
irreducible characters span, giving `|Irr G| ≥ |ConjClasses G|` and (with the reverse
inequality already proved) equality. The downstream steps are not yet formalized here.
-/

namespace OddOrder.RepresentationTheory

open Module (finrank)

section CFOp

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]

/-- The operator `∑_{g ∈ G} f(g) • ρ(g)` attached to a class function `f` and a
representation `ρ`, as an endomorphism of `V`. -/
noncomputable def classFunctionOperator (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) :
    Module.End ℂ V :=
  ∑ g : G, f g • ρ g

/-- The class-function operator commutes with the representation: `ρ(h) ∘ T = T ∘ ρ(h)`.
This is the `G`-intertwiner property, and it holds precisely because `f` is constant on
conjugacy classes. -/
theorem classFunctionOperator_comm (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) (h : G) :
    ρ h * classFunctionOperator f ρ = classFunctionOperator f ρ * ρ h := by
  unfold classFunctionOperator
  rw [Finset.mul_sum, Finset.sum_mul]
  -- LHS term: ρ h * (f g • ρ g) = f g • ρ (h * g); RHS term: (f g • ρ g) * ρ h = f g • ρ (g * h)
  have hL : ∀ g : G, ρ h * (f g • ρ g) = f g • ρ (h * g) := by
    intro g; rw [mul_smul_comm, ← map_mul]
  have hR : ∀ g : G, (f g • ρ g) * ρ h = f g • ρ (g * h) := by
    intro g; rw [smul_mul_assoc, ← map_mul]
  rw [Finset.sum_congr rfl (fun g _ => hL g), Finset.sum_congr rfl (fun g _ => hR g)]
  -- Goal: ∑ g, f g • ρ (h * g) = ∑ g, f g • ρ (g * h).
  -- Reindex the RHS by conjugation `g ↦ h * g * h⁻¹`, which sends `g * h ↦ h * g` and fixes `f`.
  rw [← Equiv.sum_comp (MulAut.conj h).toEquiv (fun g => f g • ρ (g * h))]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have hconj : (MulAut.conj h).toEquiv g = h * g * h⁻¹ := by simp [MulAut.conj_apply]
  rw [hconj, f.conj_eq g h, show h * g * h⁻¹ * h = h * g from by group]

/-- The class-function operator `T_ρ f`, packaged as an `IntertwiningMap ρ ρ`
(`classFunctionOperator_comm` is exactly the intertwining condition). -/
noncomputable def classFunctionIntertwiner (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) :
    Representation.IntertwiningMap ρ ρ :=
  (classFunctionOperator f ρ).intertwiningMap_of_isIntertwiningMap ρ ρ (by
    intro g v
    have h := classFunctionOperator_comm f ρ g
    have h2 := (LinearMap.congr_fun h v).symm
    simpa only [Module.End.mul_apply] using h2)

@[simp] theorem classFunctionIntertwiner_toLinearMap (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) :
    (classFunctionIntertwiner f ρ).toLinearMap = classFunctionOperator f ρ := rfl

/-- **Schur's lemma (scalar form).** On a finite-dimensional irreducible complex
representation, the class-function operator `T_ρ f` is a scalar multiple of the identity. -/
theorem classFunctionOperator_eq_smul_id [FiniteDimensional ℂ V] (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    ∃ c : ℂ, classFunctionOperator f ρ = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (classFunctionIntertwiner f ρ)
  refine ⟨c, ?_⟩
  have hL : classFunctionOperator f ρ
      = (algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c).toLinearMap := by
    rw [hc]; rfl
  rw [hL, Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul]
  congr 1

/-- The trace of `T_ρ f = ∑_g f(g) • ρ(g)` is `∑_g f(g) · χ_ρ(g)`. -/
theorem trace_classFunctionOperator [FiniteDimensional ℂ V] (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) :
    LinearMap.trace ℂ V (classFunctionOperator f ρ) = ∑ g : G, f g * ρ.character g := by
  unfold classFunctionOperator
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- If `∑_g f(g) · χ_ρ(g) = 0` for a finite-dimensional irreducible representation `ρ`, then the
class-function operator `T_ρ f` vanishes: by Schur it is `c • id`, and the trace forces `c = 0`. -/
theorem classFunctionOperator_eq_zero_of_sum_eq_zero [FiniteDimensional ℂ V] [Nontrivial V]
    (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (h : ∑ g : G, f g * ρ.character g = 0) :
    classFunctionOperator f ρ = 0 := by
  obtain ⟨c, hc⟩ := classFunctionOperator_eq_smul_id f ρ
  have hfr : 0 < finrank ℂ V := Module.finrank_pos
  have htr : c * (finrank ℂ V : ℂ) = 0 := by
    have e1 : LinearMap.trace ℂ V (classFunctionOperator f ρ) = c * (finrank ℂ V : ℂ) := by
      rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul]
    rw [trace_classFunctionOperator] at e1
    rw [← e1, h]
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp htr with hc0 | hfr0
    · exact hc0
    · exact absurd (Nat.cast_eq_zero.mp hfr0) hfr.ne'
  rw [hc, hc0, zero_smul]

end CFOp

section Transfer

variable {G : Type*} [Group G]

/-- Transport a representation `σ` on `W` along a linear equivalence `e : W ≃ₗ[ℂ] X`, giving a
representation on `X` (conjugation by `e`). Used to move a finite-dimensional representation to a
representative on `Fin n → ℂ`, a `Type 0` space. -/
noncomputable def transportRep {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) :
    Representation ℂ G X :=
  ((e.conjRingEquiv : Module.End ℂ W ≃+* Module.End ℂ X).toRingHom.toMonoidHom).comp σ

@[simp] theorem transportRep_apply {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) (g : G) :
    transportRep σ e g = e.conj (σ g) := rfl

/-- Transporting a representation preserves its character. -/
theorem transportRep_character {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) :
    (transportRep σ e).character = σ.character := by
  funext g
  show LinearMap.trace ℂ X (e.conj (σ g)) = LinearMap.trace ℂ W (σ g)
  exact LinearMap.trace_conj' (σ g) e

set_option backward.isDefEq.respectTransparency false in
/-- Transporting an irreducible representation along a linear equivalence keeps it irreducible. -/
theorem transportRep_isIrreducible {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X)
    [Representation.IsIrreducible σ] : Representation.IsIrreducible (transportRep σ e) := by
  -- rep equivalence `σ ≃ transportRep σ e` via `e`
  have he : ∀ g : G, (e : W →ₗ[ℂ] X) ∘ₗ σ g = (transportRep σ e) g ∘ₗ (e : W →ₗ[ℂ] X) := by
    intro g; ext w
    simp only [LinearMap.comp_apply, transportRep_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  let φ : σ.Equiv (transportRep σ e) := Representation.Equiv.mk e he
  -- transport to `asModule` linear equivalence over `ℂ[G]`
  have hbij : Function.Bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule σ (transportRep σ e)
        φ.toIntertwiningMap) :=
    e.bijective
  -- No type annotation on `L`: the `asModule` `MonoidAlgebra`-module instance is baked into the
  -- result of `equivLinearMapAsModule`, whereas re-stating the type would re-trigger (and fail)
  -- instance search on the `asModule` type synonym.
  let L := LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule σ (transportRep σ e)
        φ.toIntertwiningMap) hbij
  haveI hσs := (Representation.irreducible_iff_isSimpleModule_asModule σ).mp
    ‹Representation.IsIrreducible σ›
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr L.symm

/-- **Every finite-dimensional irreducible complex representation has its character among the
`IsIrreducibleCharacter`s.** (`IsIrreducibleCharacter` only quantifies over `Type 0` carriers;
this discharges the universe restriction by transporting to `Fin n → ℂ`.) -/
theorem exists_isIrreducibleCharacter_eq {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∃ φ : ClassFunction G ℂ, IsIrreducibleCharacter φ ∧ (φ : G → ℂ) = σ.character := by
  let e : W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  haveI : Representation.IsIrreducible (transportRep σ e) := transportRep_isIrreducible σ e
  refine ⟨repCharacterClassFunction (transportRep σ e),
    ⟨Fin (finrank ℂ W) → ℂ, inferInstance, inferInstance, inferInstance, transportRep σ e,
      inferInstance, rfl⟩, ?_⟩
  funext g
  exact congrFun (transportRep_character σ e) g

end Transfer

section Completeness

open scoped MonoidAlgebra

variable {G : Type*} [Group G]

/-- `f` precomposed with inversion, `g ↦ f g⁻¹`. A class function, since inversion permutes each
conjugacy class. -/
def classFunctionInv (f : ClassFunction G ℂ) : ClassFunction G ℂ :=
  ⟨fun g => f g⁻¹, fun g h => by
    show f (h * g * h⁻¹)⁻¹ = f g⁻¹
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ from by group, f.conj_eq]⟩

@[simp] theorem classFunctionInv_apply (f : ClassFunction G ℂ) (g : G) :
    classFunctionInv f g = f g⁻¹ := rfl

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- If `f` is orthogonal to every irreducible character, then for every finite-dimensional
irreducible representation `σ`, `∑_g f(g⁻¹) · χ_σ(g) = 0`. (Reindexing by `g ↦ g⁻¹` and the
identity `χ_σ(g⁻¹) = conj χ_σ(g)` turn this sum into `|G| · (f, χ_σ)`, which vanishes since
`χ_σ ∈ Irr G`.) -/
theorem sum_classFunctionInv_character_eq_zero {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (f : ClassFunction G ℂ)
    (hf : ∀ χ : IrreducibleCharacter G, ClassFunction.inner f (χ : ClassFunction G ℂ) = 0)
    (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∑ g : G, classFunctionInv f g * σ.character g = 0 := by
  obtain ⟨χ, hχirr, hχeq⟩ := exists_isIrreducibleCharacter_eq σ
  have hstep : ∑ g : G, classFunctionInv f g * σ.character g
      = ∑ g : G, f g * star ((χ : ClassFunction G ℂ) g) := by
    apply Fintype.sum_equiv (Equiv.inv G)
    intro g
    simp only [Equiv.inv_apply, classFunctionInv_apply]
    rw [congrFun hχeq g⁻¹, character_inv σ g, star_star]
  rw [hstep]
  have : ∑ g : G, f g * star ((χ : ClassFunction G ℂ) g)
      = ClassFunction.innerSum f (χ : ClassFunction G ℂ) := rfl
  rw [this, ← ClassFunction.card_mul_inner, hf ⟨χ, hχirr⟩, mul_zero]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
set_option backward.isDefEq.respectTransparency false in
/-- On the subrepresentation `ofSubmodule' N`, the `ℂ[G]`-action on `asModule` is the ambient action
restricted: `(c • v).val = c • v.val` (the right-hand smul taken in `ρ.asModule`). Reduces to
`Representation.single_smul` and `(ofSubmodule' N).toRepresentation g = (ρ g).restrict`. -/
theorem ofSubmodulePrime_coe_smul {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule) (c : ℂ[G])
    (v : (Subrepresentation.ofSubmodule' N).toRepresentation.asModule) :
    ((c • v).1 : ρ.asModule) = c • (show ρ.asModule from v.1) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_smul, add_smul, AddSubmonoid.coe_add, hx, hy]
  | single g a => rw [Representation.single_smul, Representation.single_smul]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- A `ℂ[G]`-submodule `N` of `ρ.asModule`, viewed as the subrepresentation `ofSubmodule' N`, has
its `asModule` `ℂ[G]`-linearly isomorphic to `N`. The underlying map is the identity on the shared
carrier (`↥N` and `↥(ofSubmodule' N).toSubmodule` are the same type definitionally); the only
content is `ℂ[G]`-linearity, supplied by `ofSubmodulePrime_coe_smul`. -/
noncomputable def ofSubmodulePrimeAsModuleEquiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule) :
    (↥N) ≃ₗ[ℂ[G]] (Subrepresentation.ofSubmodule' N).toRepresentation.asModule where
  toFun v := v
  invFun w := w
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c v := by
    apply Subtype.ext
    rw [RingHom.id_apply, Submodule.coe_smul]
    exact (ofSubmodulePrime_coe_smul ρ N c v).symm

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
set_option backward.isDefEq.respectTransparency false in
/-- For a simple `ℂ[G]`-submodule `N` of `ρ.asModule`, the subrepresentation `ofSubmodule' N` is
irreducible. -/
theorem ofSubmodulePrime_isIrreducible {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] (↥N)] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' N).toRepresentation := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (ofSubmodulePrimeAsModuleEquiv ρ N).isSimpleModule_iff.mp inferInstance

omit [Invertible (Nat.card G : ℂ)] in
/-- The class-function operator on the subrepresentation `ofSubmodule' N` is the ambient operator
restricted: `(classFunctionOperator cf (ofSubmodule' N).toRepresentation w).val
= classFunctionOperator cf ρ w.val`. Each summand's value matches because
`(ofSubmodule' N).toRepresentation g = (ρ g).restrict`. -/
theorem classFunctionOperator_ofSubmodulePrime_coe (f : ClassFunction G ℂ) {W : Type*}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (N : Submodule ℂ[G] ρ.asModule)
    (w : (Subrepresentation.ofSubmodule' N).toRepresentation.asModule) :
    ((classFunctionOperator f (Subrepresentation.ofSubmodule' N).toRepresentation w).1 : W)
    = classFunctionOperator f ρ (show W from w.1) := by
  rw [classFunctionOperator, classFunctionOperator, LinearMap.sum_apply, LinearMap.sum_apply,
    AddSubmonoid.coe_finset_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Completeness of irreducible characters.** If `f : ClassFunction G ℂ` is orthogonal to every
irreducible character, then `f = 0`. Equivalently, the irreducible characters span the space of
class functions.

The proof uses the regular representation `reg = ofMulAction ℂ G G`. The class-function operator
`T = ∑_g f(g⁻¹) • reg g` is `ℂ[G]`-linear (an intertwiner). By Maschke's theorem `reg.asModule` is
a semisimple `ℂ[G]`-module, hence the supremum of its simple submodules is `⊤`. On each simple
submodule `N` the corresponding subrepresentation is irreducible (`ofSubmodulePrime_isIrreducible`),
so Schur's lemma forces `T` to vanish there (`classFunctionOperator_eq_zero_of_sum_eq_zero`, fed by
`sum_classFunctionInv_character_eq_zero`). Therefore `ker T = ⊤`, i.e. `T = 0`. Evaluating `T` at
`Finsupp.single 1 1` reads off `f(g⁻¹) = 0` for every `g`, so `f = 0`. -/
theorem classFunction_eq_zero_of_orthogonal (f : ClassFunction G ℂ)
    (hf : ∀ χ : IrreducibleCharacter G, ClassFunction.inner f (χ : ClassFunction G ℂ) = 0) :
    f = 0 := by
  haveI : Finite G := Finite.of_fintype G
  haveI : NeZero (Nat.card G : ℂ) := ⟨Invertible.ne_zero _⟩
  let reg : Representation ℂ G (G →₀ ℂ) := Representation.ofMulAction ℂ G G
  have hreg : reg = Representation.ofMulAction ℂ G G := rfl
  -- The intertwiner `T = ∑_g f(g⁻¹) • reg g`, packaged as a `ℂ[G]`-linear `End` of `asModule`.
  set Ti : reg.asModule →ₗ[ℂ[G]] reg.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule reg reg
      (classFunctionIntertwiner (classFunctionInv f) reg) with hTi
  -- Each simple `ℂ[G]`-submodule lies in `ker Ti`.
  have hsimple_le : ∀ N : Submodule ℂ[G] reg.asModule, IsSimpleModule ℂ[G] (↥N) →
      N ≤ LinearMap.ker Ti := by
    intro N hN
    haveI := hN
    haveI : Nontrivial (↥N) := IsSimpleModule.nontrivial ℂ[G] (↥N)
    set σN : Representation ℂ G _ := (Subrepresentation.ofSubmodule' N).toRepresentation with hσN
    haveI : Representation.IsIrreducible σN := ofSubmodulePrime_isIrreducible reg N
    haveI : Nontrivial ((Subrepresentation.ofSubmodule' N).toSubmodule) := ‹Nontrivial (↥N)›
    haveI : FiniteDimensional ℂ ((Subrepresentation.ofSubmodule' N).toSubmodule) :=
      inferInstance
    -- `T` restricted to the subrepresentation `σN` vanishes by Schur + orthogonality.
    have hzero : classFunctionOperator (classFunctionInv f) σN = 0 :=
      classFunctionOperator_eq_zero_of_sum_eq_zero (classFunctionInv f) σN
        (sum_classFunctionInv_character_eq_zero f hf σN)
    intro v hv
    -- `Ti v` equals the unbundled operator applied to `v`.
    have hTiv : Ti v = classFunctionOperator (classFunctionInv f) reg v := by
      rw [hTi]
      rfl
    -- The value of the restricted operator at `⟨v, _⟩` equals `Ti v`.
    have hmem : v ∈ (Subrepresentation.ofSubmodule' N).toSubmodule :=
      (Subrepresentation.mem_ofSubmodule'_iff).mpr hv
    rw [LinearMap.mem_ker, hTiv]
    have hval := classFunctionOperator_ofSubmodulePrime_coe (classFunctionInv f) reg N ⟨v, hmem⟩
    rw [hσN] at hzero
    rw [← hval, hzero]
    rfl
  -- `ker Ti = ⊤` since the supremum of simple submodules is `⊤` (Maschke).
  haveI : IsSemisimpleModule ℂ[G] reg.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule reg).mp inferInstance
  have hker : LinearMap.ker Ti = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← IsSemisimpleModule.sSup_simples_eq_top ℂ[G] reg.asModule]
    exact sSup_le fun N hN => hsimple_le N hN
  -- Hence `Ti = 0`, so the unbundled operator `T = ∑_g f(g⁻¹) • reg g` is `0`.
  have hTi0 : Ti = 0 := LinearMap.ker_eq_top.mp hker
  have hop0 : classFunctionOperator (classFunctionInv f) reg = 0 := by
    have : (Representation.IntertwiningMap.equivLinearMapAsModule reg reg).symm Ti
        = classFunctionIntertwiner (classFunctionInv f) reg := by
      rw [hTi, LinearEquiv.symm_apply_apply]
    rw [hTi0, map_zero] at this
    have h2 := congrArg Representation.IntertwiningMap.toLinearMap this.symm
    rwa [classFunctionIntertwiner_toLinearMap] at h2
  -- Evaluate `T` at `single 1 1` to read off `f (g⁻¹) = 0` for every `g`.
  apply ClassFunction.ext
  intro k
  classical
  have hcoeff : ∀ x : G, (classFunctionOperator (classFunctionInv f) reg
      (Finsupp.single (1 : G) 1)) x = f x⁻¹ := by
    intro x
    rw [classFunctionOperator]
    have hterm : ∀ g : G, (classFunctionInv f g • reg g) (Finsupp.single (1 : G) (1 : ℂ)) x
        = if g = x then f g⁻¹ else 0 := by
      intro g
      rw [LinearMap.smul_apply, hreg, Representation.ofMulAction_single, Finsupp.smul_single,
        smul_eq_mul, mul_one, Finsupp.single_apply, smul_eq_mul, mul_one, classFunctionInv_apply,
        eq_comm]
    rw [LinearMap.sum_apply, Finset.sum_apply',
      Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_ite_eq' Finset.univ x]
    simp
  have := hcoeff k⁻¹
  rw [hop0] at this
  simpa using this.symm

end Completeness

section Count

variable {G : Type*} [Group G]

open Module (finrank)

/-- The linear functional "inner product against the irreducible characters", as a single
`ℂ`-linear map `ClassFunction G ℂ →ₗ[ℂ] (IrreducibleCharacter G → ℂ)`, `f ↦ (χ ↦ (f, χ))`.
`ClassFunction.inner` is `ℂ`-linear in its first argument, so this is well-defined; completeness
(`classFunction_eq_zero_of_orthogonal`) says it is injective. -/
noncomputable def innerAgainstIrreducibleCharacters [Fintype G] [Invertible (Nat.card G : ℂ)] :
    ClassFunction G ℂ →ₗ[ℂ] (IrreducibleCharacter G → ℂ) where
  toFun f χ := ClassFunction.inner f (χ : ClassFunction G ℂ)
  map_add' f₁ f₂ := by funext χ; exact ClassFunction.inner_add_left f₁ f₂ _
  map_smul' c f := by
    funext χ
    simpa using ClassFunction.inner_smul_left c f (χ : ClassFunction G ℂ)

/-- **`|Irr G| = |ConjClasses G|`** (Isaacs Thm 2.8 / Thm 6.10 count): the number of irreducible
complex characters of a finite group equals the number of conjugacy classes.

The `≤` direction is `card_irreducibleCharacter_le` (linear independence). For `≥`, completeness
(`classFunction_eq_zero_of_orthogonal`) makes the inner-product map
`innerAgainstIrreducibleCharacters : ClassFunction G ℂ →ₗ (IrreducibleCharacter G → ℂ)` injective,
whence `|ConjClasses G| = finrank ℂ (ClassFunction G ℂ) ≤ finrank ℂ (Irr G → ℂ) = |Irr G|`. -/
theorem card_irreducibleCharacter_eq [Finite G] :
    Nat.card (IrreducibleCharacter G) = Nat.card (ConjClasses G) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI := finite_irreducibleCharacter (G := G)
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  refine le_antisymm (card_irreducibleCharacter_le (G := G)) ?_
  -- The inner-product map against the irreducible characters is injective by completeness.
  have hinj : Function.Injective (innerAgainstIrreducibleCharacters (G := G)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine classFunction_eq_zero_of_orthogonal f fun χ => ?_
    exact congrFun hf χ
  -- Injectivity bounds the dimension of the class functions by `|Irr G|`.
  have hfr : finrank ℂ (ClassFunction G ℂ) ≤ finrank ℂ (IrreducibleCharacter G → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_classFunction (G := G), Module.finrank_fintype_fun_eq_card,
    ← Nat.card_eq_fintype_card (α := IrreducibleCharacter G)] at hfr
  exact hfr

/-- **The irreducible characters span the space of class functions.** Equivalently, every class
function is a `ℂ`-linear combination of irreducible characters (Isaacs Thm 2.8). Combines linear
independence (`linearIndependent_irreducibleCharacter`) with the count
`card_irreducibleCharacter_eq` and `finrank_classFunction`. -/
theorem span_irreducibleCharacter_eq_top [Finite G] :
    Submodule.span ℂ (Set.range (fun χ : IrreducibleCharacter G => (χ : ClassFunction G ℂ)))
      = ⊤ := by
  haveI := finite_irreducibleCharacter (G := G)
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  haveI : Nonempty (IrreducibleCharacter G) := ⟨trivialIrreducibleCharacter G⟩
  refine LinearIndependent.span_eq_top_of_card_eq_finrank
    (linearIndependent_irreducibleCharacter (G := G)) ?_
  rw [finrank_classFunction (G := G), ← Nat.card_eq_fintype_card, card_irreducibleCharacter_eq]

end Count

section TableIndexing

open scoped Classical in
/-- **Hypothesis-free character-table indexing data** for a finite group, built from the count
`card_irreducibleCharacter_eq`. This discharges the cardinality input of
`CharacterTableIndexing.ofFinite`, so downstream column-orthogonality results (which take a
`CharacterTableIndexing G`) apply to any `[Finite G]`. -/
noncomputable def CharacterTableIndexing.ofFinite' (G : Type*) [Group G] [Finite G] :
    CharacterTableIndexing G := by
  haveI := finite_irreducibleCharacter (G := G)
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  refine CharacterTableIndexing.ofFinite (G := G) ?_
  letI : Fintype (ConjClasses G) := conjClassesFintypeOfFinite G
  rw [← Nat.card_eq_fintype_card (α := IrreducibleCharacter G),
    ← Nat.card_eq_fintype_card (α := ConjClasses G), card_irreducibleCharacter_eq]

/-- A finite group canonically carries character-table indexing data. -/
noncomputable instance instCharacterTableIndexingOfFinite {G : Type*} [Group G] [Finite G] :
    CharacterTableIndexing G :=
  CharacterTableIndexing.ofFinite' G

end TableIndexing

end OddOrder.RepresentationTheory
