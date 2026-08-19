/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Modules along a surjection of rings

To identify the simple `kG`-modules with the blocks of the split semisimple quotient one has to
move modules across the surjection `kG ↠ kG ⧸ J(kG) ≅ ∏_i M_{d_i}(k)`, in both directions:

* *pulling back* a module of the target is always possible (`Module.compHom`) and preserves
  simplicity, because the submodule lattices agree;
* *pushing forward* an `A`-module is possible exactly when the kernel annihilates it, which for
  `J(kG)` and a simple module is automatic (`IsSemisimpleModule.jacobson_le_annihilator`).

Both directions are the same statement about the two submodule lattices, so simplicity transfers
either way.

## Main results

* `OddOrder.moduleOfSurjective` — the push-forward module structure
* `OddOrder.isSimpleModule_of_surjective`, `OddOrder.isSimpleModule_compHom`
-/

namespace OddOrder

variable {A B : Type*} [Ring A] [Ring B]

/-! ### Pulling back along a surjection -/

section Pullback

variable {N : Type*} [AddCommGroup N] [Module B N]

theorem compHom_smul (f : A →+* B) (a : A) (x : N) :
    letI := Module.compHom N f
    a • x = f a • x := rfl

/-- **Pulling a module back along a surjection preserves simplicity**: the two rings have the
same submodules. -/
theorem isSimpleModule_compHom (f : A →+* B) (hf : Function.Surjective f) [IsSimpleModule B N] :
    letI := Module.compHom N f
    IsSimpleModule A N := by
  let := Module.compHom N f
  have : RingHomSurjective f := ⟨hf⟩
  let l : N →ₛₗ[f] N := { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

end Pullback

/-! ### Pushing forward along a surjection -/

section Pushforward

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- **A module annihilated by the kernel of a surjection is a module over the target.**  The
action is the unique one compatible with the surjection. -/
@[reducible] noncomputable def moduleOfSurjective (f : A →+* B) (hf : Function.Surjective f)
    (h : RingHom.ker f ≤ Module.annihilator A M) : Module B M :=
  Module.compHom M
    (f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
      ⟨Module.toAddMonoidEnd A M, h⟩)

@[simp]
theorem moduleOfSurjective_smul (f : A →+* B) (hf : Function.Surjective f)
    (h : RingHom.ker f ≤ Module.annihilator A M) (a : A) (m : M) :
    letI := moduleOfSurjective f hf h
    f a • m = a • m := by
  let := moduleOfSurjective f hf h
  change (f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
    ⟨Module.toAddMonoidEnd A M, h⟩ (f a)) m = a • m
  rw [RingHom.liftOfRightInverse_comp_apply]
  rfl

/-- **Pushing a simple module forward along a surjection keeps it simple.** -/
theorem isSimpleModule_of_surjective (f : A →+* B) (hf : Function.Surjective f)
    (h : RingHom.ker f ≤ Module.annihilator A M) [IsSimpleModule A M] :
    letI := moduleOfSurjective f hf h
    IsSimpleModule B M := by
  let := moduleOfSurjective f hf h
  have : RingHomSurjective f := ⟨hf⟩
  let l : M →ₛₗ[f] M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => (moduleOfSurjective_smul f hf h a m).symm }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mp inferInstance

end Pushforward

end OddOrder
