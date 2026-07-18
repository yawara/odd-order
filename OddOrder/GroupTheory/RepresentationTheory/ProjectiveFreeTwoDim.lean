/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RepresentationTheory.Irreducible
import OddOrder.BG.Ch1_Preliminary.S02_Representations
import OddOrder.GroupTheory.FreeActionOrbitCount
import OddOrder.GroupTheory.RepresentationTheory.ElemAbelianAutAction

/-!
# Free projective actions in dimension two

This file isolates the two-dimensional linear algebra used in Peterfalvi,
*Character Theory for the Odd Order Theorem*, Part II, Ch. I, Section 3,
Lemma 5 (p. 107).

If a nontrivial group acts linearly on a two-dimensional vector space and no
nonidentity element fixes a projective point, then the linear representation
is irreducible: a proper nonzero invariant subspace would be a line and hence
a fixed projective point.

Over a finite field of characteristic two, an odd-order faithful action of
this kind is cyclic and its order divides `|F| + 1`.  Cyclicity is obtained by
combining BG Theorem 2.6(a), which makes the group abelian, with the existing
faithful irreducible Singer mechanism.  Divisibility is the free-orbit count
on the projective line, whose cardinality is `|F| + 1`.
-/

set_option autoImplicit false

namespace OddOrder.RepresentationTheory

open scoped LinearAlgebra.Projectivization

universe uF uE uV

section Irreducibility

variable {F : Type uF} [Field F]
  {E : Type uE} [Group E] [Nontrivial E]
  {V : Type uV} [AddCommGroup V] [Module F V]

/-- A fixed-point-free projective action in dimension two is irreducible.

The hypothesis is stated for the projective action induced by the explicit
representation `rho`.  A proper nonzero subrepresentation has dimension one.
Choosing a nonzero vector on that line makes every group element act on it by
a scalar, so every element fixes the corresponding projective point; a
nonidentity element of `E` then contradicts `hfree`. -/
theorem isIrreducible_of_projective_no_nontrivial_fixed
    (rho : Representation F E V) (hdim : Module.finrank F V = 2)
    (hfree : ∀ e : E, e ≠ 1 → ∀ L : Projectivization F V,
      (OddOrder.BG.Ch1.S02.representationToGeneralLinearGroup rho e) • L ≠ L) :
    rho.IsIrreducible := by
  haveI : FiniteDimensional F V := .of_finrank_eq_succ hdim
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  refine { toNontrivial := ?_, eq_bot_or_eq_top := fun W => ?_ }
  · refine ⟨⊥, ⊤, fun h => ?_⟩
    have h' : (⊥ : Submodule F V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'
  · by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    by_cases hWtop : W = ⊤
    · exact Or.inr hWtop
    exfalso
    have hWbot' : W.toSubmodule ≠ ⊥ := fun h =>
      hWbot (Subrepresentation.toSubmodule_injective (by
        change W.toSubmodule = (⊥ : Submodule F V)
        exact h))
    have hWtop' : W.toSubmodule ≠ ⊤ := fun h =>
      hWtop (Subrepresentation.toSubmodule_injective (by
        change W.toSubmodule = (⊤ : Submodule F V)
        exact h))
    have hdimW : Module.finrank F W.toSubmodule = 1 := by
      have hlt := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne le_top hWtop')
      rw [finrank_top, hdim] at hlt
      have hgt := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne bot_le (Ne.symm hWbot'))
      rw [finrank_bot] at hgt
      omega
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot'
    obtain ⟨e, he⟩ := exists_ne (1 : E)
    let xW : W.toSubmodule := ⟨x, hxW⟩
    let exW : W.toSubmodule := ⟨rho e x, W.apply_mem_toSubmodule e hxW⟩
    have hxW0 : xW ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ :=
      exists_smul_eq_of_finrank_eq_one hdimW hxW0 exW
    have hscalar : c • x = rho e x := by
      exact congrArg Subtype.val hc
    have hfix :
        (OddOrder.BG.Ch1.S02.representationToGeneralLinearGroup rho e) •
          Projectivization.mk F x hx0 = Projectivization.mk F x hx0 := by
      rw [Projectivization.smul_mk]
      apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
      exact ⟨c, hscalar⟩
    exact hfree e he (Projectivization.mk F x hx0) hfix

end Irreducibility

section CharacteristicTwo

variable {F : Type uF} [Field F] [Finite F] [hcharTwo : CharP F 2]
  {E : Type uE} [Group E] [Finite E]
  {V : Type uV} [AddCommGroup V] [Module F V]

/-- An odd faithful group acting freely on a projective line in characteristic
two is cyclic, and its order divides the size of that projective line.

In dimension two the latter size is `|F| + 1`.  The theorem includes the
trivial group; in the nontrivial case projective freeness first supplies
irreducibility, BG Theorem 2.6(a) supplies commutativity, and the faithful
irreducible Singer theorem supplies cyclicity. -/
theorem isCyclic_and_card_dvd_card_add_one_of_projective_no_nontrivial_fixed
    (rho : Representation F E V) (hfaith : Function.Injective rho)
    (hodd : Odd (Nat.card E)) (hdim : Module.finrank F V = 2)
    (hfree : ∀ e : E, e ≠ 1 → ∀ L : Projectivization F V,
      (OddOrder.BG.Ch1.S02.representationToGeneralLinearGroup rho e) • L ≠ L) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card F + 1 := by
  classical
  haveI : FiniteDimensional F V := .of_finrank_eq_succ hdim
  letI : Finite V :=
    Finite.of_equiv (Fin (Module.finrank F V) → F)
      (Module.finBasis F V).equivFun.symm.toEquiv
  rcases subsingleton_or_nontrivial E with hEsub | hEnt
  · letI : Subsingleton E := hEsub
    have hcardE : Nat.card E = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hEsub, ⟨1⟩⟩
    exact ⟨isCyclic_of_subsingleton, by rw [hcardE]; exact one_dvd _⟩
  · letI : Nontrivial E := hEnt
    have hirr : rho.IsIrreducible :=
      isIrreducible_of_projective_no_nontrivial_fixed rho hdim hfree
    have hchar : ∀ p : Nat, p.Prime → p ∣ Nat.card E → ¬ CharP F p := by
      intro p hp hpdvd hcharp
      have hpodd : Odd p := hodd.of_dvd_nat hpdvd
      have hp2 : p = 2 := CharP.eq F hcharp hcharTwo
      rw [hp2] at hpodd
      exact (Nat.not_odd_iff_even.mpr even_two) hpodd
    have hcomm : ∀ a b : E, a * b = b * a :=
      (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim rho hfaith hchar).comm
    have hcyclic : IsCyclic E := by
      letI : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
      letI : rho.IsIrreducible := hirr
      exact isCyclic_of_faithful_isIrreducible rho hfaith
    letI : MulAction E (Projectivization F V) :=
      MulAction.compHom _
        (OddOrder.BG.Ch1.S02.representationToGeneralLinearGroup rho)
    refine ⟨hcyclic, ?_⟩
    calc
      Nat.card E ∣ Nat.card (Projectivization F V) :=
        card_dvd_of_no_nontrivial_fixed fun e he L => hfree e he L
      _ = Nat.card F + 1 := Projectivization.card_of_finrank_two F V hdim

end CharacteristicTwo

end OddOrder.RepresentationTheory
