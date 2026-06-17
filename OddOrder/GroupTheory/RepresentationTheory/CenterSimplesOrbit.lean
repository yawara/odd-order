/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterSplitting
import OddOrder.GroupTheory.RepresentationTheory.PiAlgebraAut

/-!
# The `MulAut G`-action on the simples, and its compatibility with `centerRep`

For Peterfalvi (9.1)'s orbit-count Brauer lemma (simples side), fix a splitting
`φ : Z(k[G]) ≃ₐ[k] (Fin N → k)` (from `exists_center_algEquiv_pi`).  `MulAut G` acts on the
"simples" `Fin N` by transporting `centerRep` through `φ` and reading off the coordinate
permutation:
`simplesAction φ = algAutPerm ∘ (autCongr φ) ∘ centerCongrHom ∘ domCongrAut`.

The key compatibility — the `hρ` the cornerstone needs — is
`centerRep g (φ.symm (Pi.single i 1)) = φ.symm (Pi.single (simplesAction φ g i) 1)`:
`centerRep g` is `domCongr g` restricted to the centre, so `φ ∘ centerRep g ∘ φ.symm` is the algebra
automorphism `autCongr φ (...)` of `Fin N → k`, which permutes the standard idempotents by
`simplesAction φ g` (`algAutPerm_apply_single`).
-/

open OddOrder.GroupTheory.CenterClassSum (centerRep centerEnd CenterCarrier centerRep' centerBasis'
  centerRep'_apply_centerBasis' finrank_centerRep_invariants_eq_card_orbits)
open OddOrder.GroupTheory.PiAlgebraAut (algAutPerm algAutPerm_apply_single)
open OddOrder.GroupTheory.PermutationInvariants (finrank_invariants_eq_card_orbits)
open Module MulAction

namespace OddOrder.GroupTheory.CenterSimplesOrbit

variable {k G : Type*} [Field k] [Group G] {N : ℕ}
  (φ : Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin N → k))

/-- `centerRep g` is `domCongr g` restricted to the centre, as an algebra automorphism. -/
theorem centerRep_eq_centerCongr (g : MulAut G) (z : Subalgebra.center k (MonoidAlgebra k G)) :
    centerRep g z = (MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr z :=
  Subtype.ext (by rw [CenterSplitting.centerCongr_apply]; rfl)

/-- The action of `MulAut G` on the simples `Fin N`, via the splitting `φ`:
`MulAut G →* Aut k[G] →* Aut Z →* Aut (Fin N → k) →* Perm (Fin N)`. -/
noncomputable def simplesAction : MulAut G →* Equiv.Perm (Fin N) :=
  algAutPerm.comp ((AlgEquiv.autCongr φ).toMonoidHom.comp
    (AlgEquiv.centerCongrHom.comp
      (MonoidAlgebra.domCongrAut (R := k) (A := k) (M := G))))

/-- **Compatibility for the cornerstone (simples side).**  `centerRep g` permutes the idempotent
basis `i ↦ φ.symm (Pi.single i 1)` according to the `simplesAction`. -/
theorem centerRep_apply_symm_single (g : MulAut G) (i : Fin N) :
    centerRep g (φ.symm (Pi.single i 1)) = φ.symm (Pi.single (simplesAction φ g i) 1) := by
  apply φ.injective
  rw [AlgEquiv.apply_symm_apply, centerRep_eq_centerCongr]
  have key :
      φ ((MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr (φ.symm (Pi.single i 1)))
        = (AlgEquiv.autCongr φ ((MonoidAlgebra.domCongrAut (R := k) (A := k) g).centerCongr))
            (Pi.single i 1) := by
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  rw [key, algAutPerm_apply_single]
  rfl

/-! ### The idempotent basis and the simples-side orbit count -/

/-- The **primitive-idempotent (coordinate) basis** of `Z(k[G])`, transported from the standard
basis of `Fin N → k` through the splitting `φ : Z(k[G]) ≃ₐ[k] (Fin N → k)`:
`idemBasis φ i = φ.symm (Pi.single i 1)`.  Retyped over the `CenterCarrier` synonym (as for the
class-sum basis) so the cornerstone application stays clear of the `Module k` instance-diamond
blowup. -/
noncomputable def idemBasis : Basis (Fin N) k (CenterCarrier k G) :=
  (Pi.basisFun k (Fin N)).map φ.symm.toLinearEquiv

/-- `centerRep'` permutes the idempotent basis according to `simplesAction φ`:
`centerRep' g (idemBasis φ i) = idemBasis φ (simplesAction φ g i)`.  This is the simples-side `hρ`
that the cornerstone needs (compare `centerRep'_apply_centerBasis'` on the class-sum side); it
repackages `centerRep_apply_symm_single`. -/
theorem centerRep'_apply_idemBasis (g : MulAut G) (i : Fin N) :
    centerRep' (k := k) g (idemBasis φ i) = idemBasis φ (simplesAction φ g i) := by
  have e : ∀ j : Fin N, idemBasis φ j = (φ.symm (Pi.single j 1) : CenterCarrier k G) := by
    intro j
    change ((Pi.basisFun k (Fin N)).map φ.symm.toLinearEquiv) j = _
    rw [Basis.map_apply, Pi.basisFun_apply]
    rfl
  rw [e i, e (simplesAction φ g i)]
  exact centerRep_apply_symm_single φ g i

/-- **Orbit count via the idempotent basis** (the simples-side companion of
`finrank_centerRep_invariants_eq_card_orbits`).  Given the splitting `φ` and any
`MulAut G`-action on the simples `Fin N` that agrees with `simplesAction φ`, the dimension of the
`MulAut G`-invariants of `Z(k[G])` equals the number of `MulAut G`-orbits on `Fin N`. -/
theorem finrank_centerRep_invariants_eq_card_orbits_simples [MulAction (MulAut G) (Fin N)]
    (hact : ∀ (g : MulAut G) (i : Fin N), g • i = simplesAction φ g i) :
    finrank k ↥(Representation.invariants (centerRep' (k := k) (G := G)))
      = Nat.card (orbitRel.Quotient (MulAut G) (Fin N)) := by
  apply finrank_invariants_eq_card_orbits (idemBasis φ) centerRep'
  intro g i
  rw [hact g i]
  exact centerRep'_apply_idemBasis φ g i

-- The `Fintype`/`DecidableEq` instances feed the class-sum capstone via `centerBasis`: used in the
-- proof but not the statement type, so suppress the in-type linters (cf. `CenterClassSumBasis`).
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The orbit-count Brauer equality** (Peterfalvi (9.1), step 3 payoff).  Over the splitting `φ`,
the number of `MulAut G`-orbits on conjugacy classes equals the number on the simples `Fin N`.
Both compute `dim Z(k[G])^{MulAut G}` — in the class-sum basis and the idempotent basis
respectively — so the two orbit counts agree, with no characteristic-0 / Teichmüller input. -/
theorem card_orbits_classes_eq_card_orbits_simples
    [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]
    [MulAction (MulAut G) (Fin N)]
    (hact : ∀ (g : MulAut G) (i : Fin N), g • i = simplesAction φ g i) :
    Nat.card (orbitRel.Quotient (MulAut G) (ConjClasses G))
      = Nat.card (orbitRel.Quotient (MulAut G) (Fin N)) := by
  rw [← finrank_centerRep_invariants_eq_card_orbits (k := k) (G := G)]
  exact finrank_centerRep_invariants_eq_card_orbits_simples φ hact

/-! ### The orbit equality for a subgroup / arbitrary acting group

For the kernel-FPF count (†) we need the orbit equality not for all of `MulAut G` but for a single
conjugation automorphism `e` (equivalently the cyclic group `⟨e⟩`).  We generalise to an arbitrary
group `Γ` acting through a hom `ψ : Γ →* MulAut G`: precomposing `centerRep'` with `ψ` gives a
`Representation k Γ` (a `Representation` is an `abbrev` for the `MonoidHom`, so `MonoidHom.comp`
typechecks), and the cornerstone applies to both bases as before.  Taking
`Γ = ↥(Subgroup.zpowers e)` with `ψ = Subgroup.subtype` (the agreement hypotheses then hold by
`rfl`) specialises to `⟨e⟩`. -/

section CompOrbitCount

variable {Γ : Type*} [Group Γ] (ψ : Γ →* MulAut G)

/-- `centerRep'` precomposed with `ψ : Γ →* MulAut G`, viewed as a representation of `Γ` on the
centre (the type ascription is what lets `Representation.invariants` resolve the carrier). -/
noncomputable def centerRepComp : Representation k Γ (CenterCarrier k G) := centerRep'.comp ψ

-- See `card_orbits_classes_eq_card_orbits_simples` for why the in-type linters are suppressed.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Class-sum side, for a `Γ`-action factoring through `ψ : Γ →* MulAut G`. -/
theorem finrank_centerRepComp_invariants_eq_card_orbits_classes
    [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]
    [MulAction Γ (ConjClasses G)]
    (hcl : ∀ (γ : Γ) (C : ConjClasses G), γ • C = ψ γ • C) :
    finrank k ↥(Representation.invariants (centerRepComp (k := k) ψ))
      = Nat.card (orbitRel.Quotient Γ (ConjClasses G)) := by
  refine finrank_invariants_eq_card_orbits centerBasis' (centerRepComp (k := k) ψ) ?_
  intro γ C
  change centerRep' (ψ γ) (centerBasis' C) = centerBasis' (γ • C)
  rw [hcl γ C]
  exact centerRep'_apply_centerBasis' (ψ γ) C

/-- Simples side, for a `Γ`-action factoring through `ψ : Γ →* MulAut G`. -/
theorem finrank_centerRepComp_invariants_eq_card_orbits_simples [MulAction Γ (Fin N)]
    (hsi : ∀ (γ : Γ) (i : Fin N), γ • i = simplesAction φ (ψ γ) i) :
    finrank k ↥(Representation.invariants (centerRepComp (k := k) ψ))
      = Nat.card (orbitRel.Quotient Γ (Fin N)) := by
  refine finrank_invariants_eq_card_orbits (idemBasis φ) (centerRepComp (k := k) ψ) ?_
  intro γ i
  change centerRep' (ψ γ) (idemBasis φ i) = idemBasis φ (γ • i)
  rw [hsi γ i]
  exact centerRep'_apply_idemBasis φ (ψ γ) i

-- See `card_orbits_classes_eq_card_orbits_simples` for why the in-type linters are suppressed.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The orbit-count Brauer equality for a `Γ`-action** (factoring through `ψ : Γ →* MulAut G`):
`#(Γ-orbits on ConjClasses G) = #(Γ-orbits on Fin N)`.  Both equal `dim Z(k[G])^Γ`.  Specialises the
full-`MulAut G` equality; for `Γ = ↥(Subgroup.zpowers e)` (with `ψ = Subgroup.subtype` and the
`compHom` action on `Fin N`) the agreement hypotheses `hcl`/`hsi` hold by `rfl`. -/
theorem card_orbits_classes_eq_card_orbits_simples_comp
    [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]
    [MulAction Γ (ConjClasses G)] [MulAction Γ (Fin N)]
    (hcl : ∀ (γ : Γ) (C : ConjClasses G), γ • C = ψ γ • C)
    (hsi : ∀ (γ : Γ) (i : Fin N), γ • i = simplesAction φ (ψ γ) i) :
    Nat.card (orbitRel.Quotient Γ (ConjClasses G)) = Nat.card (orbitRel.Quotient Γ (Fin N)) := by
  rw [← finrank_centerRepComp_invariants_eq_card_orbits_classes (k := k) ψ hcl]
  exact finrank_centerRepComp_invariants_eq_card_orbits_simples (k := k) φ ψ hsi

end CompOrbitCount

/-! ### The trivial simple is a `MulAut G`-fixed point (Peterfalvi (9.1), step 3d.3b)

The trivial central character of `k[G]` is the **augmentation** `aug : Z(k[G]) →ₐ[k] k`, the
restriction of `MonoidAlgebra.lift 1` (the algebra hom sending each `single g 1 ↦ 1`).  It is
invariant under every `centerRep α` (`α` permutes `G` without changing the sum of coefficients), and
a `k`-algebra hom `(Fin N → k) →ₐ[k] k` is evaluation at a single coordinate
(`PiAlgebraAut.algHom_pi_eq_eval`).  Transporting `aug` through the splitting `φ` names that
coordinate `i₀`; invariance then forces `simplesAction φ α i₀ = i₀` for every `α` — so `i₀` is the
**fixed simple**, the one 3d.3c pairs with the fixed (trivial) class. -/

/-- The **augmentation** of `Z(k[G])`: `MonoidAlgebra.lift 1` (sending `single g c ↦ c`) restricted
to the centre — the trivial central character, as a `k`-algebra hom `Z(k[G]) →ₐ[k] k`. -/
noncomputable def aug : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  (MonoidAlgebra.lift k k G 1).comp (Subalgebra.center k (MonoidAlgebra k G)).val

theorem aug_apply (z : Subalgebra.center k (MonoidAlgebra k G)) :
    aug z = MonoidAlgebra.lift k k G 1 (z : MonoidAlgebra k G) := rfl

/-- The augmentation `MonoidAlgebra.lift 1` is unchanged by the basis permutation `domCongrAut α`:
both algebra homs `k[G] →ₐ[k] k` send each `single g 1 ↦ 1`. -/
theorem lift_one_comp_domCongrAut (α : MulAut G) :
    (MonoidAlgebra.lift k k G 1).comp
        (MonoidAlgebra.domCongrAut (R := k) (A := k) α).toAlgHom
      = MonoidAlgebra.lift k k G 1 := by
  refine MonoidAlgebra.algHom_ext fun g => ?_
  rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    show MonoidAlgebra.domCongrAut (R := k) (A := k) α (MonoidAlgebra.single g (1 : k))
        = MonoidAlgebra.single (α g) (1 : k) from MonoidAlgebra.domCongr_single α g 1,
    MonoidAlgebra.lift_single, MonoidAlgebra.lift_single, MonoidHom.one_apply, MonoidHom.one_apply]

/-- `aug` is `centerRep`-invariant: `aug (centerRep α z) = aug z`.  Indeed
`(centerRep α z : k[G]) = domCongrAut α (z : k[G])`, and `aug = lift 1` is
`domCongrAut`-invariant (`lift_one_comp_domCongrAut`). -/
theorem aug_centerRep (α : MulAut G) (z : Subalgebra.center k (MonoidAlgebra k G)) :
    aug (centerRep α z) = aug z := by
  rw [aug_apply, aug_apply]
  have hval : ((centerRep α z : Subalgebra.center k (MonoidAlgebra k G)) : MonoidAlgebra k G)
      = MonoidAlgebra.domCongrAut (R := k) (A := k) α (z : MonoidAlgebra k G) := rfl
  rw [hval]
  exact DFunLike.congr_fun (lift_one_comp_domCongrAut (k := k) α) (z : MonoidAlgebra k G)

/-- **The trivial simple is a fixed point** (Peterfalvi (9.1), step 3d.3b).  There is a coordinate
`i₀ : Fin N` — the augmentation / trivial central character, read off through the splitting `φ` —
with `simplesAction φ α i₀ = i₀` for **every** `α : MulAut G`.  This is the fixed simple that 3d.3c
pairs with the fixed (trivial) class to conclude `E` acts freely on the *nontrivial* simples. -/
theorem exists_fixed_simple :
    ∃ i₀ : Fin N, ∀ α : MulAut G, simplesAction φ α i₀ = i₀ := by
  classical
  obtain ⟨i₀, hi₀⟩ := PiAlgebraAut.algHom_pi_eq_eval (aug.comp φ.symm.toAlgHom)
  -- `aug` at the transported idempotent `φ.symm (Pi.single j 1)` reads off coordinate `i₀`.
  have hread : ∀ j : Fin N,
      aug (φ.symm (Pi.single j (1 : k))) = (Pi.single j (1 : k) : Fin N → k) i₀ := by
    intro j
    have h := hi₀ (Pi.single j (1 : k))
    rwa [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at h
  refine ⟨i₀, fun α => ?_⟩
  have e1 : aug (φ.symm (Pi.single i₀ (1 : k))) = 1 := by rw [hread i₀, Pi.single_eq_same]
  -- invariance + the permutation: `aug` at the `α`-image of the fixed idempotent is also `1`.
  have e2 : aug (φ.symm (Pi.single (simplesAction φ α i₀) (1 : k))) = 1 := by
    rw [← centerRep_apply_symm_single φ α i₀, aug_centerRep, e1]
  rw [hread] at e2
  by_contra hne
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at e2
  exact one_ne_zero e2.symm

end OddOrder.GroupTheory.CenterSimplesOrbit
