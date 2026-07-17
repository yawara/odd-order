/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordAlgClosed
import OddOrder.GroupTheory.RepresentationTheory.CliffordMultiplicityOne
import OddOrder.GroupTheory.RepresentationTheory.SimpleSubmoduleIndependence
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The restriction as a direct sum of conjugates (BG Lemma 2.3, case (ii))

`OddOrder.GroupTheory.RepresentationTheory` shared module: the "dimension brick" of the case
`L ≇ L^x` in **Bender–Glauberman Lemma 2.3** (Fong–Swan), tracked in `issues/3008`.

Setup: `ρ : Representation k G V` is irreducible over an algebraically closed field `k`, `V` is
finite-dimensional and nontrivial, `H ⊴ G` has *prime* index `p = [G:H]`, and `G = ⟨H, x⟩`.  Let `W`
be a nonzero simple `k[H]`-submodule of the restriction `Res^G_H ρ` that is **not** isomorphic to
its `x`-conjugate `W^x = W.map (conjSemilinearEnd ρ x)`.

Then the restriction decomposes as the internal direct sum of the `p` conjugates
`W, W^x, …, W^{x^{p-1}}`, which are pairwise non-isomorphic simple `k[H]`-modules of equal
`k`-dimension, whence `dim_k V = p · dim_k W = [G:H] · dim_k W`.

## Proof outline

* `transportConj` — a `k[H]`-linear equivalence `A ≃ₗ[k[H]] B` transports to
  `A.map (ρ g) ≃ₗ[k[H]] B.map (ρ g)` by conjugating with the semilinear bijection `ρ g` (the two
  conjugation twists cancel, leaving a genuine `k[H]`-linear map).
* `conjKLinEquiv` — `ρ g` restricts to a `k`-linear (not merely additive) equivalence
  `W ≃ₗ[k] W.map (ρ g)`, since the twist fixes the scalars `k`.  So all conjugates share a
  `k`-dimension.
* `conjStab` — the set of `g` with `W ≅ W^g` is a subgroup of `G` containing `H`; since `[G:H]` is
  prime and `x` is *not* in it, it equals `H`.  This yields the pairwise non-isomorphism of the `p`
  conjugates (their iso-classes have trivial `⟨xH⟩`-stabiliser).
* Independence (`iSupIndep_of_pairwise_not_linearEquiv_of_isSimpleModule`) plus spanning
  (`iSup_map_conjSemilinearEnd_eq_top`) give an internal direct sum, and the dimensions add up.
-/

namespace OddOrder.RepresentationTheory

open Representation
open scoped MonoidAlgebra DirectSum
open Module (finrank)

variable {k : Type*} [Field k]
variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]

section Conjugates

variable (ρ : Representation k G V) {H : Subgroup G} [H.Normal]

/-- The ring automorphisms `conjMonoidAlgRingHom g` and `conjMonoidAlgRingHom g⁻¹` of `k[H]` form an
inverse pair. -/
instance conjMonoidAlgRingHom_invPair (g : G) :
    RingHomInvPair (conjMonoidAlgRingHom (k := k) (H := H) g)
      (conjMonoidAlgRingHom (k := k) (H := H) g⁻¹) where
  comp_eq := RingHom.ext fun r => by
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    have := conjMonoidAlgRingHom_conj_inv (k := k) (H := H) g⁻¹ r
    rwa [inv_inv] at this
  comp_eq₂ := RingHom.ext fun r => by
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    exact conjMonoidAlgRingHom_conj_inv (k := k) (H := H) g r

/-- The reverse inverse pair (needed because the `outParam` prevents the previous instance from
covering both orders for a fixed `g`). -/
instance conjMonoidAlgRingHom_invPair' (g : G) :
    RingHomInvPair (conjMonoidAlgRingHom (k := k) (H := H) g⁻¹)
      (conjMonoidAlgRingHom (k := k) (H := H) g) where
  comp_eq := RingHom.ext fun r => by
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    exact conjMonoidAlgRingHom_conj_inv (k := k) (H := H) g r
  comp_eq₂ := RingHom.ext fun r => by
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    have := conjMonoidAlgRingHom_conj_inv (k := k) (H := H) g⁻¹ r
    rwa [inv_inv] at this

/-- **Transport of a `k[H]`-linear isomorphism by conjugation.**  If `A ≃ₗ[k[H]] B` are isomorphic
`k[H]`-submodules of the restriction, then their `ρ g`-images `A.map (ρ g)` and `B.map (ρ g)` are
also `k[H]`-linearly isomorphic.  Conjugating a `k[H]`-linear map by the `conjMonoidAlgRingHom g`-
semilinear bijection `ρ g` cancels the two ring twists, so the composite is again `k[H]`-linear. -/
noncomputable def transportConj (g : G) {A B : Submodule k[↥H] (resRep ρ H).asModule}
    (φ : A ≃ₗ[k[↥H]] B) :
    A.map (conjSemilinearEnd (H := H) ρ g) ≃ₗ[k[↥H]] B.map (conjSemilinearEnd (H := H) ρ g) :=
  ((Submodule.equivMapOfInjective (conjSemilinearEnd (H := H) ρ g)
        (conjSemilinearEnd_bijective (H := H) ρ g).injective A).symm.trans φ).trans
    (Submodule.equivMapOfInjective (conjSemilinearEnd (H := H) ρ g)
        (conjSemilinearEnd_bijective (H := H) ρ g).injective B)

/-- **The conjugates all have the same `k`-dimension.**  The semilinear bijection `ρ g`
(`conjSemilinearEnd ρ g`) is `k`-linear because the conjugation twist fixes the scalars, so its
restriction is a genuine `k`-linear equivalence `W ≃ₗ[k] W.map (ρ g)`. -/
noncomputable def conjKLinEquiv (g : G) (W : Submodule k[↥H] (resRep ρ H).asModule) :
    (W : Type _) ≃ₗ[k] (W.map (conjSemilinearEnd (H := H) ρ g) : Type _) :=
  let eSL := Submodule.equivMapOfInjective (conjSemilinearEnd (H := H) ρ g)
    (conjSemilinearEnd_bijective (H := H) ρ g).injective W
  { toFun := fun w => eSL w
    invFun := eSL.invFun
    left_inv := eSL.left_inv
    right_inv := eSL.right_inv
    map_add' := map_add eSL
    map_smul' := fun c w => by
      apply Subtype.ext
      change conjSemilinearEnd (H := H) ρ g (↑(c • w)) = c • conjSemilinearEnd (H := H) ρ g (↑w)
      rw [Submodule.coe_smul_of_tower, conjSemilinearEnd_smul_k] }

/-- For `h ∈ H`, the `ρ h`-image of a `k[H]`-submodule `N` is contained in `N` (the standard
`k[H]`-action already realises `ρ h` as scalar multiplication by `single h 1`). -/
theorem map_conjSemilinearEnd_le_of_mem (N : Submodule k[↥H] (resRep ρ H).asModule) (h : ↥H) :
    N.map (conjSemilinearEnd (H := H) ρ (h : G)) ≤ N := by
  intro w hw
  rw [Submodule.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  have hsmul : MonoidAlgebra.single h (1 : k) • v = conjSemilinearEnd (H := H) ρ (h : G) v := by
    simp only [Representation.single_smul, one_smul, resRep_apply, conjSemilinearEnd_apply]
    rfl
  rw [← hsmul]
  exact N.smul_mem _ hv

/-- For `h ∈ H`, conjugation by `ρ h` fixes every `k[H]`-submodule `N`. -/
theorem map_conjSemilinearEnd_of_mem (N : Submodule k[↥H] (resRep ρ H).asModule) (h : ↥H) :
    N.map (conjSemilinearEnd (H := H) ρ (h : G)) = N := by
  refine le_antisymm (map_conjSemilinearEnd_le_of_mem ρ N h) ?_
  have hle_inv := map_conjSemilinearEnd_le_of_mem ρ N h⁻¹
  have hcoe : ((h⁻¹ : ↥H) : G) = (h : G)⁻¹ := by simp
  rw [hcoe] at hle_inv
  calc N = N.map (conjSemilinearEnd (H := H) ρ (1 : G)) := (map_conjSemilinearEnd_one ρ N).symm
    _ = N.map (conjSemilinearEnd (H := H) ρ ((h : G) * (h : G)⁻¹)) := by rw [mul_inv_cancel]
    _ = (N.map (conjSemilinearEnd (H := H) ρ (h : G)⁻¹)).map
          (conjSemilinearEnd (H := H) ρ (h : G)) :=
        (map_map_conjSemilinearEnd ρ N (h : G) (h : G)⁻¹).symm
    _ ≤ N.map (conjSemilinearEnd (H := H) ρ (h : G)) := Submodule.map_mono hle_inv

/-- **The conjugacy stabiliser of a `k[H]`-submodule `W`.**  The subgroup of `g : G` such that the
`ρ g`-conjugate `W^g = W.map (ρ g)` is `k[H]`-linearly isomorphic to `W`.  It contains `H`
(`map_conjSemilinearEnd_of_mem`), and is closed under the group operations via `transportConj`. -/
noncomputable def conjStab (W : Submodule k[↥H] (resRep ρ H).asModule) : Subgroup G where
  carrier := {g : G | Nonempty (W ≃ₗ[k[↥H]] W.map (conjSemilinearEnd (H := H) ρ g))}
  one_mem' := ⟨LinearEquiv.ofEq _ _ (map_conjSemilinearEnd_one ρ W).symm⟩
  mul_mem' := by
    rintro a b ⟨φ⟩ ⟨ψ⟩
    exact ⟨φ.trans ((transportConj ρ a ψ).trans
      (LinearEquiv.ofEq _ _ (map_map_conjSemilinearEnd ρ W a b)))⟩
  inv_mem' := by
    rintro a ⟨φ⟩
    refine ⟨((transportConj ρ a⁻¹ φ).trans (LinearEquiv.ofEq _ _ ?_)).symm⟩
    rw [map_map_conjSemilinearEnd, inv_mul_cancel, map_conjSemilinearEnd_one]

theorem mem_conjStab_iff (W : Submodule k[↥H] (resRep ρ H).asModule) (g : G) :
    g ∈ conjStab ρ W ↔ Nonempty (W ≃ₗ[k[↥H]] W.map (conjSemilinearEnd (H := H) ρ g)) :=
  Iff.rfl

theorem le_conjStab (W : Submodule k[↥H] (resRep ρ H).asModule) : H ≤ conjStab ρ W := by
  intro h hh
  exact ⟨LinearEquiv.ofEq _ _ (map_conjSemilinearEnd_of_mem ρ W ⟨h, hh⟩).symm⟩

end Conjugates

section MainTheorem

variable (ρ : Representation k G V) {H : Subgroup G} [H.Normal]

set_option backward.isDefEq.respectTransparency false in
/-- **BG Lemma 2.3, case (ii): the "dimension brick".**  Over an algebraically closed field `k`,
let `ρ` be an irreducible representation of a finite group `G`, `V` finite-dimensional and
nontrivial, `H ⊴ G` of prime index with `G = ⟨H, x⟩`, and `W` a nonzero simple `k[H]`-submodule of
the restriction whose `x`-conjugate is **not** isomorphic to it.  Then the restriction is the direct
sum of the `[G:H]` conjugates of `W`, so `dim_k V = [G:H] · dim_k W`. -/
theorem finrank_eq_index_mul_finrank_of_not_linearEquiv_conj
    [Finite G]
    [ρ.IsIrreducible] [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hp : (H.index).Prime)
    (W : Submodule k[↥H] (resRep ρ H).asModule) (hWne : W ≠ ⊥)
    [IsSimpleModule k[↥H] W]
    (hnotconj : ¬ Nonempty
      (W ≃ₗ[k[↥H]] W.map (conjSemilinearEnd (H := H) ρ x))) :
    Module.finrank k V = H.index * Module.finrank k W := by
  -- The conjugate family `W' i = W^{x^i}`.
  set W' : Fin (H.index) → Submodule k[↥H] (resRep ρ H).asModule :=
    fun i => W.map (conjSemilinearEnd (H := H) ρ (x ^ (i : ℕ))) with hW'
  -- Quotient bookkeeping: `a = xH` has order `p = [G:H]` in the cyclic group `G ⧸ H`.
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hidx : H.index = Nat.card (G ⧸ H) := rfl
  have hcardQ : Fintype.card (G ⧸ H) = H.index := by rw [hidx, Nat.card_eq_fintype_card]
  set a : G ⧸ H := QuotientGroup.mk' H x with ha_def
  have hxnotH : x ∉ H := by
    intro hxH
    have hunion : ((H : Set G) ∪ {x}) = (H : Set G) :=
      Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hxH)
    have hHtop : (⊤ : Subgroup G) = H := by rw [← hgen, hunion, Subgroup.closure_eq]
    rw [← hHtop, Subgroup.index_top] at hp
    exact Nat.not_prime_one hp
  have ha1 : a ≠ 1 := fun h => hxnotH ((QuotientGroup.eq_one_iff x).mp h)
  have horder : orderOf a = H.index := by
    have hdvd : orderOf a ∣ H.index := by rw [hidx]; exact orderOf_dvd_natCard a
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h1
  -- `i ↦ a^i` is a bijection `Fin p ≃ G ⧸ H`.
  have hinj : Function.Injective (fun i : Fin (H.index) => a ^ (i : ℕ)) := by
    intro i j hij
    have hi : (i : ℕ) < orderOf a := by rw [horder]; exact i.isLt
    have hj : (j : ℕ) < orderOf a := by rw [horder]; exact j.isLt
    exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) hij)
  have hsurj : Function.Surjective (fun i : Fin (H.index) => a ^ (i : ℕ)) :=
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, hcardQ]⟩).surjective
  -- `conjStab W = H`: it contains `H`, has prime index cofactor, and excludes `x`.
  have hHle : H ≤ conjStab ρ W := le_conjStab ρ W
  have hSle : conjStab ρ W ≤ H := by
    have hmul := Subgroup.relIndex_mul_index hHle
    have hdvd : (conjStab ρ W).index ∣ H.index :=
      ⟨H.relIndex (conjStab ρ W), by rw [Nat.mul_comm]; exact hmul.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpp
    · refine absurd ?_ hnotconj
      have hxS : x ∈ conjStab ρ W := by rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top x
      exact (mem_conjStab_iff ρ W x).mp hxS
    · have hrel1 : H.relIndex (conjStab ρ W) = 1 := by
        rw [hpp] at hmul
        exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [one_mul]; exact hmul)
      exact Subgroup.relIndex_eq_one.mp hrel1
  -- Each conjugate is simple.
  have hsimple : ∀ i, IsSimpleModule k[↥H] (W' i) := by
    intro i
    rw [hW']
    exact isSimpleModule_map_conjSemilinearEnd ρ (x ^ (i : ℕ)) W
  -- Pairwise non-isomorphic (trivial `⟨xH⟩`-stabiliser).
  have hpair : ∀ i j : Fin (H.index), i ≠ j → ¬ Nonempty (W' i ≃ₗ[k[↥H]] W' j) := by
    rintro i j hij ⟨φ⟩
    have htr := transportConj ρ (x ^ (i : ℕ))⁻¹ φ
    have hLi : (W' i).map (conjSemilinearEnd (H := H) ρ (x ^ (i : ℕ))⁻¹) = W := by
      change (W.map (conjSemilinearEnd (H := H) ρ (x ^ (i : ℕ)))).map
        (conjSemilinearEnd (H := H) ρ (x ^ (i : ℕ))⁻¹) = W
      rw [map_map_conjSemilinearEnd, inv_mul_cancel, map_conjSemilinearEnd_one]
    have hLj : (W' j).map (conjSemilinearEnd (H := H) ρ (x ^ (i : ℕ))⁻¹) =
        W.map (conjSemilinearEnd (H := H) ρ ((x ^ (i : ℕ))⁻¹ * x ^ (j : ℕ))) := by
      change (W.map (conjSemilinearEnd (H := H) ρ (x ^ (j : ℕ)))).map
        (conjSemilinearEnd (H := H) ρ (x ^ (i : ℕ))⁻¹) = _
      rw [map_map_conjSemilinearEnd]
    have hconjmem : (x ^ (i : ℕ))⁻¹ * x ^ (j : ℕ) ∈ conjStab ρ W :=
      ⟨(LinearEquiv.ofEq _ _ hLi).symm.trans (htr.trans (LinearEquiv.ofEq _ _ hLj))⟩
    have hHmem : (x ^ (i : ℕ))⁻¹ * x ^ (j : ℕ) ∈ H := hSle hconjmem
    have hpow : a ^ (i : ℕ) = a ^ (j : ℕ) := by
      have h1 : (QuotientGroup.mk' H) ((x ^ (i : ℕ))⁻¹ * x ^ (j : ℕ)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hHmem
      rw [map_mul, map_inv, map_pow, map_pow, ← ha_def] at h1
      exact (inv_mul_eq_one.mp h1)
    exact hij (hinj hpow)
  -- Independence and spanning give an internal direct sum.
  have hindep : iSupIndep W' :=
    iSupIndep_of_pairwise_not_linearEquiv_of_isSimpleModule W' hsimple hpair
  have htop : ⨆ i, W' i = ⊤ := by
    rw [eq_top_iff, ← iSup_map_conjSemilinearEnd_eq_top ρ W hWne]
    refine iSup_le fun g => ?_
    obtain ⟨i, hi⟩ := hsurj (QuotientGroup.mk' H g)
    have hmem : (x ^ (i : ℕ))⁻¹ * g ∈ H := by
      have h1 : (QuotientGroup.mk' H) ((x ^ (i : ℕ))⁻¹ * g) = 1 := by
        have hi2 : a ^ (i : ℕ) = QuotientGroup.mk' H g := hi
        rw [map_mul, map_inv, map_pow, ← ha_def, hi2, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hg : x ^ (i : ℕ) * ((x ^ (i : ℕ))⁻¹ * g) = g := by group
    have hkey : (W.map (conjSemilinearEnd (H := H) ρ ((x ^ (i : ℕ))⁻¹ * g))).map
        (conjSemilinearEnd (H := H) ρ (x ^ (i : ℕ))) = W.map (conjSemilinearEnd (H := H) ρ g) := by
      rw [map_map_conjSemilinearEnd, hg]
    have hWinv : W.map (conjSemilinearEnd (H := H) ρ ((x ^ (i : ℕ))⁻¹ * g)) = W :=
      map_conjSemilinearEnd_of_mem ρ W ⟨(x ^ (i : ℕ))⁻¹ * g, hmem⟩
    have hval : W.map (conjSemilinearEnd (H := H) ρ g) = W' i := by
      rw [hW', ← hkey, hWinv]
    rw [hval]
    exact le_iSup W' i
  haveI : DirectSum.IsInternal W' :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W').mpr ⟨hindep, htop⟩
  -- Assemble the `k`-dimension.
  haveI hfin : ∀ i, Module.Finite k (W' i) := fun i =>
    Module.Finite.of_injective ((W' i).subtype.restrictScalars k) Subtype.val_injective
  have e : (⨁ i, (W' i : Type _)) ≃ₗ[k[↥H]] (resRep ρ H).asModule :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap W') ‹DirectSum.IsInternal W'›
  have hfr : ∀ i, Module.finrank k (W' i) = Module.finrank k W := by
    intro i
    rw [hW']
    exact (conjKLinEquiv ρ (x ^ (i : ℕ)) W).finrank_eq.symm
  calc Module.finrank k V
      = Module.finrank k (resRep ρ H).asModule :=
        ((resRep ρ H).asModuleEquiv.finrank_eq).symm
    _ = Module.finrank k (⨁ i, (W' i : Type _)) :=
        (LinearEquiv.finrank_eq (e.restrictScalars k)).symm
    _ = ∑ i, Module.finrank k (W' i) :=
        Module.finrank_directSum k (fun i => (W' i : Type _))
    _ = ∑ _i : Fin (H.index), Module.finrank k W := Finset.sum_congr rfl (fun i _ => hfr i)
    _ = H.index * Module.finrank k W := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end MainTheorem

end OddOrder.RepresentationTheory
