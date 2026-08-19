/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.NormalPSubgroupTrivialAction
import OddOrder.GroupTheory.PRegularQuotient
import OddOrder.GroupTheory.RepresentationTheory.Modular.IrreducibleBrauerCharacter

/-!
# The splitting of `k[G/P]` induced by a splitting of `k[G]`

Second step of Navarro (7.6).  Let `N ⊴ G` be a `p`-subgroup and `char k = p`.  A normal
`p`-subgroup acts trivially on every simple `kG`-module (`pi_single_eq_one_of_mem_normal_pSubgroup`,
Navarro (2.32)), so a splitting

`π : kG ↠ ∏_{j ∈ ι} M_{n_j}(k)`  with  `ker π = J(kG)`

factors through `k[G/N]`, and the factorisation is again such a splitting — **with the same index
set `ι` and the same matrix sizes**.  That is the formal content of Navarro's "`φ ↦ φ̄` is a
bijection from `IBr(G)` onto `IBr(Ḡ)`": the two sets of irreducible Brauer characters are indexed
by the same `ι`, and the corresponding characters agree under `g ↦ ḡ`.

The Jacobson condition transports because `f : kG ↠ k[G/N]` is surjective with
`ker f ≤ ker π = J(kG)`, so `Ring.map_jacobson_of_ker_le` gives `f(J(kG)) = J(k[G/N])`, while
`ker π̄` is exactly `f(ker π)`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.blockPiHom` — `g ↦ π (single g 1)` as a monoid hom
* `OddOrder.RepresentationTheory.Modular.quotientMap` — the surjection `kG ↠ k[G/N]`
* `OddOrder.RepresentationTheory.Modular.quotientPi` — the induced splitting of `k[G/N]`

## Main results

* `OddOrder.RepresentationTheory.Modular.quotientPi_mapDomain` — `π̄ ∘ f = π`
* `OddOrder.RepresentationTheory.Modular.quotientPi_surjective`
* `OddOrder.RepresentationTheory.Modular.ker_quotientPi`
* `OddOrder.RepresentationTheory.Modular.irreducibleBrauerCharacter_quotientPi` — `φ(g) = φ̄(ḡ)`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

section GeneralField

variable {k ι G : Type*} [Field k] [Group G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
section QuotientMap

variable {N : Subgroup G} [N.Normal]

/-- The surjection `kG ↠ k[G/N]` induced by `G ↠ G/N`. -/
noncomputable abbrev quotientMap :
    MonoidAlgebra k G →ₐ[k] MonoidAlgebra k (G ⧸ N) :=
  mapDomainAlgHom k k (QuotientGroup.mk' N)

theorem quotientMap_surjective :
    Function.Surjective (quotientMap (k := k) (G := G) (N := N)) := fun y => by
  obtain ⟨c, hc⟩ := Finsupp.mapDomain_surjective (QuotientGroup.mk'_surjective N) y.coeff
  refine ⟨MonoidAlgebra.ofCoeff c, ?_⟩
  apply MonoidAlgebra.coeff_injective
  simpa using hc

instance : RingHomSurjective (quotientMap (k := k) (G := G) (N := N)).toRingHom :=
  ⟨quotientMap_surjective⟩

end QuotientMap

variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k)

/-- **The group elements as matrices**: `g ↦ π (single g 1)`, a monoid homomorphism into the
split semisimple quotient. -/
noncomputable def blockPiHom : G →* ∀ j, Matrix (nn j) (nn j) k where
  toFun g := π (single g (1 : k))
  map_one' := by rw [← MonoidAlgebra.one_def, map_one]
  map_mul' g h := by rw [← map_mul, single_mul_single, one_mul]

@[simp]
theorem blockPiHom_apply (g : G) : blockPiHom π g = π (single g (1 : k)) := rfl

variable [∀ i, Nonempty (nn i)] [Finite G]
variable {p : ℕ} [Fact p.Prime] [CharP k p] {N : Subgroup G} [N.Normal]
variable (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
  (hN : IsPGroup p ↥N)

include hπ hlin hN in
/-- A normal `p`-subgroup is killed by `blockPiHom` — Navarro (2.32). -/
theorem blockPiHom_eq_one_of_mem {u : G} (hu : u ∈ N) : blockPiHom π u = 1 :=
  funext fun i =>
    OddOrder.GroupAlgebra.pi_single_eq_one_of_mem_normal_pSubgroup π hπ hlin hN i hu

/-- **The splitting of `k[G/N]` induced by `π`.**  Its existence is Navarro (2.32): the group
homomorphism `g ↦ π (single g 1)` kills `N`, so it factors through `G/N`, and the universal
property of the group algebra turns the factorisation into an algebra map. -/
noncomputable def quotientPi :
    MonoidAlgebra k (G ⧸ N) →ₐ[k] ∀ j, Matrix (nn j) (nn j) k :=
  MonoidAlgebra.lift k (∀ j, Matrix (nn j) (nn j) k) (G ⧸ N)
    (QuotientGroup.lift N (blockPiHom π) fun _ hu => blockPiHom_eq_one_of_mem π hπ hlin hN hu)

include hπ hlin hN in
@[simp]
theorem quotientPi_single (g : G) :
    quotientPi π hπ hlin hN (single (QuotientGroup.mk g : G ⧸ N) (1 : k))
      = π (single g (1 : k)) := by
  rw [quotientPi, MonoidAlgebra.lift_single, one_smul]
  rfl

include hπ hlin hN in
/-- **`π̄ ∘ f = π`** for `f : kG ↠ k[G/N]` the map induced by `G ↠ G/N`. -/
theorem quotientPi_mapDomain (x : MonoidAlgebra k G) :
    quotientPi π hπ hlin hN (quotientMap x) = π x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      rw [show (MonoidAlgebra.of k G g : MonoidAlgebra k G) = single g (1 : k) from rfl,
        show quotientMap (single g (1 : k))
          = single (QuotientGroup.mk g : G ⧸ N) (1 : k) from MonoidAlgebra.mapDomain_single,
        quotientPi_single]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => rw [map_smul, map_smul, hx, hlin]

include hπ hlin hN in
theorem quotientPi_surjective : Function.Surjective (quotientPi π hπ hlin hN) := fun y => by
  obtain ⟨x, hx⟩ := hπ y
  exact ⟨quotientMap x, by rw [quotientPi_mapDomain π hπ hlin hN, hx]⟩

include hπ hlin hN in
theorem quotientPi_smul (c : k) (a : MonoidAlgebra k (G ⧸ N)) :
    quotientPi π hπ hlin hN (c • a) = c • quotientPi π hπ hlin hN a :=
  map_smul _ _ _

/-! ### The Jacobson condition transports -/

include hπ hlin hN in
/-- `ker π̄` is the image of `ker π`: the map `kG ↠ k[G/N]` is surjective and `π = π̄ ∘ f`. -/
theorem ker_quotientPi_eq_map :
    RingHom.ker (quotientPi π hπ hlin hN).toRingHom
      = Submodule.map (quotientMap (k := k) (G := G) (N := N)).toRingHom.toSemilinearMap
          (RingHom.ker π) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := quotientMap_surjective (k := k) (G := G) (N := N) y
    exact ⟨x, SetLike.mem_coe.mpr (RingHom.mem_ker.mpr
      (by rw [← quotientPi_mapDomain π hπ hlin hN x]; exact hy)), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (quotientPi_mapDomain π hπ hlin hN x).trans (RingHom.mem_ker.mp hx)

include hπ hlin hN in
/-- **The induced splitting again has kernel the Jacobson radical.**  This is what makes
`quotientPi` a splitting of `k[G/N]` in the sense the block theory of this development uses. -/
theorem ker_quotientPi (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra k G)) :
    RingHom.ker (quotientPi π hπ hlin hN).toRingHom
      = Ring.jacobson (MonoidAlgebra k (G ⧸ N)) := by
  have hle : RingHom.ker (quotientMap (k := k) (G := G) (N := N)).toRingHom
      ≤ Ring.jacobson (MonoidAlgebra k G) := by
    rw [← hkerJ]
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [← quotientPi_mapDomain π hπ hlin hN x,
      show quotientMap (k := k) (G := G) (N := N) x = 0 from hx, map_zero]
  rw [ker_quotientPi_eq_map π hπ hlin hN, hkerJ, Ring.map_jacobson_of_ker_le hle]

end GeneralField

/-! ### The irreducible Brauer characters correspond -/

section BrauerCharacter

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
  [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
  {N : Subgroup G} [N.Normal]
  (π : MonoidAlgebra (IsLocalRing.ResidueField 𝒪) G →+*
    ∀ j, Matrix (nn j) (nn j) (IsLocalRing.ResidueField 𝒪))
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : IsLocalRing.ResidueField 𝒪) (a : MonoidAlgebra (IsLocalRing.ResidueField 𝒪) G),
    π (c • a) = c • π a)
  (hN : IsPGroup p ↥N)

omit [IsPModularSystem p 𝒪] in
include hπ hlin hN in
/-- **The block representations correspond**: the matrix attached to `ḡ` by the induced splitting
is the one attached to `g` by `π`. -/
theorem blockRepresentation_quotientPi (i : ι) (g : G) :
    blockRepresentation (quotientPi π hπ hlin hN).toRingHom i (QuotientGroup.mk g : G ⧸ N)
      = blockRepresentation π i g := by
  rw [show blockRepresentation (quotientPi π hπ hlin hN).toRingHom i
        (QuotientGroup.mk g : G ⧸ N)
      = Matrix.mulVecLin ((quotientPi π hπ hlin hN).toRingHom
          (MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ N)
            (1 : IsLocalRing.ResidueField 𝒪)) i) from rfl,
    show blockRepresentation π i g
      = Matrix.mulVecLin (π (MonoidAlgebra.single g (1 : IsLocalRing.ResidueField 𝒪)) i) from rfl,
    show (quotientPi π hπ hlin hN).toRingHom
      (MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ N) (1 : IsLocalRing.ResidueField 𝒪))
      = π (MonoidAlgebra.single g (1 : IsLocalRing.ResidueField 𝒪)) from
    quotientPi_single π hπ hlin hN g]

omit [IsPModularSystem p 𝒪] in
include hπ hlin hN in
/-- **Navarro (7.6): `φ(g) = φ̄(ḡ)`.**  The irreducible Brauer characters of `G` and of `G/N` are
indexed by the same set and take the same values under `g ↦ ḡ`: the two `p`-regular exponents
agree (`pRegularExponent_quotient`) and the operators are literally the same
(`blockRepresentation_quotientPi`). -/
theorem irreducibleBrauerCharacter_quotientPi (i : ι) (g : G) :
    irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) (quotientPi π hπ hlin hN).toRingHom i
        (QuotientGroup.mk g : G ⧸ N)
      = irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g := by
  rw [irreducibleBrauerCharacter, irreducibleBrauerCharacter, brauerCharacter, brauerCharacter,
    OddOrder.GroupTheory.pRegularExponent_quotient hN,
    blockRepresentation_quotientPi π hπ hlin hN i g]

end BrauerCharacter

end OddOrder.RepresentationTheory.Modular
