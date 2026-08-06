/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockOfIrreducible
import OddOrder.GroupTheory.RepresentationTheory.Modular.PSection
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBlockForm

/-!
# Navarro (5.10): the `B`-parts inherit vanishing on a `p`-section

If a class function `θ` vanishes on the `p`-section `S(x)`, then so does every `B`-part `θ_B`.

The argument is the one Navarro gives on pp. 105–106.  Write `c_χ` for the coefficients of `θ` in
`Irr(G)` and `d^x_{χφ}` for the generalized decomposition numbers.  For `p`-regular `y ∈ C_G(x)`,

`θ_B(xy) = ∑_φ (∑_{χ ∈ Irr(B)} c_χ d^x_{χφ}) φ(y)`,

so it is enough to see that the inner sum vanishes for every `φ`.  Vanishing of `θ` on `S(x)` and
independence of `IBr(C_G(x))` give `∑_{χ ∈ Irr(G)} c_χ d^x_{χφ} = 0`, and Brauer's second main
theorem (5.8) kills one of the two halves of that sum:

* if the block of `φ` does not induce `B`, then `d^x_{χφ} = 0` for `χ ∈ Irr(B)` — the inner sum is
  already zero;
* if it does, then `d^x_{χφ} = 0` for `χ ∉ Irr(B)`, so the inner sum is the whole sum, which is
  zero.

Navarro (5.11) — **block orthogonality** — follows at once: apply (5.10) to
`θ = ∑_χ χ(h⁻¹) χ`, which by the second orthogonality relation vanishes off the class of `h`, in
particular on the `p`-section of `g_p` when `g_p` and `h_p` are not conjugate.

## Main results

* `OddOrder.RepresentationTheory.Modular.blockPart_eq_zero_of_forall_pSection` — Navarro (5.10)
* `OddOrder.RepresentationTheory.Modular.sum_character_blockOfIrr_eq_zero` — Navarro (5.11)
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open scoped TensorProduct

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)]
-- `Irr(G)`, through the Wedderburn splitting of `KG`
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
-- `IBr(C_G(x))` and `Irr(C_G(x))`
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ιH : Type*} {mH : ιH → Type*} [∀ i, Fintype (mH i)] [∀ i, DecidableEq (mH i)]
  [Finite ιH] [∀ i, Nonempty (mH i)]
-- `Bl(G)`
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]

set_option maxHeartbeats 1600000 in
-- The statement carries the two ordinary splittings, the two modular splittings and the block
-- machinery; unifying those instance chains is what costs the heartbeats.
-- The two `Fintype`s are consumed by the sums over `IBr(C_G(x))` and by (5.8) in the proof.
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **Navarro (5.10).**  If a class function `θ` of `G` vanishes on the `p`-section of a
`p`-element `x`, then so does each of its block parts `θ_B`. -/
theorem blockPart_eq_zero_of_forall_pSection (hp : p.Prime) {x : G} (hx : IsPElement p x)
    [Fintype ↥(centralizerOf x)]
    -- the Wedderburn splittings of `KG` and of `K C_G(x)`
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    (eH : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (mH i) (mH i) K)
    -- the modular splittings of `kG` and of `k C_G(x)`
    {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
    (hπG : Function.Surjective πG)
    (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
    (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    -- the class function and the block
    (θ : G → K) (hθ : ∀ g h : G, IsConj g h → θ g = θ h)
    (hvanish : ∀ u ∈ pSection p x, θ u = 0) (B : Block πG hπG hlinG) :
    ∀ u ∈ pSection p x, blockPart e hπG hlinG hnilG B θ hθ u = 0 := by
  classical
  -- the generalized decomposition numbers of the ordinary irreducibles
  set d : ι' → ι → K := fun i =>
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
      (wedderburnRepresentation e i).character
      (fun _ _ hgh => character_eq_of_isConj (wedderburnRepresentation e i) hgh) with hd
  set c : ι' → K := ordinaryCoeff e θ hθ with hc
  -- (5.8) for the `i`-th ordinary irreducible
  have hsecond : ∀ (i : ι') (j : ι),
      inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx
          (Quotient.mk (blockSetoid π hπ hlin) j) ≠ blockOfIrr e hπG hlinG hnilG i →
      d i j = 0 := fun i j hne =>
    generalizedDecompositionNumber_eq_zero_of_inducedBlockOfCentralizer_ne hp hx eH hπG
      hlinG hπ hlin hkerJ hnilH hnilG hω hω' hζ hζk hζK (wedderburnRepresentation e i)
      (invariant_wedderburnLattice e i) (exists_smul_id_of_commute_wedderburnLattice e i) hne
  -- the expansion of `θ` along the `p`-section
  have hexp : ∀ y : ↥(centralizerOf x), IsPRegular p y →
      ∑ j, (∑ i, c i * d i j) * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π j y) = θ (x * (y : G)) := by
    intro y hy
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _, Finset.sum_comm,
      ← sum_ordinaryCoeff e θ hθ (x * (y : G))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        (wedderburnRepresentation e i).character
        (fun _ _ hgh => character_eq_of_isConj (wedderburnRepresentation e i) hgh) hy,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  -- independence of `IBr(C_G(x))` pins the coefficients to zero
  have hzero : ∀ j, ∑ i, c i * d i j = 0 := by
    have hkey := eq_zero_of_sum_algebraMap_irreducibleBrauerCharacter (K := K) hp hω' hπ hlin
      hkerJ (fun j => ∑ i, c i * d i j) fun y hy => by
        rw [hexp y hy]
        exact hvanish _ (mul_mem_pSection hp ((Subgroup.mem_centralizer_iff.mp y.2) x rfl) hx
          (isPRegular_coe hy))
    exact fun j => congrFun hkey j
  -- the sums restricted to `Irr(B)` vanish too
  have hfilter : ∀ j : ι,
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B), c i * d i j = 0 := by
    intro j
    by_cases hb : inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx
        (Quotient.mk (blockSetoid π hπ hlin) j) = B
    · -- the complementary sum vanishes by (5.8), so the restricted sum is the whole sum
      have hcompl : ∑ i ∈ Finset.univ.filter (fun i => ¬ blockOfIrr e hπG hlinG hnilG i = B),
          c i * d i j = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [hsecond i j (by rw [hb]; exact fun h => (Finset.mem_filter.mp hi).2 h.symm), mul_zero]
      have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι')
        (fun i => blockOfIrr e hπG hlinG hnilG i = B) (fun i => c i * d i j)
      rw [hcompl, add_zero] at hsplit
      rw [hsplit, hzero j]
    · exact Finset.sum_eq_zero fun i hi => by
        rw [hsecond i j (by rw [(Finset.mem_filter.mp hi).2]; exact hb), mul_zero]
  -- assemble
  rw [forall_pSection_iff hp hx _
    fun _ _ hgh => blockPart_eq_of_isConj e hπG hlinG hnilG B θ hθ hgh]
  intro y hy
  change ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
      c i * (wedderburnRepresentation e i).character (x * (y : G)) = 0
  rw [Finset.sum_congr rfl fun i _ => by
      rw [← sum_generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
          (wedderburnRepresentation e i).character
          (fun _ _ hgh => character_eq_of_isConj (wedderburnRepresentation e i) hgh) hy,
        Finset.mul_sum],
    Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.sum_congr rfl fun i _ => (mul_assoc (c i) (d i j) _).symm, ← Finset.sum_mul,
    hfilter j, zero_mul]

set_option maxHeartbeats 1600000 in
-- Same instance chains as (5.10).
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **Navarro (5.11), block orthogonality.**  If the `p`-parts of `g` and `h` are not conjugate,
then the block-`B` part of the second orthogonality relation vanishes on its own:

`∑_{χ ∈ Irr(B)} χ(h⁻¹) χ(g) = 0`.

Apply (5.10) to `θ = ∑_{χ ∈ Irr(G)} χ(h⁻¹) χ`: by the second orthogonality relation `θ` is
supported on the class of `h`, which misses the `p`-section of `g_p`. -/
theorem sum_character_blockOfIrr_eq_zero (hp : p.Prime) {g h : G}
    (hgh : ¬ IsConj (pPart p g) (pPart p h)) [Fintype ↥(centralizerOf (pPart p g))]
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    (eH : MonoidAlgebra K ↥(centralizerOf (pPart p g)) ≃ₐ[K] ∀ i, Matrix (mH i) (mH i) K)
    {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
    (hπG : Function.Surjective πG)
    (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p g)) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪)
      (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p g))), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π
      = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p g))))
    (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p g))),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf (pPart p g))))
    {ω' : ResidueField 𝒪}
    (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf (pPart p g))))
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    (B : Block πG hπG hlinG) :
    ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character h⁻¹
          * (wedderburnRepresentation e i).character g = 0 := by
  classical
  set θ : G → K := fun u => ∑ i, (wedderburnRepresentation e i).character h⁻¹
    * (wedderburnRepresentation e i).character u with hθdef
  have hθ : ∀ a b : G, IsConj a b → θ a = θ b := fun a b hab =>
    Finset.sum_congr rfl fun i _ =>
      congrArg ((wedderburnRepresentation e i).character h⁻¹ * ·)
        (character_eq_of_isConj (wedderburnRepresentation e i) hab)
  -- `θ` is supported on the class of `h`, which misses `S(g_p)`
  have hvanish : ∀ u ∈ pSection p (pPart p g), θ u = 0 := by
    intro u hu
    simp only [hθdef]
    rw [sum_character_inv_mul_character e h u, if_neg]
    intro hconj
    exact hgh
      (((isConj_pPart hconj).trans (mem_pSection_iff_isConj_pPart.mp hu)).symm)
  -- the coefficients of `θ` are the values `χ(h⁻¹)`
  have hcoeff : ordinaryCoeff e θ hθ = fun i => (wedderburnRepresentation e i).character h⁻¹ :=
    (eq_ordinaryCoeff e θ hθ fun _ => rfl).symm
  have hzero : ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
      ordinaryCoeff e θ hθ i * (wedderburnRepresentation e i).character g = 0 :=
    blockPart_eq_zero_of_forall_pSection hp (isPElement_pPart hp g) e eH hπG hlinG hnilG hπ hlin
      hkerJ hnilH hω hω' hζ hζk hζK θ hθ hvanish B g
      (mem_pSection_iff_isConj_pPart.mpr (IsConj.refl _))
  rw [hcoeff] at hzero
  exact hzero

-- The centraliser data of `x` is consumed by (5.11) in the proof, not by this statement.
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **(5.11) against a nontrivial `p`-element, for a `p`-regular `g`** — the shape Külshammer's
formula carries as `hweak`.

The non-conjugacy hypothesis of `sum_character_blockOfIrr_eq_zero` becomes `x ≠ 1` here: `x` is a
`p`-element so `pPart p x = x`, and `g` is `p`-regular so `pPart p g = 1`, leaving
`¬ IsConj x 1`.

⚠ `p`-regularity of `g` is not a convenience — it is what makes the hypothesis discharge at all.
For a `p`-singular `g` the `p`-part is conjugate into any Sylow `p`-subgroup, so the sum genuinely
fails to vanish at that `x`; the `p`-singular case of Külshammer's route goes through Osima's
theorem instead (`OsimaBlockSupport`). -/
theorem sum_character_blockOfIrr_eq_zero_of_isPRegular (hp : p.Prime) {g x : G}
    (hg : IsPRegular p g) (hx : IsPElement p x) (hx1 : x ≠ 1)
    [Fintype ↥(centralizerOf (pPart p x))]
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    (eH : MonoidAlgebra K ↥(centralizerOf (pPart p x)) ≃ₐ[K] ∀ i, Matrix (mH i) (mH i) K)
    {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
    (hπG : Function.Surjective πG)
    (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p x)) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪)
      (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p x))), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π
      = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p x))))
    (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pPart p x))),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf (pPart p x))))
    {ω' : ResidueField 𝒪}
    (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf (pPart p x))))
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    (B : Block πG hπG hlinG) :
    ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character g⁻¹
          * (wedderburnRepresentation e i).character x = 0 :=
  sum_character_blockOfIrr_eq_zero hp
    (by
      rw [pPart_eq_self_of_isPElement hp hx, pPart_eq_one_of_isPRegular hp hg]
      exact fun hc => hx1 (isConj_one_left.mp hc))
    e eH hπG hlinG hnilG hπ hlin hkerJ hnilH hω hω' hζ hζk hζK B

end OddOrder.RepresentationTheory.Modular
