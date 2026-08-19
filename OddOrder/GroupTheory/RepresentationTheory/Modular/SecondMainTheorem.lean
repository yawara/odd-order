/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlockTrace
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.Modular.PSection
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainCore
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainWiring

/-!
# Brauer's second main theorem — Navarro (5.2)

Let `x` be a `p`-element of `G`, `H = C_G(x)`, `b` a block of `H` with `b^G = B`, and
`χ ∈ Irr(G)` outside `B`.  Then the generalized decomposition numbers `d^x_{χφ}` vanish for every
`φ ∈ IBr(b)`.

`SecondMainCore.blockCoeff_eq_zero_of_vanishing` carries the computation; this file supplies its
six hypotheses from the actual `p`-modular system and identifies the resulting coefficients with
the generalized decomposition numbers of (5.1):

| hypothesis | source |
| --- | --- |
| `hd` — the ordinary decomposition of `χ_H` | `exists_ordinary_decomposition` |
| `hD` — the decomposition matrix of `H` | `trace_wedderburn_eq_sum_decompositionMatrix` |
| `hindep` — independence of `IBr(H)` | `eq_zero_of_sum_algebraMap_irreducibleBrauerCharacter` |
| `hvanish` — `χ(f_b x y) = 0` | (5.7), `trace_blockIdempotent_mul_eq_zero` |
| `hblock` — block diagonality of `D`
  | `centralCharacterAlg_eq_one_of_decompositionMatrix_ne_zero` |
| `hfidem` — `ω^K_i(f_b) ∈ {0,1}` | `centralCharacterAlg_eq_zero_or_one_of_isIdempotentElem` |

The only genuinely new work here is the passage between the three group algebras `𝒪G`, `K[H]` and
`𝒪H` (`SecondMainBridge`), and the identification `(xy)_p = x`, which is what lets (5.7) apply at
the element `xy`.

⚠ The `p`-element hypothesis on `x` is used exactly once, for `(xy)_p = x`; and no absolute
irreducibility of `χ` is needed anywhere.

## Main results

* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumber_eq_zero` — Navarro (5.2)
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory
open OddOrder.GroupAlgebra (inclusionHom)

/-! ### The second main theorem -/

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Finite ι'] [∀ i, Nonempty (m i)]

set_option maxHeartbeats 1000000 in
-- The statement carries the two splittings, the three incarnations of the block idempotent and
-- the witness of (5.6); unifying those instance chains is what costs the heartbeats.
/-- **Brauer's second main theorem, Navarro (5.2).**  Let `x` be a `p`-element, `H = C_G(x)`, and
let `f_b` be the block idempotent of a block `b` of `H`.  Suppose a central idempotent `f_B` of
`𝒪G` annihilates the module `V` affording `χ` — this is (3.13.a) for `χ ∉ B` — and that `w` is a
witness of (5.6) for the pair `(f_b, f_B)`, so that `b^G = B`.  Then the generalized decomposition
number `d^x_{χφ}` vanishes for every `φ ∈ IBr(b)`.

Membership `φ_j ∈ IBr(b)` is expressed as `ω^k_j(f̄_b) = 1`, the central character of the `j`-th
simple `kH`-module taking the value `1` on the reduction of the block idempotent. -/
theorem generalizedDecompositionNumber_eq_zero (hp : p.Prime) {x : G} (hx : IsPElement p x)
    -- the ordinary splitting of `K[C_G(x)]` and the modular splitting of `k[C_G(x)]`
    (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
    -- a non-trivial `p`-th root of unity, as in (5.7)
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    -- the representation affording `χ`
    (σ : Representation K G V)
    -- the block idempotent `f_b` of `b`, in its three incarnations
    {f𝒪 : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥(centralizerOf x))}
    {fK : Subalgebra.center K (MonoidAlgebra K ↥(centralizerOf x))}
    {fk : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪)
      ↥(centralizerOf x))}
    (hfidem : IsIdempotentElem f𝒪)
    (hfK : MonoidAlgebra.mapRingHom _ (algebraMap 𝒪 K)
        (f𝒪 : MonoidAlgebra 𝒪 ↥(centralizerOf x)) = (fK : MonoidAlgebra K ↥(centralizerOf x)))
    (hfk : MonoidAlgebra.mapRingHom _ (residue 𝒪) (f𝒪 : MonoidAlgebra 𝒪 ↥(centralizerOf x))
      = (fk : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
    -- the block idempotent `f_B` of `B`, annihilating `V`: this is `χ ∉ B`
    {fB : MonoidAlgebra 𝒪 G} (hfB : fB * fB = fB) (hfBc : ∀ a, Commute fB a)
    (hσB : σ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) fB) = 0)
    -- the witness of (5.6), which is what says `b^G = B`
    {w : MonoidAlgebra 𝒪 G}
    (hwa : (1 - fB) * inclusionHom (centralizerOf x)
        (f𝒪 : MonoidAlgebra 𝒪 ↥(centralizerOf x)) = (1 - fB) * w)
    (hwb : w * inclusionHom (centralizerOf x) (f𝒪 : MonoidAlgebra 𝒪 ↥(centralizerOf x)) = w)
    (hwc : ∀ u : ↥(centralizerOf x), MonoidAlgebra.single (u : G) (1 : 𝒪) * w
      = w * MonoidAlgebra.single (u : G) 1)
    (hwd : ∀ g ∈ centralizerOf x, w.coeff g = 0)
    -- `φ_j ∈ IBr(b)`
    {j : ι} (hj : MatrixModule.centralCharacterAlg π j hπ hlin fk = 1) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        (fun g => LinearMap.trace K V (σ g))
        (fun _ _ hgh => character_eq_of_isConj σ hgh) j = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥(centralizerOf x) := Fintype.ofFinite _
  have : Fintype ι' := Fintype.ofFinite ι'
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have : NeZero (Nat.card ↥(centralizerOf x) : K) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- `x` lies in `H = C_G(x)` and is central there
  have hxmem : x ∈ centralizerOf x := Subgroup.mem_centralizer_iff.mpr (by rintro y rfl; rfl)
  set xH : ↥(centralizerOf x) := ⟨x, hxmem⟩ with hxHdef
  have hxcentral : ∀ u : ↥(centralizerOf x), xH * u = u * xH := fun u =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp u.2) x rfl)
  -- the data of the core computation
  set ρ : Representation K ↥(centralizerOf x) V := σ.comp (centralizerOf x).subtype with hρdef
  set πK := e.toAlgHom.toRingHom with hπKdef
  have hπK : Function.Surjective πK := surjective_algEquiv e
  have hlinK : ∀ (c : K) (a : MonoidAlgebra K ↥(centralizerOf x)), πK (c • a) = c • πK a :=
    smul_algEquiv e
  have hkerJK : RingHom.ker πK = Ring.jacobson (MonoidAlgebra K ↥(centralizerOf x)) :=
    ker_algEquiv_eq_jacobson e
  obtain ⟨d, hd, -⟩ := exists_ordinary_decomposition (nn := m) hπK hlinK hkerJK ρ
  set D := decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e with hDdef
  set φ : ι → ↥(centralizerOf x) → K := fun j y =>
    algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π j y) with hφdef
  -- `w = single x 1`, central in `K[H]` because `x ∈ Z(H)`
  set wcen : Subalgebra.center K (MonoidAlgebra K ↥(centralizerOf x)) :=
    ⟨MonoidAlgebra.single xH 1,
      OddOrder.GroupAlgebra.single_mem_center_of_forall_commute hxcentral 1⟩
    with hwcendef
  -- the trace of `ρ` at a monomial of `K[H]`
  have hρsingle : ∀ u : ↥(centralizerOf x),
      ρ.asAlgebraHom (MonoidAlgebra.single u (1 : K)) = σ (u : G) := by
    intro u
    rw [Representation.asAlgebraHom_single_one]
    rfl
  -- `hD`: the decomposition matrix, read in `K`
  have hDprop : ∀ y : ↥(centralizerOf x), IsPRegular p y → ∀ i : ι',
      LinearMap.trace K (m i → K) (blockRepresentation πK i y) = ∑ j, (D i j : K) * φ j y := by
    intro y hy i
    rw [hπKdef, blockRepresentation_algEquiv e i]
    exact trace_wedderburn_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i y hy
  -- `hindep`: the irreducible Brauer characters of `H` are independent over `K`
  have hindep : ∀ c : ι → K,
      (∀ y : ↥(centralizerOf x), IsPRegular p y → ∑ j, c j * φ j y = 0) → c = 0 := fun c hc =>
    eq_zero_of_sum_algebraMap_irreducibleBrauerCharacter (K := K) hp hω' hπ hlin hkerJ c hc
  -- `hfidem`: `ω^K_i(f_b)` is an idempotent of `K`
  have hfKidem : IsIdempotentElem fK := by
    refine Subtype.ext ?_
    have := congrArg (MonoidAlgebra.mapRingHom (↥(centralizerOf x)) (algebraMap 𝒪 K))
      (congrArg Subtype.val hfidem)
    rwa [Subalgebra.coe_mul, map_mul, hfK] at this
  -- `hvanish`: Navarro (5.7)
  set ρ𝒪 : MonoidAlgebra 𝒪 G →+* Module.End K V :=
    (σ.asAlgebraHom.toRingHom).comp (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K)) with hρ𝒪def
  have hρ𝒪smul : ∀ (r : 𝒪) (a : MonoidAlgebra 𝒪 G),
      ρ𝒪 (r • a) = algebraMap 𝒪 K r • ρ𝒪 a := fun r a => by
    rw [hρ𝒪def]
    change σ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (r • a))
      = algebraMap 𝒪 K r • σ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) a)
    rw [OddOrder.GroupTheory.CenterClassSum.mapRingHom_smul, map_smul]
  have hvanish : ∀ y : ↥(centralizerOf x), IsPRegular p y → LinearMap.trace K V
      (ρ.asAlgebraHom ((fK : MonoidAlgebra K ↥(centralizerOf x))
        * ((wcen : MonoidAlgebra K ↥(centralizerOf x))
          * MonoidAlgebra.single y 1))) = 0 := by
    intro y hy
    -- rewrite the argument as `f_b · (x y)` and pass to `𝒪G`
    have harg : (fK : MonoidAlgebra K ↥(centralizerOf x))
        * ((wcen : MonoidAlgebra K ↥(centralizerOf x)) * MonoidAlgebra.single y 1)
        = (fK : MonoidAlgebra K ↥(centralizerOf x))
          * MonoidAlgebra.single (xH * y) 1 := by
      rw [hwcendef, MonoidAlgebra.single_mul_single, mul_one]
    rw [harg, map_mul, asAlgebraHom_comp_subtype, asAlgebraHom_comp_subtype]
    -- both factors come from `𝒪G`
    have hfac1 : σ.asAlgebraHom (inclusionHom (centralizerOf x)
        (fK : MonoidAlgebra K ↥(centralizerOf x)))
        = ρ𝒪 (inclusionHom (centralizerOf x)
          (f𝒪 : MonoidAlgebra 𝒪 ↥(centralizerOf x))) := by
      rw [hρ𝒪def]
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [mapRingHom_inclusionHom, hfK]
      rfl
    have hfac2 : σ.asAlgebraHom (inclusionHom (centralizerOf x)
        (MonoidAlgebra.single (xH * y) (1 : K)))
        = ρ𝒪 (MonoidAlgebra.single ((xH * y : ↥(centralizerOf x)) : G) (1 : 𝒪)) := by
      rw [hρ𝒪def]
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [MonoidAlgebra.mapRingHom_single, map_one,
        OddOrder.GroupAlgebra.inclusionHom_single]
      rfl
    rw [hfac1, hfac2]
    -- `(x y)_p = x`, so `C_G((x y)_p) = H`
    have hcomm : Commute x (y : G) := ((Subgroup.mem_centralizer_iff.mp y.2) x rfl)
    have hyG : IsPRegular p ((y : G)) := isPRegular_coe hy
    have hpPart : pPart p ((xH * y : ↥(centralizerOf x)) : G) = x := by
      rw [Subgroup.coe_mul, hxHdef]
      exact pPart_mul_eq_of_isPElement hp hcomm hx hyG
    refine trace_blockIdempotent_mul_eq_zero (K := K) hp (centralizerOf x) (residue 𝒪)
      ker_residue hζ hζk hζK ?_ ?_ hfB hfBc hwa hwb hwc hwd ?_ ρ𝒪 hρ𝒪smul ?_
    · exact congrArg Subtype.val hfidem
    · exact fun u => Subalgebra.mem_center_iff.mp f𝒪.2 (MonoidAlgebra.single u 1)
    · rw [hpPart]
    · rw [hρ𝒪def]; exact hσB
  -- `hblock`: block diagonality
  have hblock : ∀ (i : ι') (j' : ι),
      j' ∈ {j'' : ι | MatrixModule.centralCharacterAlg π j'' hπ hlin fk = 1} →
      MatrixModule.centralCharacterAlg πK i hπK hlinK fK ≠ 1 → D i j' = 0 := by
    intro i j' hj' hne
    by_contra hD0
    exact hne (centralCharacterAlg_eq_one_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ
      e i j' hfK hfk hfKidem hj' hD0)
  -- the core computation
  have hzero : blockCoeff hπK hlinK d D 1 wcen j = 0 :=
    blockCoeff_eq_zero_of_vanishing hπK hlinK hd hDprop hindep hvanish hblock
      (fun i => centralCharacterAlg_eq_zero_or_one_of_isIdempotentElem hπK hlinK i hfKidem) hj
  -- and `blockCoeff … 1 wcen` *is* the generalized decomposition
  have hgd : blockCoeff hπK hlinK d D 1 wcen
      = generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        (fun g => LinearMap.trace K V (σ g)) (fun _ _ hgh => character_eq_of_isConj σ hgh) := by
    refine eq_generalizedDecompositionNumber x hp hω' hπ hlin hkerJ _ _ fun y hy => ?_
    rw [sum_blockCoeff_eq_trace hπK hlinK hd (hDprop y hy) 1 wcen]
    congr 1
    rw [hwcendef]
    simp only [OneMemClass.coe_one, one_mul]
    rw [MonoidAlgebra.single_mul_single, mul_one, hρsingle, Subgroup.coe_mul]
  rw [← hgd]
  exact hzero

end OddOrder.RepresentationTheory.Modular
