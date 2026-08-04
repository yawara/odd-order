/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.OpResidual
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockPartVanishing

/-!
# Navarro (6.9)/(6.10): the kernel of a block

`Irr(B)` is cut out by `blockOfIrr` (see `BlockOfIrreducible`), so Navarro's

`ker(B) = ⋂_{χ ∈ Irr(B)} ker(χ)`   (6.9)

is definable: `blockKernel`.  Since the ordinary irreducibles here are the Wedderburn components
of `K[G]`, "`ker χ`" is literally the kernel of the representation, and the elementary character
theory that Navarro invokes ("`ker(B)` is the kernel of `Ξ = ∑_{χ ∈ Irr(B)} χ(1) χ`") is not
needed as a separate step — it is built into the definition.

What *is* needed is the **first half of (6.10)**: `ker(B)` consists of `p`-regular elements.
Navarro's argument is that `Ξ` vanishes on `p`-singular elements by weak block orthogonality,
while `Ξ(g) = Ξ(1) = ∑_{χ ∈ Irr(B)} χ(1)^2 ≠ 0` for `g ∈ ker(B)`.  Both halves survive verbatim:
the vanishing is `sum_character_blockOfIrr_eq_zero` (= (5.11)) at `h = 1`, and the nonvanishing is
`CharZero K` plus the fact that the Wedderburn blocks are nonempty.

Weak block orthogonality is taken as a hypothesis `hweak` on the element `g` at hand rather than
baked into the statement, because (5.11) carries the ordinary and modular splittings of
`C_G(g_p)` — data that varies with `g`.  `sum_character_one_mul_character_eq_zero` at the end of
the file discharges it from (5.11) for a single `g`.

The consequence is the inclusion half of (6.10): `ker(B)` is a **normal `p'`-subgroup** of `G`,
hence `ker(B) ≤ O_{p'}(G)`, and (for `χ ∈ Irr(B)`) `ker(B) ≤ O_{p'}(ker χ)`.  The reverse
inclusion `O_{p'}(ker χ) ≤ ker(B)` is Navarro's central-character argument and needs Clifford's
theorem; it is not formalised here.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.blockKernel` — `ker(B)`, Navarro (6.9)

## Main results

* `OddOrder.RepresentationTheory.Modular.isPRegular_of_mem_blockKernel` — the elementary half of
  Navarro (6.10): `ker(B)` consists of `p`-regular elements
* `OddOrder.RepresentationTheory.Modular.not_dvd_card_blockKernel` — hence `p ∤ |ker(B)|`
* `OddOrder.RepresentationTheory.Modular.blockKernel_le_opPi` — hence `ker(B) ≤ O_{p'}(G)`
* `OddOrder.RepresentationTheory.Modular.sum_character_one_mul_character_eq_zero` — weak block
  orthogonality, i.e. (5.11) at `h = 1`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

/-! ### The kernel of a block -/

section Def

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

/-- **Navarro (6.9), the kernel of a block**: `ker(B) = ⋂_{χ ∈ Irr(B)} ker(χ)`, where `Irr(B)` is
the fibre of `blockOfIrr` over `B`. -/
noncomputable def blockKernel (B : Block πG hπG hlinG) : Subgroup G :=
  ⨅ i : {i : ι' // blockOfIrr e hπG hlinG hnilG i = B},
    MonoidHom.ker (wedderburnRepresentation e (i : ι'))

theorem mem_blockKernel_iff {B : Block πG hπG hlinG} {g : G} :
    g ∈ blockKernel e hπG hlinG hnilG B ↔
      ∀ i, blockOfIrr e hπG hlinG hnilG i = B → wedderburnRepresentation e i g = 1 := by
  simp [blockKernel, Subgroup.mem_iInf, MonoidHom.mem_ker, Subtype.forall]

/-- Each ordinary irreducible in `B` is trivial on `ker(B)`. -/
theorem blockKernel_le_ker {B : Block πG hπG hlinG} {i : ι'}
    (hi : blockOfIrr e hπG hlinG hnilG i = B) :
    blockKernel e hπG hlinG hnilG B ≤ MonoidHom.ker (wedderburnRepresentation e i) :=
  fun _ hg => MonoidHom.mem_ker.mpr ((mem_blockKernel_iff e hπG hlinG hnilG).mp hg i hi)

/-- `ker(B)` is normal: it is an intersection of kernels. -/
theorem blockKernel_normal (B : Block πG hπG hlinG) :
    (blockKernel e hπG hlinG hnilG B).Normal :=
  Subgroup.normal_iInf_normal fun _ => MonoidHom.normal_ker _

end Def

/-! ### Navarro (6.10): the kernel of a block is a `p'`-group -/

section PRegular

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

open scoped Classical in
/-- **Navarro (6.10), the elementary half**: every element of `ker(B)` is `p`-regular.

`Ξ = ∑_{χ ∈ Irr(B)} χ(1) χ` takes the value `∑_{χ ∈ Irr(B)} χ(1)^2` on `ker(B)`, which is a
nonzero natural number in the characteristic-zero field `K` as soon as `Irr(B) ≠ ∅`.  Weak block
orthogonality (`hweak`, supplied by (5.11)) says it is `0` on `p`-singular elements. -/
theorem isPRegular_of_mem_blockKernel {B : Block πG hπG hlinG}
    {i₀ : ι'} (hi₀ : blockOfIrr e hπG hlinG hnilG i₀ = B) {g : G}
    (hg : g ∈ blockKernel e hπG hlinG hnilG B)
    (hweak : ¬ IsPRegular p g →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character g = 0) :
    IsPRegular p g := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  by_contra hreg
  -- on `Irr(B)` both character values are the degree `χ(1) = |m i|`
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
      (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character g
        = ((Fintype.card (m i) * Fintype.card (m i) : ℕ) : K) := by
    intro i hi
    have hiB : blockOfIrr e hπG hlinG hnilG i = B := (Finset.mem_filter.mp hi).2
    have hker : wedderburnRepresentation e i g = 1 :=
      (mem_blockKernel_iff e hπG hlinG hnilG).mp hg i hiB
    have hone : (wedderburnRepresentation e i).character 1 = ((Fintype.card (m i) : ℕ) : K) := by
      rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
    have hgv : (wedderburnRepresentation e i).character g = ((Fintype.card (m i) : ℕ) : K) := by
      simp only [Representation.character, hker, LinearMap.trace_one,
        Module.finrank_fintype_fun_eq_card]
    rw [hone, hgv, Nat.cast_mul]
  have h0 := hweak hreg
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum] at h0
  have hnat : ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
      Fintype.card (m i) * Fintype.card (m i) = 0 := by exact_mod_cast h0
  have hmem : i₀ ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩
  have hzero := (Finset.sum_eq_zero_iff.mp hnat) i₀ hmem
  exact absurd ((Nat.mul_eq_zero.mp hzero).elim id id) Fintype.card_ne_zero

open scoped Classical in
/-- **Navarro (6.10)**: `p ∤ |ker(B)|`.  By Cauchy's theorem a prime dividing `|ker(B)|` would
give an element of that order, contradicting `p`-regularity. -/
theorem not_dvd_card_blockKernel (hp : p.Prime) {B : Block πG hπG hlinG}
    {i₀ : ι'} (hi₀ : blockOfIrr e hπG hlinG hnilG i₀ = B)
    (hweak : ∀ g ∈ blockKernel e hπG hlinG hnilG B, ¬ IsPRegular p g →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character g = 0) :
    ¬ p ∣ Nat.card ↥(blockKernel e hπG hlinG hnilG B) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(blockKernel e hπG hlinG hnilG B)) p hdvd
  have hreg : IsPRegular p ((x : G)) :=
    isPRegular_of_mem_blockKernel e hπG hlinG hnilG hi₀ x.2 (hweak _ x.2)
  exact hreg (by rw [Subgroup.orderOf_coe, hx])

open scoped Classical in
/-- **Navarro (6.10)**: `ker(B)` is a `p'`-subgroup. -/
theorem isPiSubgroup_blockKernel (hp : p.Prime) {B : Block πG hπG hlinG}
    {i₀ : ι'} (hi₀ : blockOfIrr e hπG hlinG hnilG i₀ = B)
    (hweak : ∀ g ∈ blockKernel e hπG hlinG hnilG B, ¬ IsPRegular p g →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character g = 0) :
    (blockKernel e hπG hlinG hnilG B).IsPiSubgroup {q | q ≠ p} := by
  intro q hq
  rintro (rfl : q = p)
  exact not_dvd_card_blockKernel e hπG hlinG hnilG hp hi₀ hweak (Nat.mem_primeFactors.mp hq).2.1

open scoped Classical in
/-- **Navarro (6.10), the inclusion half**: `ker(B) ≤ O_{p'}(G)`.  Being a normal `p'`-subgroup,
`ker(B)` sits inside the `p'`-radical; for `χ ∈ Irr(B)` it is moreover inside `ker χ`, so the
same argument places it inside `O_{p'}(ker χ)`.  The reverse inclusion is Navarro's
central-character argument and is not formalised here. -/
theorem blockKernel_le_opPi (hp : p.Prime) {B : Block πG hπG hlinG}
    {i₀ : ι'} (hi₀ : blockOfIrr e hπG hlinG hnilG i₀ = B)
    (hweak : ∀ g ∈ blockKernel e hπG hlinG hnilG B, ¬ IsPRegular p g →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character g = 0) :
    blockKernel e hπG hlinG hnilG B ≤ Subgroup.opPi G {q | q ≠ p} := by
  haveI := blockKernel_normal e hπG hlinG hnilG B
  exact Subgroup.self_le_opPi _ (isPiSubgroup_blockKernel e hπG hlinG hnilG hp hi₀ hweak)

end PRegular

/-! ### Weak block orthogonality, i.e. (5.11) at `h = 1` -/

section WeakOrthogonality

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ιH : Type*} {mH : ιH → Type*} [∀ i, Fintype (mH i)] [∀ i, DecidableEq (mH i)]
  [Finite ιH] [∀ i, Nonempty (mH i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]

set_option maxHeartbeats 1600000 in
-- Same instance chains as (5.11): two ordinary splittings plus two modular ones.
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **Weak block orthogonality**: `∑_{χ ∈ Irr(B)} χ(1) χ(g) = 0` for `p`-singular `g`.

This is Navarro (5.11) (`sum_character_blockOfIrr_eq_zero`) at `h = 1`: the `p`-part of `1` is
`1`, and `g` is `p`-singular exactly when its `p`-part is not `1`. -/
theorem sum_character_one_mul_character_eq_zero (hp : p.Prime) {g : G} (hg : ¬ IsPRegular p g)
    [Fintype ↥(centralizerOf (pPart p g))]
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
        (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character g = 0 := by
  classical
  have hconj : ¬ IsConj (pPart p g) (pPart p (1 : G)) := by
    rw [pPart_eq_one_of_isPRegular hp (isPRegular_one hp), isConj_one_left]
    exact fun h1 => hg (isPRegular_of_pPart_eq_one hp (isOfFinOrder_of_finite g) h1)
  have h := sum_character_blockOfIrr_eq_zero (𝒪 := 𝒪) (mH := mH) (nn := nn) hp hconj e eH hπG
    hlinG hnilG hπ hlin hkerJ hnilH hω hω' hζ hζk hζK B
  simpa using h

end WeakOrthogonality

end OddOrder.RepresentationTheory.Modular
