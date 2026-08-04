/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SubgroupSum
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
hence `ker(B) ≤ O_{p'}(G)`, and (for `χ ∈ Irr(B)`) `ker(B) ≤ O_{p'}(ker χ)`.

The reverse inclusion is `le_blockKernel_of_normal_of_forall_eq_one`.  Navarro gets it from
Clifford's theorem via the inner products `[ψ_N, 1_N]`; the argument here instead runs the central
element `N̂ = ∑_{n ∈ N} n` through the central characters, where being in the same block forces the
scalars `ω_i(N̂)` to have a common — and, since `p ∤ |N|`, nonzero — reduction.  Together the two
halves say `ker(B)` is the **largest normal `p'`-subgroup of `G` inside `ker χ`**
(`isGreatest_blockKernel`), which is what `O_{p'}(ker χ)` means.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.blockKernel` — `ker(B)`, Navarro (6.9)

## Main results

* `OddOrder.RepresentationTheory.Modular.isPRegular_of_mem_blockKernel` — the elementary half of
  Navarro (6.10): `ker(B)` consists of `p`-regular elements
* `OddOrder.RepresentationTheory.Modular.not_dvd_card_blockKernel` — hence `p ∤ |ker(B)|`
* `OddOrder.RepresentationTheory.Modular.blockKernel_le_opPi` — hence `ker(B) ≤ O_{p'}(G)`
* `OddOrder.RepresentationTheory.Modular.le_blockKernel_of_normal_of_forall_eq_one` — the reverse
  inclusion of Navarro (6.10)
* `OddOrder.RepresentationTheory.Modular.isGreatest_blockKernel` — Navarro (6.10) in full:
  `ker(B) = O_{p'}(ker χ)`
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

/-! ### Navarro (6.10), the reverse inclusion -/

section Converse

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

set_option maxHeartbeats 1000000 in
-- The two central characters and the lattice/ambient bridge carry long instance chains.
/-- **Navarro (6.10), the reverse inclusion**: a normal `p'`-subgroup `N` lying in the kernel of
*one* `χ ∈ Irr(B)` lies in the kernel of *all* of them, i.e. `N ≤ ker(B)`.

Navarro deduces this from Clifford's theorem via the inner products `[ψ_N, 1_N]`.  It is shorter
to argue with the central element `N̂ = ∑_{n ∈ N} n` directly:

* `N̂` is central (`N ⊴ G`), so it acts on each absolutely irreducible `𝒪`-lattice by a scalar
  `ω_i(N̂) ∈ 𝒪`;
* `χ_i` and `χ_{i₀}` lie in the same block, so those scalars have the **same reduction**
  `λ_B(N̂*)`;
* on `χ_{i₀}` the scalar is `|N|`, which is a unit mod `𝔪` because `p ∤ |N|`;
* hence `ω_i(N̂)` is a unit of the local ring `𝒪`, and the absorption `n · N̂ = N̂` cancels it:
  `ρ_i(n) = 1`.

No Clifford theory, no inner products, and `|N|` never has to be inverted in `𝒪`. -/
theorem le_blockKernel_of_normal_of_forall_eq_one {B : Block πG hπG hlinG} {i₀ : ι'}
    (hi₀ : blockOfIrr e hπG hlinG hnilG i₀ = B)
    {N : Subgroup G} (hN : N.Normal) (hNp : ¬ p ∣ Nat.card ↥N)
    (hker : ∀ n ∈ N, wedderburnRepresentation e i₀ n = 1) :
    N ≤ blockKernel e hπG hlinG hnilG B := by
  classical
  -- `N̂` as a central element of `𝒪G`, and its reduction in `Z(kG)`
  set zN : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G) :=
    ⟨GroupAlgebra.subgroupSum 𝒪 N, GroupAlgebra.subgroupSum_mem_center hN⟩ with hzNdef
  set zN' : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G) :=
    ⟨GroupAlgebra.subgroupSum (ResidueField 𝒪) N, GroupAlgebra.subgroupSum_mem_center hN⟩
    with hzN'def
  have hmap : MonoidAlgebra.mapRingHom G (residue 𝒪) (zN : MonoidAlgebra 𝒪 G)
      = (zN' : MonoidAlgebra (ResidueField 𝒪) G) :=
    GroupAlgebra.mapRingHom_subgroupSum _ N
  -- the scalar by which `N̂` acts on the `i`-th ordinary irreducible
  set c : ι' → 𝒪 := fun i => centralScalar K
    ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
    (exists_smul_id_of_commute_wedderburnLattice e i) zN with hcdef
  -- block membership pins the reduction of that scalar
  have hres : ∀ i, blockOfIrr e hπG hlinG hnilG i = B →
      residue 𝒪 (c i) = MatrixModule.blockCharacter πG hπG hlinG B zN' := by
    intro i hi
    rw [← hi]
    exact (blockCharacter_blockOfLattice_mapRingHom K _
      (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
      zN hmap).symm
  -- on `χ_{i₀}` the scalar is `|N|`
  have hone : ∀ n ∈ N, ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i₀).asAlgebraHom)
      (MonoidAlgebra.single n (1 : 𝒪)) = 1 := by
    intro n hn
    rw [Representation.asAlgebraHom_single_one]
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hcoe : (((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i₀) n v : _) : m i₀ → K)
        = wedderburnRepresentation e i₀ n (v : m i₀ → K) :=
      coe_latticeRepresentation_apply _ (invariant_wedderburnLattice e i₀) n v
    rw [hcoe, hker n hn]
    rfl
  have hact : ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i₀).asAlgebraHom)
      (GroupAlgebra.subgroupSum 𝒪 N)
      = (Nat.card ↥N : ℕ) • (1 : Module.End 𝒪 ↥(wedderburnLattice (𝒪 := 𝒪) e i₀)) :=
    GroupAlgebra.map_subgroupSum_of_forall_map_single_eq_one _ hone
  have hc0 : c i₀ = ((Nat.card ↥N : ℕ) : 𝒪) := by
    refine (eq_centralScalar K _ (exists_smul_id_of_commute_wedderburnLattice e i₀) ?_).symm
    rw [show ((zN : MonoidAlgebra 𝒪 G)) = GroupAlgebra.subgroupSum 𝒪 N from rfl, hact,
      Module.End.one_eq_id, Nat.cast_smul_eq_nsmul]
  -- `|N|` is invertible in the residue field
  have hcard : ((Nat.card ↥N : ℕ) : ResidueField 𝒪) ≠ 0 := fun h =>
    hNp ((CharP.cast_eq_zero_iff (ResidueField 𝒪) p _).mp h)
  have hres0 : residue 𝒪 (c i₀) ≠ 0 := by rw [hc0, map_natCast]; exact hcard
  -- conclude, block member by block member
  intro n hn
  rw [mem_blockKernel_iff]
  intro i hi
  have hci : residue 𝒪 (c i) ≠ 0 := by rw [hres i hi, ← hres i₀ hi₀]; exact hres0
  have hunit : IsUnit (c i) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact fun hmem => hci (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hψ : ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (GroupAlgebra.subgroupSum 𝒪 N) = c i • LinearMap.id :=
    apply_center_eq_centralScalar_smul K _
      (exists_smul_id_of_commute_wedderburnLattice e i) zN
  have hψunit : IsUnit (((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (GroupAlgebra.subgroupSum 𝒪 N)) := by
    rw [hψ, ← Module.algebraMap_end_eq_smul_id]
    exact hunit.map _
  have hkill : ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (MonoidAlgebra.single n (1 : 𝒪)) = 1 :=
    GroupAlgebra.map_single_eq_one_of_isUnit_map_subgroupSum _ hψunit hn
  -- push the vanishing of `single n 1 - 1` from the lattice up to the ambient space
  have hzero : ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (MonoidAlgebra.single n (1 : 𝒪) - 1) = 0 := by rw [map_sub, hkill, map_one, sub_self]
  have hamb := asAlgebraHom_eq_zero_of_latticeRepresentation (wedderburnRepresentation e i)
    (invariant_wedderburnLattice e i) hzero
  rw [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one, map_sub, map_one,
    Representation.asAlgebraHom_single_one, sub_eq_zero] at hamb
  exact hamb

open scoped Classical in
/-- **Navarro (6.10)**, in full: for `χ ∈ Irr(B)`, `ker(B)` is the *largest* normal `p'`-subgroup
of `G` contained in `ker χ` — which is exactly what `O_{p'}(ker χ)` denotes.

(`O_{p'}(ker χ)` is characteristic in `ker χ ⊴ G`, hence normal in `G`; conversely a `G`-normal
`p'`-subgroup of `ker χ` is normal in `ker χ`.  So the greatest element of the set below and
`O_{p'}(ker χ)` are the same subgroup, and phrasing it this way avoids transporting subgroups of
`ker χ` back into `G`.) -/
theorem isGreatest_blockKernel [Fintype ι'] (hp : p.Prime) {B : Block πG hπG hlinG} {i₀ : ι'}
    (hi₀ : blockOfIrr e hπG hlinG hnilG i₀ = B)
    (hweak : ∀ g ∈ blockKernel e hπG hlinG hnilG B, ¬ IsPRegular p g →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character g = 0) :
    IsGreatest {N : Subgroup G | N.Normal ∧ ¬ p ∣ Nat.card ↥N ∧
        N ≤ MonoidHom.ker (wedderburnRepresentation e i₀)}
      (blockKernel e hπG hlinG hnilG B) := by
  refine ⟨⟨blockKernel_normal e hπG hlinG hnilG B,
    not_dvd_card_blockKernel e hπG hlinG hnilG hp hi₀ hweak,
    blockKernel_le_ker e hπG hlinG hnilG hi₀⟩, ?_⟩
  rintro N ⟨hN, hNp, hNker⟩
  exact le_blockKernel_of_normal_of_forall_eq_one e hπG hlinG hnilG hi₀ hN hNp
    fun n hn => MonoidHom.mem_ker.mp (hNker hn)

end Converse

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
