/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import OddOrder.GroupTheory.RepresentationTheory.Modular.WittVectorSystem

/-!
# Splitting `p`-modular systems

A `p`-modular system `𝒪` (`PModularSystem.lean`) is **splitting for `n`** when its residue
field `k` contains a primitive `n`-th root of unity — in mathlib's vocabulary, when
`HasEnoughRootsOfUnity k n` holds.  This is the hypothesis that makes Brauer characters
possible: a `p`-regular element of order dividing `n` then acts on a `kG`-module with all
eigenvalues in `k`, and `RootsOfUnityLift` transports those eigenvalues to characteristic `0`.

`ℤ_[p]` is *not* splitting for any `n > 1` prime to `p` (its residue field is the prime field
`ZMod p`), so a genuine construction is needed.  This file gives one, for every prime `p` and
every `n` prime to `p`:

`SplittingSystem p n = 𝕎 (GF(p ^ φ(n)))`,

the Witt vectors over the finite field with `p ^ φ(n)` elements.  Euler's theorem
`p ^ φ(n) ≡ 1 (mod n)` puts `n` roots of unity into that field, `WittVectorSystem.lean` makes
`𝕎` of it a `p`-modular system with that residue field, and the Henselian lift
(`rootsOfUnityEquivResidue_of_not_dvd`) moves the roots of unity up into `𝒪` itself.  So the
notion is not vacuous, in the strong sense demanded by issue 9506: the carrier is *constructed*,
not posited.

## Main results

* `OddOrder.RepresentationTheory.Modular.hasEnoughRootsOfUnity_of_dvd_card_sub_one` — a finite
  field has all `n`-th roots of unity as soon as `n ∣ |F| - 1`
* `OddOrder.RepresentationTheory.Modular.hasEnoughRootsOfUnity_of_residueField` — splitting is
  inherited by `𝒪` from its residue field, for `p ∤ n`
* `OddOrder.RepresentationTheory.Modular.hasEnoughRootsOfUnity_residueField_splittingSystem`
  and `..._splittingSystem` — the construction works
* `OddOrder.RepresentationTheory.Modular.natCard_rootsOfUnity_splittingSystem` — `μ_n(𝒪)` has
  exactly `n` elements
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing

/-! ### Roots of unity in a finite field -/

/-- A finite field has all `|F| - 1` roots of unity: they are *all* the units. -/
theorem hasEnoughRootsOfUnity_card_sub_one (F : Type*) [Field F] [Fintype F] :
    HasEnoughRootsOfUnity F (Fintype.card F - 1) := by
  classical
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  haveI : NeZero (Fintype.card F - 1) := ⟨by omega⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have htop : rootsOfUnity (Fintype.card F - 1) F = ⊤ := by
    ext u
    simpa [Units.ext_iff] using FiniteField.pow_card_sub_one_eq_one (u : F) (Units.ne_zero u)
  have hnc := Nat.card_congr (MulEquiv.subgroupCongr htop).toEquiv
  rw [Nat.card_eq_fintype_card] at hnc
  rw [hnc]
  simp [Fintype.card_units]

/-- A finite field has all `n`-th roots of unity as soon as `n ∣ |F| - 1`. -/
theorem hasEnoughRootsOfUnity_of_dvd_card_sub_one (F : Type*) [Field F] [Fintype F] {n : ℕ}
    (hn : n ∣ Fintype.card F - 1) : HasEnoughRootsOfUnity F n := by
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  haveI : NeZero (Fintype.card F - 1) := ⟨by omega⟩
  haveI := hasEnoughRootsOfUnity_card_sub_one F
  exact HasEnoughRootsOfUnity.of_dvd F hn

/-- **Euler**: `n ∣ p ^ φ(n) - 1` whenever the prime `p` does not divide `n`.  This is what
selects the degree of the finite field below. -/
theorem dvd_pow_totient_sub_one {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    n ∣ p ^ n.totient - 1 :=
  (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp
    (Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)).symm

/-! ### Transporting the splitting condition -/

/-- **Roots of unity transport along any homomorphism of fields** (which is injective, so a
primitive root stays primitive; cyclicity is automatic in a field). -/
theorem hasEnoughRootsOfUnity_of_ringHom {F E : Type*} [Field F] [Field E] {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity F n] (f : F →+* E) : HasEnoughRootsOfUnity E n where
  prim := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
    exact ⟨f ζ, hζ.map_of_injective f.injective⟩
  cyc := rootsOfUnity.isCyclic E n

/-- **Splitting is inherited by `𝒪` from its residue field.**  For `p ∤ n` the reduction map is
an isomorphism `μ_n(𝒪) ≃* μ_n(k)` (`rootsOfUnityEquivResidue_of_not_dvd`), so a primitive
`n`-th root of unity downstairs comes from one upstairs.  This is what lets Brauer characters
take values in characteristic `0`. -/
theorem hasEnoughRootsOfUnity_of_residueField {p : ℕ} {𝒪 : Type*} [CommRing 𝒪]
    [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] {n : ℕ} [NeZero n] (hn : ¬ p ∣ n)
    [HasEnoughRootsOfUnity (ResidueField 𝒪) n] : HasEnoughRootsOfUnity 𝒪 n :=
  MulEquiv.hasEnoughRootsOfUnity
    (rootsOfUnityEquivResidue_of_not_dvd (p := p) (𝒪 := 𝒪) hn (NeZero.ne n)).symm

/-! ### The standard splitting system -/

variable (p n : ℕ) [Fact p.Prime]

/-- The **standard splitting `p`-modular system for `n`**: the Witt vectors over the finite
field with `p ^ φ(n)` elements.  It is a `p`-modular system by `instIsPModularSystemWittVector`,
and splitting for `n` by `hasEnoughRootsOfUnity_splittingSystem` below (when `p ∤ n`). -/
abbrev SplittingSystem : Type := WittVector p (GaloisField p n.totient)

/-- The residue field of `SplittingSystem p n` is `GF(p ^ φ(n))`. -/
noncomputable def splittingSystemResidueFieldEquiv :
    ResidueField (SplittingSystem p n) ≃+* GaloisField p n.totient :=
  wittVectorResidueFieldEquiv _

/-- `GF(p ^ φ(n))` contains all `n`-th roots of unity when `p ∤ n`. -/
theorem hasEnoughRootsOfUnity_galoisField (hp : ¬ p ∣ n) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity (GaloisField p n.totient) n := by
  haveI : Fintype (GaloisField p n.totient) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p n.totient) = p ^ n.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p _ (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  refine hasEnoughRootsOfUnity_of_dvd_card_sub_one _ ?_
  rw [hcard]
  exact dvd_pow_totient_sub_one Fact.out hp

/-- The residue field of the standard splitting system contains all `n`-th roots of unity. -/
theorem hasEnoughRootsOfUnity_residueField_splittingSystem (hp : ¬ p ∣ n) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity (ResidueField (SplittingSystem p n)) n := by
  haveI : NeZero n := ⟨hn⟩
  haveI := hasEnoughRootsOfUnity_galoisField p n hp hn
  exact hasEnoughRootsOfUnity_of_ringHom (splittingSystemResidueFieldEquiv p n).symm.toRingHom

/-- **The standard splitting system itself contains all `n`-th roots of unity** — they lift
from the residue field through the Henselian ring. -/
theorem hasEnoughRootsOfUnity_splittingSystem (hp : ¬ p ∣ n) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity (SplittingSystem p n) n := by
  haveI : NeZero n := ⟨hn⟩
  haveI := hasEnoughRootsOfUnity_residueField_splittingSystem p n hp hn
  exact hasEnoughRootsOfUnity_of_residueField (p := p) hp

/-- `μ_n` of the standard splitting system has exactly `n` elements. -/
theorem natCard_rootsOfUnity_splittingSystem (hp : ¬ p ∣ n) (hn : n ≠ 0) :
    Nat.card (rootsOfUnity n (SplittingSystem p n)) = n := by
  haveI : NeZero n := ⟨hn⟩
  haveI := hasEnoughRootsOfUnity_splittingSystem p n hp hn
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n

/-- A primitive `n`-th root of unity exists in the standard splitting system. -/
theorem exists_isPrimitiveRoot_splittingSystem (hp : ¬ p ∣ n) (hn : n ≠ 0) :
    ∃ ζ : SplittingSystem p n, IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn⟩
  haveI := hasEnoughRootsOfUnity_splittingSystem p n hp hn
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ n

/-! ### Algebraically closed residue fields

The counting side of Brauer's theorem needs the residue field to be a splitting field, and the
easiest sufficient condition is that it be algebraically closed; the Brauer characters need it to
contain the `n`-th roots of unity.  Both hold for `𝕎(𝔽̄_p)`, because an algebraically closed
field of characteristic `p` contains the finite field `GF(p ^ φ(n))`, which already has all the
`n`-th roots of unity for `p ∤ n`.
-/

/-- **An algebraically closed field of characteristic `p` has all `n`-th roots of unity** for
`p ∤ n`: they already live in the finite subfield `GF(p ^ φ(n))`. -/
theorem hasEnoughRootsOfUnity_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (hp : ¬ p ∣ n) (hn : n ≠ 0) : HasEnoughRootsOfUnity K n := by
  haveI : NeZero n := ⟨hn⟩
  haveI := hasEnoughRootsOfUnity_galoisField p n hp hn
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Algebra.IsAlgebraic (ZMod p) (GaloisField p n.totient) :=
    Algebra.IsAlgebraic.of_finite _ _
  have f : GaloisField p n.totient →ₐ[ZMod p] K := IsAlgClosed.lift
  exact hasEnoughRootsOfUnity_of_ringHom f.toRingHom

end OddOrder.RepresentationTheory.Modular
