/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Nat.GCD.Basic

/-!
# The Singer mechanism: irreducible abelian linear actions realize fields

If a finite abelian group `C` acts `𝔽_p`-linearly and *irreducibly* on a finite
`𝔽_p`-vector space `M` — formalized as: `M` is a *simple* module over the group
algebra `𝔽_p[C] = MonoidAlgebra (ZMod p) C` — then `M` carries the structure of a
finite field, with `C` acting by multiplication.

Concretely there is a maximal ideal `I ⊴ 𝔽_p[C]` with `M ≃ₗ 𝔽_p[C] ⧸ I`, and
`𝔽_p[C] ⧸ I` is a field because `𝔽_p[C]` is **commutative** (a simple module over a
commutative ring is the quotient by a maximal ideal — the abelian case avoids
Wedderburn / Jacobson density entirely).  Each group element `c` acts as the unit
`mk (of c)` of the quotient field, giving a monoid hom `C → Kˣ`.

This is the abstract core of **Peterfalvi (14.2)(a)**: the elementary abelian Fitting
subgroup `P` of a minimal simple group of odd order acquires its `GF(p^q)` field
structure from the irreducible action of its cyclic complement, the complement being
realized inside the multiplicative group `GF(p^q)ˣ`.

## Main definitions / results

* `OddOrder.RepresentationTheory.SingerFieldData` — bundles the field `K`, the additive
  isomorphism `e : M ≃+ K`, and the multiplicative realization `μ : C →* Kˣ` with the
  compatibility `e (of c • m) = μ c * e m`.
* `OddOrder.RepresentationTheory.nonempty_singerFieldData` — the existence theorem.
* `OddOrder.RepresentationTheory.SingerFieldData.card_K_eq` — `|K| = |M|`.
-/

namespace OddOrder.RepresentationTheory

universe u

variable {p : ℕ} {C M : Type u} [CommGroup C] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) C) M]

/-- Witness that an irreducible `𝔽_p`-linear action of an abelian group `C` on `M`
realizes `M` as a finite field with `C` acting by multiplication.

The field `K`, the additive isomorphism `e : M ≃+ K`, and the multiplicative
realization `μ : C →* Kˣ` package Peterfalvi (14.2)(a) in abstract form: `M` *is* the
additive group of a field, and the group action *is* multiplication. -/
structure SingerFieldData where
  /-- The field structure carried by `M`. -/
  K : Type u
  [field : Field K]
  [fintype : Fintype K]
  /-- `M` is additively the field `K`. -/
  e : M ≃+ K
  /-- `C` is realized inside `Kˣ` by the action. -/
  μ : C →* Kˣ
  /-- The action of `c` on `M` is multiplication by `μ c` in the field `K`. -/
  compat : ∀ (c : C) (m : M),
    e (MonoidAlgebra.of (ZMod p) C c • m) = (μ c : K) * e m

attribute [instance] SingerFieldData.field SingerFieldData.fintype

namespace SingerFieldData

/-- The additive isomorphism transports cardinality: `|K| = |M|`. -/
theorem card_K_eq [Fintype M] (data : SingerFieldData (p := p) (C := C) (M := M)) :
    Fintype.card data.K = Fintype.card M :=
  (Fintype.card_congr data.e.toEquiv).symm

/-- When `|M| = p ^ n` (`n ≠ 0`), the Singer field `K` is the Galois field `GF(p^n)`.
This is the form consumed by Peterfalvi's finite-field model, in which the elementary
abelian `P` (`|P| = p^q`) is identified with the additive group of `GF(p^q)`. -/
theorem nonempty_ringEquiv_galoisField [Fact p.Prime] [Fintype M] {n : ℕ} (hn : n ≠ 0)
    (data : SingerFieldData (p := p) (C := C) (M := M)) (hcard : Fintype.card M = p ^ n) :
    Nonempty (data.K ≃+* GaloisField p n) := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [data.card_K_eq, hcard, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]

end SingerFieldData

/-- **Singer mechanism (abelian case).**  If the finite abelian group `C` acts
`𝔽_p`-linearly and irreducibly (`M` is simple over `𝔽_p[C]`) on the finite module `M`,
then `M` is a field and `C` acts by multiplication: there is a `SingerFieldData`.

The construction: a simple module over the *commutative* ring `R = 𝔽_p[C]` is `R ⧸ I`
for a maximal ideal `I` (`isSimpleModule_iff_quot_maximal`), and `R ⧸ I` is a field
because `R` is commutative (`Ideal.Quotient.field`).  Under the additive identification
`M ≃+ R ⧸ I`, the action of `MonoidAlgebra.of _ _ c` is multiplication by the unit
`mk (of c)`. -/
theorem nonempty_singerFieldData [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M] :
    Nonempty (SingerFieldData (p := p) (C := C) (M := M)) := by
  classical
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) C) (M := M)).mp ‹_›
  haveI : I.IsMaximal := hImax
  letI : Field (MonoidAlgebra (ZMod p) C ⧸ I) := Ideal.Quotient.field I
  haveI : Finite (MonoidAlgebra (ZMod p) C ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  letI : Fintype (MonoidAlgebra (ZMod p) C ⧸ I) := Fintype.ofFinite _
  refine ⟨{
    K := MonoidAlgebra (ZMod p) C ⧸ I
    e := lequiv.toAddEquiv
    μ := (Units.map
            (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) C →+* _).toMonoidHom).comp
          (MonoidAlgebra.of (ZMod p) C).toHomUnits
    compat := ?_ }⟩
  intro c m
  change lequiv (MonoidAlgebra.of (ZMod p) C c • m) = _
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  rfl

/-! ## Number-theoretic core of the irreducibility criterion

The Singer construction is applied (Peterfalvi (14.2)(a)) to a cyclic group `U` of order
`u = (p^q-1)/(p-1)` acting faithfully on an elementary abelian `p`-group `P` of order `p^q`
(`q` prime).  Irreducibility of that action reduces to the fact that `u` cannot divide
`p^D - 1` for any `D` not divisible by `q`: if every Maschke constituent had dimension `dᵢ<q`,
then `u = lcm(uᵢ)` would divide `p^{lcm dᵢ}-1` with `q ∤ lcm dᵢ`, forcing the contradiction
below. -/

/-- If `q` is prime, `2 ≤ p`, and `q ∤ D`, then `(p^q-1)/(p-1)` does **not** divide `p^D - 1`.

Indeed `u := (p^q-1)/(p-1)` divides both `p^q-1` and (by hypothesis) `p^D-1`, hence divides
`gcd(p^q-1, p^D-1) = p^{gcd(q,D)}-1 = p-1` (as `gcd(q,D)=1`, `q` prime, `q∤D`).  But
`u·(p-1) = p^q-1 ≥ p^2-1 > (p-1)^2`, so `u > p-1` — a contradiction. -/
theorem cyclotomicQuotient_not_dvd_pow_sub_one {p q D : ℕ} (hp : 2 ≤ p) (hq : q.Prime)
    (hqD : ¬ q ∣ D) : ¬ ((p ^ q - 1) / (p - 1) ∣ p ^ D - 1) := by
  intro hdvd
  have hp1 : (1 : ℕ) ≤ p := by omega
  -- `(p-1) ∣ p^q - 1` via `p ≡ 1 [MOD p-1]`.
  have hpmod : (1 : ℕ) ≡ p [MOD (p - 1)] := (Nat.modEq_iff_dvd' hp1).mpr (dvd_refl (p - 1))
  have hpq_dvd : (p - 1) ∣ p ^ q - 1 := by
    have h := hpmod.pow q
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h
  have hmul : (p ^ q - 1) / (p - 1) * (p - 1) = p ^ q - 1 := Nat.div_mul_cancel hpq_dvd
  set u := (p ^ q - 1) / (p - 1) with hu
  have hu_dvd_pq : u ∣ p ^ q - 1 := ⟨p - 1, hmul.symm⟩
  -- `u ∣ gcd(p^q-1, p^D-1) = p^(gcd q D) - 1 = p - 1`.
  have hg : u ∣ Nat.gcd (p ^ q - 1) (p ^ D - 1) := Nat.dvd_gcd hu_dvd_pq hdvd
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have hcop : Nat.gcd q D = 1 := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqD
  rw [hcop, pow_one] at hg
  have hle : u ≤ p - 1 := Nat.le_of_dvd (by omega) hg
  -- `u·(p-1) = p^q-1 ≥ p^2-1`, but `u ≤ p-1` gives `u·(p-1) ≤ (p-1)^2 = p^2-2p+1 < p^2-1`.
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have hm1 : m + 2 - 1 = m + 1 := rfl
  rw [hm1] at hmul hle
  have hpos : 1 ≤ (m + 2) ^ q := Nat.one_le_pow _ _ (by omega)
  have hmul' : u * (m + 1) + 1 = (m + 2) ^ q := by omega
  have hpq2 : (m + 2) ^ 2 ≤ (m + 2) ^ q := Nat.pow_le_pow_right (by omega) hq.two_le
  nlinarith [hmul', hpq2, Nat.mul_le_mul hle (le_refl (m + 1))]

end OddOrder.RepresentationTheory
