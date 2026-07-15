/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RepresentationTheory.Maschke
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import OddOrder.GroupTheory.PrimitivePrimeDivisor

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

/-- If `a ∣ b` then `p^a - 1 ∣ p^b - 1` (a divisor of exponents lifts to a divisor of
`p^· - 1`).  Derived from `gcd(p^a-1, p^b-1) = p^{gcd a b}-1` with `gcd a b = a`. -/
theorem pow_sub_one_dvd_of_dvd {p a b : ℕ} (h : a ∣ b) : p ^ a - 1 ∣ p ^ b - 1 := by
  have hg : Nat.gcd (p ^ a - 1) (p ^ b - 1) = p ^ a - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_eq_left h]
  rw [← hg]
  exact Nat.gcd_dvd_right _ _

/-- A prime `q` does not divide `(q-1)!`. -/
theorem not_dvd_factorial_pred {q : ℕ} (hq : q.Prime) : ¬ q ∣ (q - 1).factorial := by
  rw [Nat.Prime.dvd_factorial hq]
  have := hq.two_le
  omega

/-! ## Irreducibility of a large-order faithful cyclic action

The Singer construction is applied to a cyclic group `C` of order `(p^q-1)/(p-1)` acting
faithfully on an `F_p`-space `M` of order `p^q` (`q` prime).  Such an action is automatically
**irreducible** (`M` is a simple `F_p[C]`-module): otherwise Maschke decomposes `M` into simple
constituents of dimensions `dᵢ < q`; each `Sᵢ` becomes a field of order `p^{dᵢ}` (Singer engine),
so a generator `g` satisfies `g^{p^{dᵢ}-1}=1` on `Sᵢ`, hence `g^{p^D-1}=1` on `M` for `D=(q-1)!`
(`dᵢ ∣ D`); faithfulness gives `|C| ∣ p^D-1` with `q ∤ D`, contradicting
`cyclotomicQuotient_not_dvd_pow_sub_one`. -/
section Irreducibility

variable {p : ℕ} [Fact p.Prime] {C M : Type u}
  [CommGroup C] [IsCyclic C] [Finite C]
  [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) C) M] [Finite M]

/-- **Singer irreducibility.**  A faithful action of a cyclic group `C` of order
`(p^q-1)/(p-1)` on an `F_p`-module `M` of order `p^q` (`q` prime) is irreducible.

`NeZero (Nat.card C : ZMod p)` records that `|C|` is coprime to `p` (so Maschke applies);
it holds because `(p^q-1)/(p-1)` divides `p^q-1`, which is coprime to `p`. -/
theorem isSimpleModule_of_isCyclic_faithful_card {q : ℕ} (hq : q.Prime)
    [NeZero (Nat.card C : ZMod p)]
    (hcardM : Nat.card M = p ^ q)
    (hcardC : Nat.card C = (p ^ q - 1) / (p - 1))
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    IsSimpleModule (MonoidAlgebra (ZMod p) C) M := by
  classical
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hMpos : 0 < Nat.card M := by rw [hcardM]; positivity
  haveI : IsSemisimpleModule (MonoidAlgebra (ZMod p) C) M := inferInstance
  haveI : Nontrivial M := by
    have hp2q : 2 ≤ p ^ q := le_trans hp2 (Nat.le_self_pow hq.pos.ne' p)
    have : 1 < Nat.card M := by rw [hcardM]; omega
    exact (Finite.one_lt_card_iff_nontrivial).mp this
  by_contra hns
  obtain ⟨s, _hindep, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (MonoidAlgebra (ZMod p) C) M
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  set D := (q - 1).factorial with hDdef
  set N := p ^ D - 1 with hNdef
  -- `g^N` fixes every simple constituent `m ∈ s`.
  have hfix : ∀ m ∈ s, ∀ x : M, x ∈ m → MonoidAlgebra.of (ZMod p) C (g ^ N) • x = x := by
    intro m hm x hxm
    haveI hsm : IsSimpleModule (MonoidAlgebra (ZMod p) C) ↥m := hsimple m hm
    haveI : Fintype ↥m := Fintype.ofFinite _
    obtain ⟨data⟩ := nonempty_singerFieldData (p := p) (C := C) (M := ↥m)
    -- `|m| = p^d`, `1 ≤ d < q`, `d ∣ D`.
    have hmdvd : Nat.card ↥m ∣ Nat.card M :=
      AddSubgroup.card_addSubgroup_dvd_card m.toAddSubgroup
    obtain ⟨d, hdq, hmcard⟩ := (Nat.dvd_prime_pow (Fact.out (p := p.Prime))).mp (hcardM ▸ hmdvd)
    have hmne : m ≠ ⊤ := by
      rintro rfl
      exact hns (IsSimpleModule.congr Submodule.topEquiv.symm)
    have hcard_ne : Nat.card ↥m ≠ Nat.card M := by
      intro heq
      apply hmne
      have hAtop : m.toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq m.toAddSubgroup heq
      rwa [Submodule.toAddSubgroup_eq_top] at hAtop
    have hmlt : Nat.card ↥m < Nat.card M :=
      lt_of_le_of_ne (Nat.le_of_dvd hMpos hmdvd) hcard_ne
    have hdltq : d < q := by
      rw [hmcard, hcardM] at hmlt
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp hmlt
    have hd1 : 1 ≤ d := by
      have h2 : 2 ≤ Nat.card ↥m :=
        (Finite.one_lt_card_iff_nontrivial).mpr
          (IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) C) ↥m)
      rcases Nat.eq_zero_or_pos d with h0 | h
      · rw [h0, pow_zero] at hmcard; omega
      · exact h
    have hdD : d ∣ D := Nat.dvd_factorial hd1 (by omega)
    -- `μ(g)^(p^d-1) = 1`, hence `μ(g)^N = 1`.
    have hKcard : Fintype.card data.K = p ^ d := by
      rw [data.card_K_eq, ← Nat.card_eq_fintype_card, hmcard]
    have hμpow : (data.μ g) ^ (p ^ d - 1) = 1 := by
      have hu : (data.μ g) ^ (Fintype.card data.Kˣ) = 1 := pow_card_eq_one
      rwa [Fintype.card_units, hKcard] at hu
    have hμN : (data.μ g) ^ N = 1 := by
      obtain ⟨k, hk⟩ := pow_sub_one_dvd_of_dvd (p := p) hdD
      rw [hNdef, hk, pow_mul, hμpow, one_pow]
    -- Transport along `data.compat` to fix `x`.
    have hcompat := data.compat (g ^ N) ⟨x, hxm⟩
    have hμcoe : ((data.μ (g ^ N) : data.K)) = 1 := by
      rw [map_pow, hμN, Units.val_one]
    rw [hμcoe, one_mul] at hcompat
    have hfixsub : MonoidAlgebra.of (ZMod p) C (g ^ N) • (⟨x, hxm⟩ : ↥m) = ⟨x, hxm⟩ :=
      data.e.injective hcompat
    simpa using congrArg (Subtype.val) hfixsub
  -- `g^N` fixes all of `M` (the fixed locus is a submodule containing `sSup s = ⊤`).
  have hfixM : ∀ x : M, MonoidAlgebra.of (ZMod p) C (g ^ N) • x = x := by
    have hle : (⊤ : Submodule (MonoidAlgebra (ZMod p) C) M) ≤
        LinearMap.eqLocus
          (LinearMap.lsmul (MonoidAlgebra (ZMod p) C) M
            (MonoidAlgebra.of (ZMod p) C (g ^ N))) LinearMap.id := by
      rw [← hsup]
      refine sSup_le fun m hm => ?_
      intro x hx
      simpa [LinearMap.mem_eqLocus] using hfix m hm x hx
    intro x
    have hx : x ∈ LinearMap.eqLocus _ _ := hle Submodule.mem_top
    simpa [LinearMap.mem_eqLocus] using hx
  -- Faithfulness gives `g^N = 1`, so `card C ∣ N`, contradicting the number theory.
  have hgN : g ^ N = 1 := hfaith _ hfixM
  have hcardCdvd : Nat.card C ∣ N := by
    have h := orderOf_dvd_of_pow_eq_one hgN
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg] at h
  rw [hcardC, hNdef] at hcardCdvd
  exact cyclotomicQuotient_not_dvd_pow_sub_one hp2 hq (not_dvd_factorial_pred hq) hcardCdvd

omit [IsCyclic C] in
/-- **Singer irreducibility, abelian form.**  A faithful action of an abelian group `C` of order
`(p^q-1)/(p-1)` on an `F_p`-module `M` of order `p^q` (`q` an *odd* prime) is irreducible —
**without assuming `C` cyclic**.  This is the input that lets one *deduce* `C` cyclic (via the
Singer embedding), rather than assuming it (Peterfalvi (13.2.a) `U`/`V`-cyclic).

The cyclic proof uses the generator only to derive `card C ∣ N` from `g^N = 1`.  Here we instead
take a **primitive prime divisor** `r` of `p^q - 1` dividing `card C = ∑_{i<q} p^i`
(`exists_prime_orderOf_eq`), a Cauchy element `a` of order `r`, and the same fixed-point argument:
`a^N = 1`, so `r ∣ N = p^{(q-1)!} - 1`, i.e. `q = orderOf (p : ZMod r) ∣ (q-1)!`, contradicting
Wilson (`not_dvd_factorial_pred`). -/
theorem isSimpleModule_of_abelian_faithful_card {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    [NeZero (Nat.card C : ZMod p)]
    (hcardM : Nat.card M = p ^ q)
    (hcardC : Nat.card C = (p ^ q - 1) / (p - 1))
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    IsSimpleModule (MonoidAlgebra (ZMod p) C) M := by
  classical
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hq2ne : q ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hqodd
  have hMpos : 0 < Nat.card M := by rw [hcardM]; positivity
  haveI : IsSemisimpleModule (MonoidAlgebra (ZMod p) C) M := inferInstance
  haveI : Nontrivial M := by
    have hp2q : 2 ≤ p ^ q := le_trans hp2 (Nat.le_self_pow hq.pos.ne' p)
    have : 1 < Nat.card M := by rw [hcardM]; omega
    exact (Finite.one_lt_card_iff_nontrivial).mp this
  by_contra hns
  obtain ⟨s, _hindep, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (MonoidAlgebra (ZMod p) C) M
  set D := (q - 1).factorial with hDdef
  set N := p ^ D - 1 with hNdef
  -- For **any** `c`, `c^N` fixes every simple constituent `m ∈ s`.
  have hfix : ∀ (c : C), ∀ m ∈ s, ∀ x : M, x ∈ m →
      MonoidAlgebra.of (ZMod p) C (c ^ N) • x = x := by
    intro c m hm x hxm
    haveI hsm : IsSimpleModule (MonoidAlgebra (ZMod p) C) ↥m := hsimple m hm
    haveI : Fintype ↥m := Fintype.ofFinite _
    obtain ⟨data⟩ := nonempty_singerFieldData (p := p) (C := C) (M := ↥m)
    have hmdvd : Nat.card ↥m ∣ Nat.card M :=
      AddSubgroup.card_addSubgroup_dvd_card m.toAddSubgroup
    obtain ⟨d, hdq, hmcard⟩ := (Nat.dvd_prime_pow (Fact.out (p := p.Prime))).mp (hcardM ▸ hmdvd)
    have hmne : m ≠ ⊤ := by
      rintro rfl
      exact hns (IsSimpleModule.congr Submodule.topEquiv.symm)
    have hcard_ne : Nat.card ↥m ≠ Nat.card M := by
      intro heq
      apply hmne
      have hAtop : m.toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq m.toAddSubgroup heq
      rwa [Submodule.toAddSubgroup_eq_top] at hAtop
    have hmlt : Nat.card ↥m < Nat.card M :=
      lt_of_le_of_ne (Nat.le_of_dvd hMpos hmdvd) hcard_ne
    have hdltq : d < q := by
      rw [hmcard, hcardM] at hmlt
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp hmlt
    have hd1 : 1 ≤ d := by
      have h2 : 2 ≤ Nat.card ↥m :=
        (Finite.one_lt_card_iff_nontrivial).mpr
          (IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) C) ↥m)
      rcases Nat.eq_zero_or_pos d with h0 | h
      · rw [h0, pow_zero] at hmcard; omega
      · exact h
    have hdD : d ∣ D := Nat.dvd_factorial hd1 (by omega)
    have hKcard : Fintype.card data.K = p ^ d := by
      rw [data.card_K_eq, ← Nat.card_eq_fintype_card, hmcard]
    have hμpow : (data.μ c) ^ (p ^ d - 1) = 1 := by
      have hu : (data.μ c) ^ (Fintype.card data.Kˣ) = 1 := pow_card_eq_one
      rwa [Fintype.card_units, hKcard] at hu
    have hμN : (data.μ c) ^ N = 1 := by
      obtain ⟨k, hk⟩ := pow_sub_one_dvd_of_dvd (p := p) hdD
      rw [hNdef, hk, pow_mul, hμpow, one_pow]
    have hcompat := data.compat (c ^ N) ⟨x, hxm⟩
    have hμcoe : ((data.μ (c ^ N) : data.K)) = 1 := by
      rw [map_pow, hμN, Units.val_one]
    rw [hμcoe, one_mul] at hcompat
    have hfixsub : MonoidAlgebra.of (ZMod p) C (c ^ N) • (⟨x, hxm⟩ : ↥m) = ⟨x, hxm⟩ :=
      data.e.injective hcompat
    simpa using congrArg (Subtype.val) hfixsub
  have hfixM : ∀ (c : C), ∀ x : M, MonoidAlgebra.of (ZMod p) C (c ^ N) • x = x := by
    intro c
    have hle : (⊤ : Submodule (MonoidAlgebra (ZMod p) C) M) ≤
        LinearMap.eqLocus
          (LinearMap.lsmul (MonoidAlgebra (ZMod p) C) M
            (MonoidAlgebra.of (ZMod p) C (c ^ N))) LinearMap.id := by
      rw [← hsup]
      refine sSup_le fun m hm => ?_
      intro x hx
      simpa [LinearMap.mem_eqLocus] using hfix c m hm x hx
    intro x
    have hx : x ∈ LinearMap.eqLocus _ _ := hle Submodule.mem_top
    simpa [LinearMap.mem_eqLocus] using hx
  -- A **primitive prime divisor** `r ∣ card C` with `orderOf (p : ZMod r) = q`.
  obtain ⟨r, hr, hrn, hord⟩ := OddOrder.NumberTheory.exists_prime_orderOf_eq hp2 hq hq2ne
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype C := Fintype.ofFinite _
  have hrdvdC : r ∣ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card, hcardC, ← Nat.geomSum_eq hp2 q]; exact hrn
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card r hrdvdC
  -- `a^N = 1` (faithful), so `r = orderOf a ∣ N`; but `r ∤ N` by Wilson.
  have haN : a ^ N = 1 := hfaith _ (hfixM a)
  have hrN : r ∣ N := ha ▸ orderOf_dvd_of_pow_eq_one haN
  have hnotdvd : ¬ r ∣ N := by
    rw [hNdef]
    intro hdvd
    have hpD1 : (p : ZMod r) ^ D = 1 := by
      have h0 : ((p ^ D - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      have hle1 : 1 ≤ p ^ D := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub hle1] at h0
      exact sub_eq_zero.mp h0
    have hqdvdD : q ∣ D := by
      rw [← hord]; exact orderOf_dvd_of_pow_eq_one hpD1
    rw [hDdef] at hqdvdD
    exact not_dvd_factorial_pred hq hqdvdD
  exact hnotdvd hrN

omit [IsCyclic C] [Finite C] in
/-- **Galois-field realization of a faithful irreducible abelian action.**

If a commutative group `C` acts faithfully and irreducibly on a finite
`F_p[C]`-module `M` of order `p^q`, then `M` is additively `GF(p^q)` and
the action is multiplication through an injective homomorphism
`C → GF(p^q)ˣ`.

Unlike `exists_galoisField_repr`, this theorem takes irreducibility directly
as an `IsSimpleModule` instance and imposes no order condition on `C`.  This
is the branch-independent Singer entry used by Peterfalvi (9.7.b), including
the divided-order branch needed in (14.6). -/
theorem exists_galoisField_repr_of_faithful_irreducible {q : ℕ} (hq : q ≠ 0)
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M]
    (hcardM : Nat.card M = p ^ q)
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    ∃ (e : M ≃+ GaloisField p q) (μ : C →* (GaloisField p q)ˣ),
      Function.Injective μ ∧
      ∀ (c : C) (x : M),
        e (MonoidAlgebra.of (ZMod p) C c • x) = (μ c : GaloisField p q) * e x := by
  classical
  haveI : Fintype M := Fintype.ofFinite _
  obtain ⟨data⟩ := nonempty_singerFieldData (p := p) (C := C) (M := M)
  obtain ⟨φ⟩ := data.nonempty_ringEquiv_galoisField hq
    (by rw [← Nat.card_eq_fintype_card, hcardM])
  refine ⟨data.e.trans φ.toAddEquiv,
    (Units.map (φ : data.K →+* GaloisField p q).toMonoidHom).comp data.μ, ?_, ?_⟩
  · -- Faithfulness turns the multiplicative realization into an embedding.
    rw [injective_iff_map_eq_one]
    intro c hc
    apply hfaith c
    intro x
    have hcoe : φ ((data.μ c : data.K)) = 1 := by
      have := congrArg (Units.val) hc
      simpa [Units.coe_map] using this
    have hdμ : (data.μ c : data.K) = 1 := by
      have := φ.injective (hcoe.trans (map_one φ).symm)
      exact this
    have hcompat := data.compat c x
    rw [hdμ, one_mul] at hcompat
    exact data.e.injective hcompat
  · intro c x
    have hμc : ((((Units.map (φ : data.K →+* GaloisField p q).toMonoidHom).comp data.μ) c :
        (GaloisField p q)ˣ) : GaloisField p q) = φ ((data.μ c : data.K)) := by
      simp [Units.coe_map]
    calc (data.e.trans φ.toAddEquiv) (MonoidAlgebra.of (ZMod p) C c • x)
        = φ (data.e (MonoidAlgebra.of (ZMod p) C c • x)) := rfl
      _ = φ ((data.μ c : data.K) * data.e x) := by rw [data.compat c x]
      _ = φ ((data.μ c : data.K)) * φ (data.e x) := map_mul _ _ _
      _ = (((Units.map (φ : data.K →+* GaloisField p q).toMonoidHom).comp data.μ) c :
            GaloisField p q) * (data.e.trans φ.toAddEquiv) x := by rw [hμc]; rfl

omit [IsCyclic C] in
/-- **Peterfalvi (14.2)(a), abstract form.**  A faithful action of an abelian group `C` of order
`(p^q-1)/(p-1)` on an `F_p`-module `M` of order `p^q` (`q` an *odd* prime) realizes `M` as the
Galois field `GF(p^q)` with `C` embedded in the multiplicative group `GF(p^q)ˣ`: there is an
additive isomorphism `e : M ≃+ GF(p^q)` and an injective `μ : C →* GF(p^q)ˣ` with
`e (c • x) = μ c · e x`.

This is the field-isomorphism that the Section 16 finite-field model (`FieldNormalizerData`)
requires: combine `isSimpleModule_of_abelian_faithful_card` (irreducibility), the Singer engine,
and `nonempty_ringEquiv_galoisField` (uniqueness of finite fields). -/
theorem exists_galoisField_repr {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    [NeZero (Nat.card C : ZMod p)]
    (hcardM : Nat.card M = p ^ q) (hcardC : Nat.card C = (p ^ q - 1) / (p - 1))
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    ∃ (e : M ≃+ GaloisField p q) (μ : C →* (GaloisField p q)ˣ),
      Function.Injective μ ∧
      ∀ (c : C) (x : M),
        e (MonoidAlgebra.of (ZMod p) C c • x) = (μ c : GaloisField p q) * e x := by
  haveI hsimp : IsSimpleModule (MonoidAlgebra (ZMod p) C) M :=
    isSimpleModule_of_abelian_faithful_card hq hqodd hcardM hcardC hfaith
  exact exists_galoisField_repr_of_faithful_irreducible hq.pos.ne' hcardM hfaith

omit [IsCyclic C] [Finite C] in
/-- **Singer order bound.**  A (commutative) group `C` acting `𝔽_p`-linearly,
faithfully, and irreducibly (`M` a *simple* `𝔽_p[C]`-module) on a finite module `M` is
**cyclic**, and its order **divides `|M| - 1`**.

`C` embeds (via `nonempty_singerFieldData`) in the multiplicative group `Kˣ` of the Singer
field `K ≅ M`, which is cyclic of order `|K| - 1 = |M| - 1`; faithfulness makes the embedding
`μ : C →* Kˣ` injective.

This is the field-theoretic core of the irreducible case of **Peterfalvi (12.12)** (a Frobenius
complement acting irreducibly on an elementary abelian Sylow subgroup `T` of order `p^2` is
cyclic of order dividing `p^2 - 1`), and the order half of **(14.2)(a)**.

`Finite C` is *derived* (the injection `μ : C →* Kˣ` lands in the finite `Kˣ`), so it is not
assumed; neither `IsCyclic C` nor `Fact p.Prime` is needed. -/
theorem isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M]
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    IsCyclic C ∧ Nat.card C ∣ Nat.card M - 1 := by
  classical
  obtain ⟨data⟩ := nonempty_singerFieldData (p := p) (C := C) (M := M)
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype data.K := data.fintype
  -- The realization `μ : C →* Kˣ` is injective by faithfulness.
  have hμinj : Function.Injective data.μ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    apply hfaith c
    intro x
    have hcompat := data.compat c x
    rw [hc, Units.val_one, one_mul] at hcompat
    exact data.e.injective hcompat
  -- `Kˣ` is cyclic (finite field), so its subgroup `range μ` is cyclic, hence so is `C`.
  haveI : IsCyclic data.Kˣ := inferInstance
  haveI : IsCyclic data.μ.range := inferInstance
  have hCcyc : IsCyclic C :=
    isCyclic_of_surjective (MonoidHom.ofInjective hμinj).symm.toMonoidHom
      (MonoidHom.ofInjective hμinj).symm.surjective
  refine ⟨hCcyc, ?_⟩
  -- `|C| = |range μ|` divides `|Kˣ| = |K| - 1 = |M| - 1`.
  have hcardC : Nat.card C = Nat.card data.μ.range :=
    Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv
  have hdvd : Nat.card data.μ.range ∣ Nat.card data.Kˣ :=
    Subgroup.card_subgroup_dvd_card _
  have hunits : Nat.card data.Kˣ = Nat.card data.K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hKM : Nat.card data.K = Nat.card M := (Nat.card_congr data.e.toEquiv).symm
  rw [hunits, hKM] at hdvd
  rw [hcardC]
  exact hdvd

end Irreducibility

/-! ## Coprimality from a trivial intersection in a cyclic group

The fixed-point-free half of Peterfalvi (9.7)(b) supplies a *trivial intersection*
`Ū ∩ 𝔽ₚ* = 1` inside the cyclic multiplicative group of the Singer field; the divisibility
`|Ū| ∣ (p^q-1)/(p-1)` then needs `|Ū|` coprime to `p-1`.  In a cyclic group, a trivial
intersection of two subgroups *does* force coprime orders (the converse of
`Subgroup.disjoint_of_coprime_natCard`, which fails in general groups). -/

/-- In a finite cyclic group, two subgroups with trivial intersection have coprime orders.

Valid because a cyclic group has a *unique* subgroup of each order dividing the group order:
with `g = gcd(|H|, |K|)`, the `g`-torsion subgroup `ker(x ↦ x^g)` has order `gcd(|Z|, g) = g`
and lies in both `H` and `K` (each subgroup is its own `|·|`-torsion), hence in `H ⊓ K = ⊥`,
forcing `g = 1`. -/
theorem coprime_card_of_inf_eq_bot_isCyclic {Z : Type*} [CommGroup Z] [Finite Z] [IsCyclic Z]
    {H K : Subgroup Z} (hdisj : H ⊓ K = ⊥) :
    Nat.Coprime (Nat.card H) (Nat.card K) := by
  classical
  -- Each subgroup `J` is the kernel of `x ↦ x ^ |J|` (its `|J|`-torsion).
  have htorsion : ∀ J : Subgroup Z, (powMonoidHom (Nat.card J) : Z →* Z).ker = J := by
    intro J
    have hsub : J ≤ (powMonoidHom (Nat.card J) : Z →* Z).ker := by
      intro x hx
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hpow : ((⟨x, hx⟩ : J) ^ Nat.card J : J) = (1 : J) := pow_card_eq_one'
      have := congrArg (Subgroup.subtype J) hpow
      rw [map_pow, map_one] at this
      exact this
    have hcard : Nat.card (powMonoidHom (Nat.card J) : Z →* Z).ker = Nat.card J := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Subgroup.card_subgroup_dvd_card J)]
    exact (Subgroup.eq_of_le_of_card_ge hsub hcard.le).symm
  -- `ker(x ↦ x^g)` is contained in both `H` and `K`, where `g = gcd(|H|,|K|)`.
  set g := Nat.gcd (Nat.card H) (Nat.card K) with hg
  have hgH : g ∣ Nat.card H := Nat.gcd_dvd_left _ _
  have hgK : g ∣ Nat.card K := Nat.gcd_dvd_right _ _
  have hkerle : ∀ (J : Subgroup Z), g ∣ Nat.card J →
      (powMonoidHom g : Z →* Z).ker ≤ J := by
    intro J hJ
    rw [← htorsion J]
    intro x hx
    simp only [MonoidHom.mem_ker, powMonoidHom_apply] at hx ⊢
    obtain ⟨k, hk⟩ := hJ
    rw [hk, pow_mul, hx, one_pow]
  have hbot : (powMonoidHom g : Z →* Z).ker ≤ ⊥ := by
    rw [← hdisj]; exact le_inf (hkerle H hgH) (hkerle K hgK)
  -- Its order is `gcd(|Z|, g) = g` (since `g ∣ |H| ∣ |Z|`), so `g = 1`.
  have hgZ : g ∣ Nat.card Z := hgH.trans (Subgroup.card_subgroup_dvd_card H)
  have : Nat.card (powMonoidHom g : Z →* Z).ker = 1 := by
    rw [le_bot_iff.mp hbot, Subgroup.card_bot]
  rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hgZ] at this
  exact this

/-! ## Singer mechanism with commutativity supplied as a hypothesis

`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible` requires a `CommGroup`
*instance*.  That is awkward to supply when commutativity is only available as a *proof*
`∀ a b, a * b = b * a` — for example the conclusion of **BG Theorem 2.6(a)**
(`odd_two_dim_abelian`), which abelianizes a plain `[Group E]` carrying a faithful
two-dimensional representation.

This variant takes the commutativity hypothesis directly.  For abelian `E` the group algebra
`𝔽_p[E]` *is* commutative, so we give it a `CommRing` structure built on top of its existing
`Ring` (no instance diamond, since the underlying `Ring` is reused), realize the Singer field
as the quotient `K = 𝔽_p[E] ⧸ I` by a maximal ideal (`M ≅ K` because `M` is simple), and read
off the injection `E ↪ Kˣ`.  As `Kˣ` is cyclic, so is `E`, and `|E| ∣ |K| - 1 = |M| - 1`. -/
section CommGroupFreeSinger

variable {p : ℕ} {E M : Type*} [Group E] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) E) M]

/-- For an abelian group `E`, the group algebra `𝔽_p[E]` is commutative. -/
theorem mul_comm_monoidAlgebra_of_comm (hcomm : ∀ a b : E, a * b = b * a)
    (x y : MonoidAlgebra (ZMod p) E) : x * y = y * x := by
  have hsingle : ∀ (a : E) (c : ZMod p) (z : MonoidAlgebra (ZMod p) E),
      MonoidAlgebra.single a c * z = z * MonoidAlgebra.single a c := by
    intro a c z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => rw [mul_add, add_mul, hf, hg]
    | single b d =>
        rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
          hcomm a b, mul_comm c d]
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, mul_add, hf, hg]
  | single a c => exact hsingle a c y

/-- **Singer mechanism, commutativity as a hypothesis.**  If a finite group `E` acts
faithfully (`hfaith`), commutatively (`hcomm`), and irreducibly
(`IsSimpleModule (𝔽_p[E]) M`) on a finite module `M`, then `E` is cyclic and `|E| ∣ |M| - 1`.

Unlike `isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`, this requires only a
*proof* of commutativity, not a `CommGroup` instance: the commutative `CommRing (𝔽_p[E])` is
supplied locally on top of the existing `Ring` and the Singer field is `𝔽_p[E] ⧸ I`. -/
theorem isCyclic_and_card_dvd_of_faithful_irreducible_comm [Finite E] [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) E) M]
    (hcomm : ∀ a b : E, a * b = b * a)
    (hfaith : ∀ e : E, (∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card M - 1 := by
  classical
  -- `𝔽_p[E]` is commutative; equip it with a `CommRing` built on its existing `Ring` (no diamond).
  letI : CommRing (MonoidAlgebra (ZMod p) E) :=
    { (inferInstance : Ring (MonoidAlgebra (ZMod p) E)) with
      mul_comm := mul_comm_monoidAlgebra_of_comm hcomm }
  -- `M` simple over `𝔽_p[E]` ⟹ `M ≅ 𝔽_p[E] ⧸ I` for a maximal ideal `I`; the quotient is a field.
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) E) (M := M)).mp ‹_›
  haveI : I.IsMaximal := hImax
  letI : Field (MonoidAlgebra (ZMod p) E ⧸ I) := Ideal.Quotient.field I
  haveI : Finite (MonoidAlgebra (ZMod p) E ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  -- `μ : E ↪ Kˣ` realizes `E` inside the units of the field `K = 𝔽_p[E] ⧸ I`.
  let μ : E →* (MonoidAlgebra (ZMod p) E ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) E →+* _).toMonoidHom).comp
      (MonoidAlgebra.of (ZMod p) E).toHomUnits
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply hfaith e
    intro x
    apply lequiv.injective
    have hcompat : lequiv (MonoidAlgebra.of (ZMod p) E e • x)
        = (↑(μ e) : MonoidAlgebra (ZMod p) E ⧸ I) * lequiv x := by
      rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]; rfl
    rw [hcompat, he, Units.val_one, one_mul]
  haveI : IsCyclic (MonoidAlgebra (ZMod p) E ⧸ I)ˣ := inferInstance
  haveI : IsCyclic μ.range := inferInstance
  refine ⟨isCyclic_of_surjective (MonoidHom.ofInjective hμinj).symm.toMonoidHom
      (MonoidHom.ofInjective hμinj).symm.surjective, ?_⟩
  -- `|E| = |μ.range| ∣ |Kˣ| = |K| - 1 = |M| - 1`.
  have hKM : Nat.card (MonoidAlgebra (ZMod p) E ⧸ I) = Nat.card M :=
    (Nat.card_congr lequiv.toEquiv).symm
  calc Nat.card E = Nat.card μ.range := Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv
    _ ∣ Nat.card (MonoidAlgebra (ZMod p) E ⧸ I)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = Nat.card (MonoidAlgebra (ZMod p) E ⧸ I) - 1 :=
        Nat.card_units (α := MonoidAlgebra (ZMod p) E ⧸ I)
    _ = Nat.card M - 1 := by rw [hKM]

/-- **Singer coprimality core, `𝔽ₚ`-scalar form.**  Adds to the Singer hypotheses (`E` finite
acting faithfully, commutatively, and irreducibly on the finite `𝔽ₚ[E]`-module `M`) the condition
that only `e = 1` acts on `M` as an `𝔽ₚ`-scalar (`x ↦ n • x`).  Then `|E|` is coprime to `p - 1`.

The realization `μ : E ↪ Kˣ` (`K = 𝔽ₚ[E] ⧸ I` the Singer field) meets the prime-subfield units
`ν : 𝔽ₚ* ↪ Kˣ` only in `1`: a common unit `μ e = ν c` makes `e` act as the scalar `(c).val`, so
`hnonscalar` forces `e = 1`.  Hence `μ.range ⊓ ν.range = ⊥` in the cyclic group `Kˣ`, and
`coprime_card_of_inf_eq_bot_isCyclic` yields `Coprime |E| (p - 1)`.  The fixed-point-free bridge
`coprime_card_sub_one_of_faithful_irreducible_comm_fpf` and the `p + 1` refinement of Peterfalvi
(12.12) both specialize this by supplying the non-scalar condition from their own structure. -/
theorem coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar
    [Fact p.Prime] [Finite E] [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) E) M]
    (hcomm : ∀ a b : E, a * b = b * a)
    (hfaith : ∀ e : E, (∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1)
    (hnonscalar : ∀ e : E,
        (∃ n : ℕ, ∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = n • x) → e = 1) :
    Nat.Coprime (Nat.card E) (p - 1) := by
  classical
  letI : CommRing (MonoidAlgebra (ZMod p) E) :=
    { (inferInstance : Ring (MonoidAlgebra (ZMod p) E)) with
      mul_comm := mul_comm_monoidAlgebra_of_comm hcomm }
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) E) (M := M)).mp ‹_›
  haveI : I.IsMaximal := hImax
  letI : Field (MonoidAlgebra (ZMod p) E ⧸ I) := Ideal.Quotient.field I
  haveI : Finite (MonoidAlgebra (ZMod p) E ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  let μ : E →* (MonoidAlgebra (ZMod p) E ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) E →+* _).toMonoidHom).comp
      (MonoidAlgebra.of (ZMod p) E).toHomUnits
  let ν : (ZMod p)ˣ →* (MonoidAlgebra (ZMod p) E ⧸ I)ˣ :=
    Units.map (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) E ⧸ I)).toMonoidHom
  have hcompat : ∀ (a : E) (x : M),
      lequiv (MonoidAlgebra.of (ZMod p) E a • x)
        = (↑(μ a) : MonoidAlgebra (ZMod p) E ⧸ I) * lequiv x := by
    intro a x
    rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]; rfl
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply hfaith e
    intro x
    apply lequiv.injective
    rw [hcompat e x, he, Units.val_one, one_mul]
  have hνinj : Function.Injective ν :=
    Units.map_injective (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) E ⧸ I)).injective
  haveI : IsCyclic (MonoidAlgebra (ZMod p) E ⧸ I)ˣ := inferInstance
  have hdisj : μ.range ⊓ ν.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨⟨e, he⟩, ⟨c, hc⟩⟩ := hz
    have hμν : (↑(μ e) : MonoidAlgebra (ZMod p) E ⧸ I)
        = algebraMap (ZMod p) (MonoidAlgebra (ZMod p) E ⧸ I) (c : ZMod p) := by
      have heν : μ e = ν c := he.trans hc.symm
      rw [heν, Units.coe_map]; rfl
    have hscalar : ∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = (c : ZMod p).val • x := by
      intro x
      apply lequiv.injective
      rw [hcompat e x, hμν, map_nsmul, nsmul_eq_mul]
      congr 1
      conv_lhs => rw [← ZMod.natCast_zmod_val (c : ZMod p)]
      rw [map_natCast]
    have he1 : e = 1 := hnonscalar e ⟨(c : ZMod p).val, hscalar⟩
    rw [← he, he1, map_one]
  have hcop := coprime_card_of_inf_eq_bot_isCyclic hdisj
  have hcardμ : Nat.card μ.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv).symm
  have hcardν : Nat.card ν.range = p - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hνinj).toEquiv, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]
  rwa [hcardμ, hcardν] at hcop

/-- **Peterfalvi (9.7)(b), the coprimality `Coprime |E| (p-1)`.**  Adds to the Singer hypotheses
(`E` finite abelian acting faithfully, commutatively, and irreducibly on the finite `𝔽ₚ[E]`-module
`M`) a fixed-point-free additive automorphism `σ` of `M`: the only `e` whose `𝔽ₚ[E]`-action
commutes with `σ` is `e = 1`.  Then `|E|` is coprime to `p - 1`.

This is the fixed-point-free input of (9.7)(b).  An `e ∈ E` whose realization `μ e ∈ Kˣ` lands in
the prime subfield `𝔽ₚ* = algebraMap '' (ZMod p)ˣ` acts on `M` as an `𝔽ₚ`-scalar (an `nsmul`),
hence commutes with the *additive* `σ`; fixed-point-freeness then forces `e = 1`.  So `E ↪ Kˣ` and
`𝔽ₚ* ↪ Kˣ` intersect trivially in the cyclic group `Kˣ` of the Singer field `K`, and
`coprime_card_of_inf_eq_bot_isCyclic` yields `Coprime |E| (p-1)`.

In Peterfalvi's application `σ = φ(w)` is the action of a nontrivial `w ∈ W₁`: an `𝔽ₚ`-scalar is
central in `Aut(H̄)`, so it is `W₁`-fixed, and `Ū ⋊ W₁` is Frobenius, so it is trivial. -/
theorem coprime_card_sub_one_of_faithful_irreducible_comm_fpf [Fact p.Prime] [Finite E] [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) E) M]
    (hcomm : ∀ a b : E, a * b = b * a)
    (hfaith : ∀ e : E, (∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1)
    (σ : M ≃+ M)
    (hfpf : ∀ e : E, (∀ x : M, σ (MonoidAlgebra.of (ZMod p) E e • x)
                              = MonoidAlgebra.of (ZMod p) E e • σ x) → e = 1) :
    Nat.Coprime (Nat.card E) (p - 1) :=
  -- An `𝔽ₚ`-scalar action `x ↦ n • x` commutes with the additive `σ`, so the non-scalar core
  -- applies with its scalar hypothesis discharged by fixed-point-freeness.
  coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar hcomm hfaith
    (fun e ⟨n, hn⟩ => hfpf e (fun x => by rw [hn, hn, map_nsmul]))

end CommGroupFreeSinger

end OddOrder.RepresentationTheory
