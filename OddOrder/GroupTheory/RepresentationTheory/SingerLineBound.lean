/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SingerField

/-!
# The Singer line bound: `|C| ∣ (p^q − 1)/(p − 1)`

The σ-theory foundation of Peterfalvi (9.7)(b) (the *Galois* branch of `typeP_Galois`): a faithful
irreducible action of a finite commutative group `C` on an `𝔽_p`-space `M` of order `p^q` realizes
the field `𝔽_{p^q}` with `C ↪ 𝔽_{p^q}^×` (the Singer mechanism, `SingerField.lean`), giving the
*coarse* bound `|C| ∣ p^q − 1`.  When moreover `C` acts *fixed-point-freely* relative to an
additive automorphism (the Frobenius setup of (9.7)), `|C|` is coprime to `p − 1`
(`coprime_card_sub_one_of_faithful_irreducible_comm_fpf`); the two combine to the *refined* bound

  `|C| ∣ (p^q − 1)/(p − 1)`,

i.e. `C` embeds in the group of `𝔽_{p^q}^×`-elements modulo the scalar subgroup `𝔽_p^×` — it acts
on the projective lines.  This is the divisibility that Peterfalvi (13.2.c) uses for `u`
(`basic_structure.u_bound`, via `caseB_u_bound_arith` on the non-Galois side) and the Galois branch
of (13.12) `c_eq_one`.

The arithmetic heart (`dvd_div_of_coprime_of_dvd_sub_one`) is a general `ℕ` fact isolated for reuse.
-/

namespace OddOrder.RepresentationTheory

universe u

/-- **Arithmetic core of the Singer line bound**: if `a ∣ p^q − 1` and `a` is coprime to `p − 1`,
then `a ∣ (p^q − 1)/(p − 1)`.

`p − 1` divides `p^q − 1` (`nat_sub_dvd_pow_sub_pow p 1 q`), so `p^q − 1 = (p − 1)·m` with
`m = (p^q − 1)/(p − 1)`; from `a ∣ (p − 1)·m` and `gcd(a, p − 1) = 1` the coprime cancellation
`Nat.Coprime.dvd_of_dvd_mul_left` gives `a ∣ m`.  Pure `ℕ` arithmetic, `sorry`-free. -/
theorem dvd_div_of_coprime_of_dvd_sub_one {p q a : ℕ} (hp : 1 ≤ p)
    (hadvd : a ∣ p ^ q - 1) (hcop : Nat.Coprime a (p - 1)) :
    a ∣ (p ^ q - 1) / (p - 1) := by
  -- `(p − 1) ∣ p^q − 1` via `1 ≡ p [MOD p−1]` raised to the `q`-th power.
  have hsub : (p - 1) ∣ p ^ q - 1 := by
    have hpmod : (1 : ℕ) ≡ p [MOD (p - 1)] := (Nat.modEq_iff_dvd' hp).mpr (dvd_refl (p - 1))
    have h := hpmod.pow q
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h
  -- `p^q − 1 = (p − 1) · m` with `m = (p^q − 1)/(p − 1)`.
  have hfac : p ^ q - 1 = (p - 1) * ((p ^ q - 1) / (p - 1)) :=
    (Nat.mul_div_cancel' hsub).symm
  -- `a ∣ (p − 1) · m`, and `a` coprime to `p − 1`, so `a ∣ m`.
  rw [hfac] at hadvd
  exact hcop.dvd_of_dvd_mul_left hadvd

/-- **Singer line bound** (Peterfalvi (9.7)(b) Galois divisibility): a faithful, fixed-point-free,
irreducible action of a finite commutative group `C` on an `𝔽_p`-module `M` of order `p^q` has

  `|C| ∣ (p^q − 1)/(p − 1)`.

Assembles the two `SingerField` outputs — `|C| ∣ p^q − 1`
(`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`, the Singer embedding `C ↪ 𝔽_{p^q}^×`)
and `gcd(|C|, p − 1) = 1` (`coprime_card_sub_one_of_faithful_irreducible_comm_fpf`, the
fixed-point-free
trivial intersection `C ∩ 𝔽_p^× = 1`) — through the arithmetic core
`dvd_div_of_coprime_of_dvd_sub_one`.  This is the divisibility Peterfalvi (13.2.c) reads for `u` in
the Galois branch of `typeP_Galois` (issue 9000; consumed by `basic_structure.u_bound` and the
Galois
branch of (13.12) `c_eq_one`). -/
theorem card_dvd_cyclotomicQuotient_of_faithful_irreducible_fpf
    {p q : ℕ} [Fact p.Prime] {C M : Type u}
    [CommGroup C] [Finite C] [AddCommGroup M] [Finite M]
    [Module (MonoidAlgebra (ZMod p) C) M] [IsSimpleModule (MonoidAlgebra (ZMod p) C) M]
    (hcardM : Nat.card M = p ^ q)
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1)
    (σ : M ≃+ M)
    (hfpf : ∀ c : C, (∀ x : M, σ (MonoidAlgebra.of (ZMod p) C c • x)
                              = MonoidAlgebra.of (ZMod p) C c • σ x) → c = 1) :
    Nat.card C ∣ (p ^ q - 1) / (p - 1) := by
  have hp : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
  have hdvd : Nat.card C ∣ p ^ q - 1 := by
    have h := (isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible
      (p := p) (C := C) (M := M) hfaith).2
    rwa [hcardM] at h
  have hcop : Nat.Coprime (Nat.card C) (p - 1) :=
    coprime_card_sub_one_of_faithful_irreducible_comm_fpf mul_comm hfaith σ hfpf
  exact dvd_div_of_coprime_of_dvd_sub_one hp hdvd hcop

/-- **Singer line bound, `≤` form** (Peterfalvi (13.2.c) Galois branch): under the hypotheses of
`card_dvd_cyclotomicQuotient_of_faithful_irreducible_fpf` and `q ≥ 1`,

  `|C| ≤ (p^q − 1)/(p − 1)`.

The divisibility upgrades to the inequality since the quotient is positive (`p^q ≥ p`, so
`p^q − 1 ≥ p − 1 > 0`, and `(p−1) ∣ p^q − 1`).  This is precisely `basic_structure.u_bound`'s
Galois half: `u = |Ū| ≤ (p^q − 1)/(p − 1)`. -/
theorem card_le_cyclotomicQuotient_of_faithful_irreducible_fpf
    {p q : ℕ} [Fact p.Prime] {C M : Type u}
    [CommGroup C] [Finite C] [AddCommGroup M] [Finite M]
    [Module (MonoidAlgebra (ZMod p) C) M] [IsSimpleModule (MonoidAlgebra (ZMod p) C) M]
    (hq : 1 ≤ q) (hcardM : Nat.card M = p ^ q)
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1)
    (σ : M ≃+ M)
    (hfpf : ∀ c : C, (∀ x : M, σ (MonoidAlgebra.of (ZMod p) C c • x)
                              = MonoidAlgebra.of (ZMod p) C c • σ x) → c = 1) :
    Nat.card C ≤ (p ^ q - 1) / (p - 1) := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hdvd := card_dvd_cyclotomicQuotient_of_faithful_irreducible_fpf hcardM hfaith σ hfpf
  -- `(p^q − 1)/(p − 1) > 0`: `p − 1 ≤ p^q − 1` (as `p ≤ p^q`) and `0 < p − 1`.
  have hple : p ≤ p ^ q := Nat.le_self_pow (by omega) p
  have hpos : 0 < (p ^ q - 1) / (p - 1) := Nat.div_pos (by omega) (by omega)
  exact Nat.le_of_dvd hpos hdvd

end OddOrder.RepresentationTheory
