/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod

/-!
# BG Appendix C: the finite-field norm-set argument

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, pp. 145--152 (mmd L4855--5005).

This file develops the finite-field side of BG Appendix C (the Carlip--Wheeler
account of Peterfalvi's generators-and-relations argument) on the *actual* field
`GaloisField p q = 𝔽_{p^q}`, as opposed to the propositional scaffold carried by
`OddOrder.BG.AppC` in `AppC_FinalContradiction.lean`.

Let `p`, `q` be primes satisfying **condition (A)**
`gcd((p^q-1)/(p-1), p-1) = 1`.  Writing `N` for the norm of `𝔽_{p^q}` over `𝔽_p`,
the key object is the **norm set**

  `E = { a ∈ 𝔽_{p^q} | N(a) = N(2-a) = 1 }`.

The contradiction `p ≤ q` (BG Theorem C) is obtained from three lemmas:

* **Lemma C.1**: `E = E⁻¹ ∧ |E| ≥ 2  ⟹  p ≤ q`  (a polynomial root count);
* **Lemma C.2**: `|E| ≥ 2`  (case `q = 3` elementary, `q ≥ 5` via the character
  theory of the Frobenius group `H = P ⋊ U`);
* **Lemma C.3**: `E = E⁻¹`  (the generators-and-relations argument; needs the
  embedding hypothesis (B) into the minimal counterexample `G`).

## Main definitions

* `normN p q x` — the norm `N(x) = ∏_{i<q} x^{p^i}` of `x ∈ 𝔽_{p^q}` over `𝔽_p`.
* `normSetE p q` — the norm set `E`.

## Main results (this file)

* `conditionA_iff_not_dvd` — **Remark (I)**: condition (A) `⟺ q ∤ (p-1)`.
* `normOneUnits_card` — **Remark (VII)**: the norm-one subgroup
  `U ≤ 𝔽_{p^q}ˣ` has order `(p^q - 1)/(p - 1)`.
* `exists_primeFieldUnit_mul_normOne` — **Remark (VII)**: under condition (A),
  every unit of `𝔽_{p^q}` is a prime-field unit times an element of `U`.
* `primeFieldUnits_inf_normOneUnits_eq_bot` — **Remark (VII)**: the
  prime-field unit subgroup intersects `U` trivially under condition (A).
* `primeFieldUnits_mul_normOneUnits_eq_univ` — **Remark (VII)**: the
  carrier-set product `𝔽_pˣ · U` is all of `𝔽_{p^q}ˣ` under condition (A).
* `normOneFrobenius_conj_inl` — the concrete `H = P ⋊ U` action formula
  `u s u⁻¹ = u*s` for the q≥5 Frobenius-group branch of Lemma C.2.
* `mem_normOnePairSetAt_iff_inl_mul_inl` — the BG pair condition `us+vs=2s`
  rewritten as a product equation inside the additive kernel of `H`.
* `normOnePairSet_ncard_eq_normSetE_ncard` — the finite-field counting bridge
  identifying `|E|` with the number of pairs `(u, v) ∈ U × U` satisfying `u + v = 2`.
* `normOnePairSetAt_ncard_eq_normSetE_ncard` — the same bridge in BG
  Lemma C.2 form, with `u * s + v * s = 2 * s` for nonzero `s`.

Lemma C.1 and the `q = 3` branch of Lemma C.2 are formalized; the `q ≥ 5`
branch of C.2, Lemma C.3, and the assembly into BG Theorem C are tracked in
issue 3000 / `notes/bg/appC_normset_plan.md`.

## References

* Bender, Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188,
  1994), Appendix C.
-/

namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-! ## The norm and the norm set -/

/-- **BG App C norm** `N(x)`: the norm of `x ∈ 𝔽_{p^q}` over `𝔽_p`, written as the
product of its Frobenius conjugates `∏_{i<q} x^{p^i}` (this equals
`Algebra.norm (ZMod p) x`). -/
noncomputable def normN [Fact p.Prime] (x : GaloisField p q) : GaloisField p q :=
  ∏ i ∈ Finset.range q, x ^ (p ^ i)

/-- **BG App C norm set** `E = { a ∈ 𝔽_{p^q} | N(a) = N(2-a) = 1 }` (mmd L4853). -/
def normSetE [Fact p.Prime] : Set (GaloisField p q) :=
  {a | normN p q a = 1 ∧ normN p q (2 - a) = 1}

/-! ### Basic algebra of the norm and the norm set -/

@[simp] lemma normN_one [Fact p.Prime] : normN p q (1 : GaloisField p q) = 1 := by
  simp [normN]

/-- The norm is multiplicative (it is a product of multiplicative maps). -/
lemma normN_mul [Fact p.Prime] (x y : GaloisField p q) :
    normN p q (x * y) = normN p q x * normN p q y := by
  simp only [normN, mul_pow, Finset.prod_mul_distrib]

/-- The norm of a nonzero element is nonzero. -/
lemma normN_ne_zero [Fact p.Prime] {x : GaloisField p q} (hx : x ≠ 0) :
    normN p q x ≠ 0 := by
  simp only [normN]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hx

/-- The product definition `normN` agrees with the mathlib finite-field norm after
embedding `𝔽_p` into `𝔽_{p^q}`.  This is the bridge needed for the norm-one
subgroup `U` used in BG Appendix C, Remark (VII). -/
lemma normN_eq_algebraMap_norm [Fact p.Prime] (hq : q ≠ 0) (x : GaloisField p q) :
    normN p q x = algebraMap (ZMod p) (GaloisField p q) (Algebra.norm (ZMod p) x) := by
  simpa [normN, GaloisField.finrank p hq, Nat.card_zmod]
    using (FiniteField.algebraMap_norm_eq_prod_pow
      (ZMod p) (GaloisField p q) x).symm

/-- **BG Appendix C, Remark (VII)**: the subgroup
`U = {x ∈ 𝔽_{p^q}ˣ | N(x)=1}` of norm-one units. -/
noncomputable def normOneUnits [Fact p.Prime] : Subgroup (GaloisField p q)ˣ :=
  (Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))).ker

/-- The subgroup of `𝔽_{p^q}ˣ` consisting of units coming from the prime field
`𝔽_pˣ`.  Under condition (A), BG Appendix C Remark (VII) uses this subgroup
together with `U` to decompose `𝔽_{p^q}ˣ`. -/
noncomputable def primeFieldUnits [Fact p.Prime] : Subgroup (GaloisField p q)ˣ :=
  (Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom)).range

lemma mem_normOneUnits_iff_normN [Fact p.Prime] (hq : q ≠ 0)
    (u : (GaloisField p q)ˣ) :
    u ∈ normOneUnits p q ↔ normN p q (u : GaloisField p q) = 1 := by
  constructor
  · intro hu
    have hbase : Algebra.norm (ZMod p) (u : GaloisField p q) = 1 :=
      congrArg Units.val hu
    rw [normN_eq_algebraMap_norm p q hq, hbase, map_one]
  · intro hu
    ext
    apply (algebraMap (ZMod p) (GaloisField p q)).injective
    change algebraMap (ZMod p) (GaloisField p q)
        (Algebra.norm (ZMod p) (u : GaloisField p q)) =
      algebraMap (ZMod p) (GaloisField p q) (1 : ZMod p)
    rw [← normN_eq_algebraMap_norm p q hq, hu, map_one]

/-- **BG Appendix C, Remark (VII)**: `|U| = (p^q - 1)/(p - 1)` for the
norm-one subgroup `U ≤ 𝔽_{p^q}ˣ`.  This is the `|U|` used in the `q ≥ 5`
character-sum branch of Lemma C.2. -/
theorem normOneUnits_card [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) := by
  classical
  let f : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
  have hf_surj : Function.Surjective f :=
    FiniteField.unitsMap_norm_surjective (ZMod p) (GaloisField p q)
  have hker : normOneUnits p q = f.ker := rfl
  have hcod : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdom : Nat.card (GaloisField p q)ˣ = p ^ q - 1 := by
    rw [Nat.card_units, GaloisField.card p q hq]
  have hindex : f.ker.index = p - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj, Subgroup.card_top, hcod]
  have hmul : Nat.card (normOneUnits p q) * (p - 1) = p ^ q - 1 := by
    rw [hker, ← hindex, f.ker.card_mul_index, hdom]
  exact Nat.eq_div_of_mul_eq_right (ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
    (by simpa [mul_comm] using hmul)

/-- The norm of a prime-field unit, viewed in `𝔽_{p^q}`, is its `q`-th power. -/
theorem unitsMap_norm_primeFieldUnit [Fact p.Prime] (hq : q ≠ 0) (b : (ZMod p)ˣ) :
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
        (Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom) b) = b ^ q := by
  ext
  simp [Algebra.norm_algebraMap, GaloisField.finrank p hq]

/-- The pair set `{(u, v) ∈ U × U | u + v = 2}` whose cardinality is the
structure constant identified with `|E|` in BG Appendix C, Lemma C.2. -/
def normOnePairSet [Fact p.Prime] : Set (normOneUnits p q × normOneUnits p q) :=
  {uv | (((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) +
      ((uv.2 : (GaloisField p q)ˣ) : GaloisField p q)) = 2}

/-- The BG Appendix C, Lemma C.2 pair set at a nonzero additive element `s`: pairs
`(u, v) ∈ U × U` satisfying `u * s + v * s = 2 * s`.  BG identifies the
cardinality of this set with the structure constant of a class-sum product in
the Frobenius group `H = P ⋊ U`. -/
def normOnePairSetAt [Fact p.Prime] (s : GaloisField p q) :
    Set (normOneUnits p q × normOneUnits p q) :=
  {uv | (((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) * s +
      ((uv.2 : (GaloisField p q)ˣ) : GaloisField p q) * s) = 2 * s}

/-- For `s ≠ 0`, the BG pair condition `u * s + v * s = 2 * s` is equivalent to
`u + v = 2`. -/
theorem normOnePairSetAt_eq_normOnePairSet_of_ne_zero [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    normOnePairSetAt p q s = normOnePairSet p q := by
  ext uv
  constructor
  · intro h
    dsimp [normOnePairSetAt, normOnePairSet] at h ⊢
    have hmul : ((((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) +
        ((uv.2 : (GaloisField p q)ˣ) : GaloisField p q)) * s) =
        (2 : GaloisField p q) * s := by
      rw [right_distrib]
      exact h
    exact mul_right_cancel₀ hs hmul
  · intro h
    dsimp [normOnePairSetAt, normOnePairSet] at h ⊢
    rw [← right_distrib, h]

lemma mem_normSetE_iff [Fact p.Prime] {a : GaloisField p q} :
    a ∈ normSetE p q ↔ normN p q a = 1 ∧ normN p q (2 - a) = 1 := Iff.rfl

/-- `E` is symmetric under `a ↦ 2 - a` (the two norm conditions just swap). -/
lemma two_sub_mem_normSetE [Fact p.Prime] {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : (2 - a) ∈ normSetE p q := by
  refine ⟨ha.2, ?_⟩
  rw [show (2 : GaloisField p q) - (2 - a) = a by ring]
  exact ha.1

/-- `1 ∈ E`, since `N(1) = N(2-1) = N(1) = 1`. -/
lemma one_mem_normSetE [Fact p.Prime] : (1 : GaloisField p q) ∈ normSetE p q := by
  refine ⟨normN_one p q, ?_⟩
  rw [show (2 : GaloisField p q) - 1 = 1 by ring]
  exact normN_one p q

/-- If `E` has at least two elements then it contains an element `≠ 1` — the
`a ∈ E^#` with which the Lemma C.1 argument begins. -/
lemma exists_mem_normSetE_ne_one [Fact p.Prime]
    (hcard : 2 ≤ (normSetE p q).ncard) :
    ∃ a ∈ normSetE p q, a ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : normSetE p q ⊆ {1} := fun a ha => h a ha
  have hle : (normSetE p q).ncard ≤ ({1} : Set (GaloisField p q)).ncard :=
    Set.ncard_le_ncard hsub (Set.finite_singleton 1)
  rw [Set.ncard_singleton] at hle
  omega

/-! ## Remark (I): condition (A) ⟺ q ∤ (p-1) -/

/-- **BG Appendix C, Remark (I)** (mmd L4877): condition (A),
`gcd((p^q-1)/(p-1), p-1) = 1`, is equivalent to `q ∤ (p-1)`.

Indeed `(p^q-1)/(p-1) = ∑_{i<q} p^i ≡ q (mod p-1)` since `p ≡ 1 (mod p-1)`, so the
gcd with `p-1` is `gcd(q, p-1)`, which is `1` iff the prime `q` does not divide
`p-1`. -/
theorem conditionA_iff_not_dvd (hp : 2 ≤ p) (hq : q.Prime) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ ¬ q ∣ (p - 1) := by
  -- `(p^q-1)/(p-1)` is the geometric sum `∑_{i<q} p^i`.
  have hsum : (p ^ q - 1) / (p - 1) = ∑ k ∈ Finset.range q, p ^ k :=
    (Nat.geomSum_eq hp q).symm
  -- `↑p = 1` in `ZMod (p-1)`.
  have hp1 : (p : ZMod (p - 1)) = 1 := by
    have hcast : (p : ZMod (p - 1)) = ((p - 1) + 1 : ℕ) := by congr 1; omega
    rw [hcast, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  -- Hence `↑(∑_{i<q} p^i) = ↑q` in `ZMod (p-1)`.
  have hsumcast : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod (p - 1)) = (q : ZMod (p - 1)) := by
    push_cast
    rw [hp1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- Translate coprimality to a unit statement in `ZMod (p-1)`.
  have hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ Nat.Coprime q (p - 1) := by
    rw [hsum, ← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime, hsumcast]
  rw [hcop]
  exact hq.coprime_iff_not_dvd

/-- Under BG Appendix C condition (A), the `q`-power map on the prime-field unit
group `(ZMod p)ˣ` is surjective.  This is the finite cyclic-group input in
Remark (VII), used to split `𝔽_{p^q}ˣ` into prime-field units times `U`. -/
theorem zmodUnits_pow_surjective_of_conditionA [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    Function.Surjective (fun b : (ZMod p)ˣ => b ^ q) := by
  classical
  have hnot : ¬ q ∣ (p - 1) :=
    (conditionA_iff_not_dvd p q (Fact.out : p.Prime).two_le hq).mp hA
  have hcop : Nat.Coprime (p - 1) q :=
    ((hq.coprime_iff_not_dvd).mpr hnot).symm
  have hgcd : (Nat.card (ZMod p)ˣ).gcd q = 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact hcop
  have hindex : (powMonoidHom q : (ZMod p)ˣ →* (ZMod p)ˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hgcd]
  have htop : (powMonoidHom q : (ZMod p)ˣ →* (ZMod p)ˣ).range = ⊤ :=
    Subgroup.index_eq_one.mp hindex
  intro x
  have hx : x ∈ (powMonoidHom q : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    rw [htop]
    exact trivial
  rcases hx with ⟨b, rfl⟩
  exact ⟨b, rfl⟩

/-- **BG Appendix C, Remark (VII)** decomposition: under condition (A), every unit
of `𝔽_{p^q}` is a product of a prime-field unit and a norm-one unit.  This is the
Lean form of `𝔽_{p^q}ˣ = 𝔽_pˣ · U` used before the generator-relation argument. -/
theorem exists_primeFieldUnit_mul_normOne [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (x : (GaloisField p q)ˣ) :
    ∃ b : (ZMod p)ˣ, ∃ u : normOneUnits p q,
      x = Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom) b *
        (u : (GaloisField p q)ˣ) := by
  classical
  let normMap : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
  obtain ⟨b, hb⟩ := zmodUnits_pow_surjective_of_conditionA p q hq hA (normMap x)
  let bF : (GaloisField p q)ˣ :=
    Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom) b
  let uUnit : (GaloisField p q)ˣ := bF⁻¹ * x
  have hu_mem : uUnit ∈ normOneUnits p q := by
    change normMap uUnit = 1
    calc
      normMap uUnit = (normMap bF)⁻¹ * normMap x := by simp [uUnit, bF]
      _ = (b ^ q)⁻¹ * normMap x := by rw [unitsMap_norm_primeFieldUnit p q hq.ne_zero b]
      _ = 1 := by rw [← hb]; simp
  refine ⟨b, ⟨uUnit, hu_mem⟩, ?_⟩
  simp [uUnit, bF]

/-- **BG Appendix C, Remark (VII)**: under condition (A), the prime-field unit
subgroup and the norm-one subgroup meet trivially.  Together with
`exists_primeFieldUnit_mul_normOne`, this is the direct-product content of
`𝔽_{p^q}ˣ = 𝔽_pˣ × U`. -/
theorem primeFieldUnits_inf_normOneUnits_eq_bot [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    primeFieldUnits p q ⊓ normOneUnits p q = ⊥ := by
  classical
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_bot]
    have hxmem : x ∈ primeFieldUnits p q ∧ x ∈ normOneUnits p q := by
      simpa using hx
    rcases hxmem.1 with ⟨b, hb⟩
    let normMap : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
      Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
    have hnorm : normMap x = 1 := by
      simpa [normMap, normOneUnits] using hxmem.2
    have hbq : b ^ q = 1 := by
      rw [← unitsMap_norm_primeFieldUnit p q hq.ne_zero b, hb]
      exact hnorm
    have hsurj := zmodUnits_pow_surjective_of_conditionA p q hq hA
    have hinj : Function.Injective (fun b : (ZMod p)ˣ => b ^ q) :=
      (Finite.injective_iff_surjective).mpr hsurj
    have hb1 : b = 1 := hinj (by simpa using hbq)
    rw [hb1] at hb
    simpa using hb.symm
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact Subgroup.one_mem _

/-- **BG Appendix C, Remark (VII)**: under condition (A), the carrier-set product
of prime-field units and norm-one units is all of `𝔽_{p^q}ˣ`.  Together with
`primeFieldUnits_inf_normOneUnits_eq_bot`, this is the usable subgroup form of
`𝔽_{p^q}ˣ = 𝔽_pˣ × U`. -/
theorem primeFieldUnits_mul_normOneUnits_eq_univ [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    (primeFieldUnits p q : Set (GaloisField p q)ˣ) *
        (normOneUnits p q : Set (GaloisField p q)ˣ) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨b, u, hx⟩ := exists_primeFieldUnit_mul_normOne p q hq hA x
  refine Set.mem_mul.mpr ⟨
    Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom) b, ?_,
    (u : (GaloisField p q)ˣ), ?_, hx.symm⟩
  · exact ⟨b, rfl⟩
  · exact u.property

/-! ### Generator-relation finite-field helpers for Lemma C.3 -/

/-- **BG Appendix C, Lemma C.3, Step 1 (nonzero orbit form)**: under
condition (A), every nonzero field element lies in the `U`-orbit of a nonzero
point on any fixed nonzero prime-field line.  This is the finite-field content
of BG Step 1, using `𝔽_{p^q}ˣ = 𝔽_pˣ · U`. -/
theorem exists_normOne_mul_primeFieldUnit_mul_eq [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s x : GaloisField p q} (hs : s ≠ 0) (hx : x ≠ 0) :
    ∃ b : (ZMod p)ˣ, ∃ u : normOneUnits p q,
      x = (((u : (GaloisField p q)ˣ) : GaloisField p q) *
        ((algebraMap (ZMod p) (GaloisField p q) (b : ZMod p)) * s)) := by
  let F := GaloisField p q
  let emb : ZMod p →+* F := algebraMap (ZMod p) F
  let xOverS : Fˣ := Units.mk0 (x / s) (div_ne_zero hx hs)
  obtain ⟨b, u, hxu⟩ := exists_primeFieldUnit_mul_normOne p q hq hA xOverS
  refine ⟨b, u, ?_⟩
  let uval : F := ((u : Fˣ) : F)
  have hval : x / s = emb (b : ZMod p) * uval := by
    change (xOverS : F) = emb (b : ZMod p) * uval
    simpa [xOverS, emb, uval] using congrArg (fun z : Fˣ => (z : F)) hxu
  calc
    x = (x / s) * s := by rw [div_mul_cancel₀ _ hs]
    _ = (emb (b : ZMod p) * uval) * s := by rw [hval]
    _ = uval * (emb (b : ZMod p) * s) := by ring

/-- **BG Appendix C, Lemma C.3, Step 1 (prime-line decomposition)**: under
condition (A), every field element is a norm-one multiple of a point on any
fixed nonzero prime-field line.  The zero case supplies the identity element of
the additive kernel; the nonzero case is the direct-product decomposition of
`𝔽_{p^q}ˣ`. -/
theorem exists_normOne_mul_primeLine_eq [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s x : GaloisField p q} (hs : s ≠ 0) :
    ∃ c : ZMod p, ∃ u : normOneUnits p q,
      x = (((u : (GaloisField p q)ˣ) : GaloisField p q) *
        ((algebraMap (ZMod p) (GaloisField p q) c) * s)) := by
  by_cases hx : x = 0
  · refine ⟨0, 1, ?_⟩
    simp [hx]
  · obtain ⟨b, u, h⟩ :=
      exists_normOne_mul_primeFieldUnit_mul_eq p q hq hA (s := s) (x := x) hs hx
    exact ⟨(b : ZMod p), u, h⟩

/-- **BG Appendix C, Lemma C.3, Step 3 input**: under condition (A), the
norm-one subgroup acts irreducibly on the additive `𝔽_p`-space `𝔽_{p^q}`.
Any nonzero `U`-invariant subspace is the whole field. -/
theorem normOneUnits_invariant_submodule_eq_top_of_ne_bot [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (W : Submodule (ZMod p) (GaloisField p q))
    (hU : ∀ u : normOneUnits p q, ∀ x : GaloisField p q, x ∈ W →
      (((u : (GaloisField p q)ˣ) : GaloisField p q) * x) ∈ W)
    (hne : W ≠ ⊥) :
    W = ⊤ := by
  classical
  obtain ⟨s, hsW, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨c, u, hx⟩ := exists_normOne_mul_primeLine_eq p q hq hA (s := s) (x := x) hs0
  rw [hx]
  exact hU u ((algebraMap (ZMod p) (GaloisField p q) c) * s) (by
    simpa [Algebra.smul_def] using W.smul_mem c hsW)

/-- **BG Appendix C, Lemma C.3, Step 2 (intersection core)**: under condition
(A), a norm-one unit that also comes from the prime field is trivial.  This is
the finite-field `U ∩ 𝔽_pˣ = 1` input used in the generator-relation argument. -/
theorem normOneUnits_eq_one_of_mem_primeFieldUnits [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (u : normOneUnits p q) (hu : (u : (GaloisField p q)ˣ) ∈ primeFieldUnits p q) :
    u = 1 := by
  have hx : (u : (GaloisField p q)ˣ) ∈ primeFieldUnits p q ⊓ normOneUnits p q := by
    exact ⟨hu, u.property⟩
  rw [primeFieldUnits_inf_normOneUnits_eq_bot p q hq hA] at hx
  exact Subtype.ext hx

/-- **BG Appendix C, Lemma C.3, Step 2 (prime-line core)**: on a nonzero
prime-field line `𝔽_p s`, if a norm-one unit `u` carries one nonzero prime-field
multiple into a relation with another, then `u = 1`.  In BG notation this is the
finite-field calculation behind `s₁ u s₂ ∈ U` forcing `u = 1` in the nonzero
case. -/
theorem normOneUnits_eq_one_of_primeLine_relation [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) {c d : ZMod p} (hc : c ≠ 0) (hd : d ≠ 0)
    (u : normOneUnits p q)
    (h : (algebraMap (ZMod p) (GaloisField p q) c) * s +
        (((u : (GaloisField p q)ˣ) : GaloisField p q) *
          ((algebraMap (ZMod p) (GaloisField p q) d) * s)) = 0) :
    u = 1 := by
  let F := GaloisField p q
  let emb : ZMod p →+* F := algebraMap (ZMod p) F
  let uval : F := ((u : Fˣ) : F)
  have hfactor : (emb c + uval * emb d) * s = 0 := by
    change (emb c) * s + uval * ((emb d) * s) = 0 at h
    rw [add_mul, mul_assoc]
    exact h
  have hcoef : emb c + uval * emb d = 0 := by
    exact (mul_eq_zero.mp hfactor).resolve_right hs
  have hdF : emb d ≠ 0 := by
    exact (map_ne_zero emb).2 hd
  have hmul : uval * emb d = - emb c := by
    rw [add_comm] at hcoef
    exact eq_neg_of_add_eq_zero_left hcoef
  have huval : uval = - emb c / emb d := by
    calc
      uval = (uval * emb d) / emb d := by rw [mul_div_cancel_right₀ _ hdF]
      _ = - emb c / emb d := by rw [hmul]
  have hbne : -c / d ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hc) hd
  let b : (ZMod p)ˣ := Units.mk0 (-c / d) hbne
  have hbmap : Units.map emb.toMonoidHom b = (u : Fˣ) := by
    apply Units.ext
    change emb (-c / d) = uval
    rw [huval]
    simp [emb]
  have hu_prime : (u : Fˣ) ∈ primeFieldUnits p q := by
    exact ⟨b, hbmap⟩
  exact normOneUnits_eq_one_of_mem_primeFieldUnits p q hq hA u hu_prime

/-- **BG Appendix C, Lemma C.3, Step 2 (prime-line form)**: for a nonzero
prime-field line `𝔽_p s`, the additive relation corresponding to
`s₁ u s₂ ∈ U` has only the two BG alternatives: either both prime-field
coefficients vanish, or `u = 1` and the coefficients sum to zero. -/
theorem generatorRelation_step2_primeLine [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) (c d : ZMod p) (u : normOneUnits p q)
    (h : (algebraMap (ZMod p) (GaloisField p q) c) * s +
        (((u : (GaloisField p q)ˣ) : GaloisField p q) *
          ((algebraMap (ZMod p) (GaloisField p q) d) * s)) = 0) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  let F := GaloisField p q
  let emb : ZMod p →+* F := algebraMap (ZMod p) F
  by_cases hc : c = 0
  · left
    refine ⟨hc, ?_⟩
    subst c
    have hmul : (((u : Fˣ) : F) * (emb d * s)) = 0 := by
      simpa [emb] using h
    have huds : emb d * s = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left (Units.ne_zero (u : Fˣ))
    have hdemb : emb d = 0 := by
      exact (mul_eq_zero.mp huds).resolve_right hs
    by_contra hd
    exact (map_ne_zero emb).2 hd hdemb
  · by_cases hd : d = 0
    · exfalso
      subst d
      have hmul : (emb c) * s = 0 := by
        simpa [emb] using h
      have hcemb : emb c = 0 := by
        exact (mul_eq_zero.mp hmul).resolve_right hs
      exact (map_ne_zero emb).2 hc hcemb
    · right
      have hu1 := normOneUnits_eq_one_of_primeLine_relation p q hq hA hs hc hd u h
      refine ⟨hu1, ?_⟩
      subst hu1
      have hsum_mul : (emb (c + d)) * s = 0 := by
        change emb c * s + ((1 : Fˣ) : F) * (emb d * s) = 0 at h
        simpa [emb, map_add, add_mul] using h
      have hsum_emb : emb (c + d) = 0 := by
        exact (mul_eq_zero.mp hsum_mul).resolve_right hs
      by_contra hsum
      exact (map_ne_zero emb).2 hsum hsum_emb


/-! ### Lemma C.3 Step 4: Frobenius stability of the norm set -/

/-- **BG Appendix C, Lemma C.3, Step 4**: in `𝔽_{p^q}`, the `p`-power
Frobenius fixes the prime-field element `2`. -/
lemma pow_p_natCast_two [Fact p.Prime] :
    (2 : GaloisField p q) ^ p = 2 := by
  simpa [frobenius_def] using
    (map_natCast (frobenius (GaloisField p q) p) 2)

/-- **BG Appendix C, Lemma C.3, Step 4**: the BG norm is compatible with the
`p`-power Frobenius. -/
theorem normN_pow_p [Fact p.Prime] (hq : q ≠ 0) (a : GaloisField p q) :
    normN p q (a ^ p) = (normN p q a) ^ p := by
  rw [normN_eq_algebraMap_norm p q hq, normN_eq_algebraMap_norm p q hq]
  rw [← map_pow]
  rw [← (Algebra.norm (ZMod p) (S := GaloisField p q)).map_pow a p]

/-- **BG Appendix C, Lemma C.3, Step 4**: the `p`-power Frobenius carries
`2 - a` to `2 - a^p`. -/
theorem two_sub_pow_p [Fact p.Prime] (a : GaloisField p q) :
    ((2 : GaloisField p q) - a) ^ p = (2 : GaloisField p q) - a ^ p := by
  have h := map_sub (frobenius (GaloisField p q) p) (2 : GaloisField p q) a
  simpa [frobenius_def, pow_p_natCast_two p q] using h

/-- **BG Appendix C, Lemma C.3, Step 4**: in characteristic `p`, Frobenius
turns a two-term sum into the sum of `p`-th powers. -/
lemma add_pow_p [Fact p.Prime] (a b : GaloisField p q) :
    a ^ p + b ^ p = (a + b) ^ p := by
  have h := map_add (frobenius (GaloisField p q) p) a b
  simpa [frobenius_def] using h.symm

/-- **BG Appendix C, Lemma C.3, Step 4**: the norm set `E` is stable under
the `p`-power Frobenius. -/
theorem normSetE_pow_p [Fact p.Prime] (hq : q ≠ 0) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) :
    a ^ p ∈ normSetE p q := by
  constructor
  · rw [normN_pow_p p q hq, ha.1, one_pow]
  · rw [← two_sub_pow_p p q a, normN_pow_p p q hq, ha.2, one_pow]

/-- **BG Appendix C, Lemma C.3, Step 4**: if `a,b ∈ E` and `a+b=2`, then
their Frobenius images again lie in `E` and still sum to `2`. -/
theorem normSetE_frobenius_pair [Fact p.Prime] (hq : q ≠ 0)
    {a b : GaloisField p q} (ha : a ∈ normSetE p q) (hb : b ∈ normSetE p q)
    (hsum : a + b = 2) :
    a ^ p ∈ normSetE p q ∧ b ^ p ∈ normSetE p q ∧ a ^ p + b ^ p = 2 := by
  refine ⟨normSetE_pow_p p q hq ha, normSetE_pow_p p q hq hb, ?_⟩
  rw [add_pow_p p q, hsum, pow_p_natCast_two p q]

/-- **BG Appendix C, Lemma C.3, Step 4**: under condition (A), a norm-one
unit whose `(p - 1)`-st power is trivial is itself trivial.  This is the
finite-group form of the line `w_i^{p-1}=1`, hence `w_i=1` by (A). -/
theorem normOneUnits_eq_one_of_pow_sub_one_eq_one [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (u : normOneUnits p q) (hu : u ^ (p - 1) = 1) :
    u = 1 := by
  have hcard : Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) :=
    normOneUnits_card p q hq.ne_zero
  have horder_card : orderOf u ∣ (p ^ q - 1) / (p - 1) := by
    simpa [hcard] using orderOf_dvd_natCard u
  have horder_p : orderOf u ∣ p - 1 := orderOf_dvd_of_pow_eq_one hu
  have horder_one : orderOf u = 1 :=
    Nat.eq_one_of_dvd_coprimes hA horder_card horder_p
  exact orderOf_eq_one_iff.mp horder_one

/-- The twisted-inverse map attached to an automorphism `φ`: `x ↦ φ(x⁻¹)`.
This is the abstract form of the last induction in BG Appendix C, Lemma C.3. -/
def twistedInv {α : Type*} [Group α] (φ : MulAut α) (x : α) : α := φ x⁻¹

@[simp] lemma twistedInv_twistedInv {α : Type*} [Group α] (φ : MulAut α)
    (x : α) :
    twistedInv φ (twistedInv φ x) = (φ ^ 2) x := by
  simp [twistedInv, pow_two]

/-- Odd iterates of the twisted-inverse map are a power of `φ` applied to the
inverse. -/
lemma iterate_twistedInv_odd {α : Type*} [Group α] (φ : MulAut α) (n : ℕ)
    (x : α) :
    Nat.iterate (twistedInv φ) (2 * n + 1) x = (φ ^ (2 * n + 1)) x⁻¹ := by
  induction n with
  | zero =>
      simp [twistedInv]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega]
      rw [Function.iterate_add_apply]
      rw [show
          Nat.iterate (twistedInv φ) 2 (Nat.iterate (twistedInv φ) (2 * n + 1) x) =
            twistedInv φ (twistedInv φ (Nat.iterate (twistedInv φ) (2 * n + 1) x)) by
        rfl]
      rw [twistedInv_twistedInv, ih]
      simp [pow_add, pow_two]

/-- **BG Appendix C, Lemma C.3, Step 4 tail**: if a set is closed under the
operation `x ↦ φ(x⁻¹)` and `φ` has odd order dividing `p`, then the set is closed
under inversion.  This packages the final `n = p` induction in BG. -/
theorem inv_mem_of_twistedInv_step {α : Type*} [Group α] (φ : MulAut α) (S : Set α)
    {p : ℕ} (hpodd : Odd p) (hφp : φ ^ p = 1)
    (hstep : ∀ x : α, x ∈ S → twistedInv φ x ∈ S) :
    ∀ x : α, x ∈ S → x⁻¹ ∈ S := by
  intro x hx
  rcases hpodd with ⟨n, hp⟩
  have hiter_mem_all :
      ∀ m (x : α), x ∈ S → Nat.iterate (twistedInv φ) m x ∈ S := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
        intro x hx
        change Nat.iterate (twistedInv φ) m (twistedInv φ x) ∈ S
        exact ih (twistedInv φ x) (hstep x hx)
  have hiter_mem : Nat.iterate (twistedInv φ) p x ∈ S := hiter_mem_all p x hx
  subst p
  rw [iterate_twistedInv_odd φ n x] at hiter_mem
  simpa [hφp] using hiter_mem

/-! ### The Frobenius semidirect product `P ⋊ U` for Lemmas C.2 and C.3 -/

/-- The additive group of `𝔽_{p^q}`, written multiplicatively so it can be the
kernel factor in mathlib's `SemidirectProduct`. -/
abbrev additiveFieldGroup [Fact p.Prime] := Multiplicative (GaloisField p q)

/-- The action of the norm-one subgroup `U` on the additive group `P = 𝔽_{p^q}`:
`u` sends `s` to `u * s`.  This is the action used in the Frobenius group
`H = P ⋊ U` in BG Appendix C, Lemma C.2. -/
noncomputable def normOneMulAction [Fact p.Prime] :
    normOneUnits p q →* MulAut (additiveFieldGroup p q) :=
  (MulAutMultiplicative (GaloisField p q)).symm.toMonoidHom.comp
    ((AddAut.mulLeft :
        (GaloisField p q)ˣ →* Multiplicative (AddAut (GaloisField p q))).comp
      (normOneUnits p q).subtype)

/-- The concrete Frobenius group `H = P ⋊ U` from BG Appendix C, Lemma C.2, with
`P` the additive group of `𝔽_{p^q}` and `U` the norm-one subgroup. -/
abbrev normOneFrobeniusGroup [Fact p.Prime] :=
  additiveFieldGroup p q ⋊[normOneMulAction p q] normOneUnits p q

@[simp] theorem normOneMulAction_apply [Fact p.Prime] (u : normOneUnits p q)
    (s : GaloisField p q) :
    ((normOneMulAction p q u) (Multiplicative.ofAdd s)).toAdd =
      ((u : (GaloisField p q)ˣ) : GaloisField p q) * s := by
  rfl

/-- In the concrete Frobenius group `H = P ⋊ U`, conjugating an additive-kernel
point `s` by `u ∈ U` is multiplication by `u` on the finite field.  This is the
formal `u s u⁻¹ = u*s` bridge used to turn BG's class sums into the finite-field
pair condition. -/
theorem normOneFrobenius_conj_inl [Fact p.Prime] (u : normOneUnits p q)
    (s : GaloisField p q) :
    (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
        SemidirectProduct.inl (Multiplicative.ofAdd s) * SemidirectProduct.inr u⁻¹ =
      SemidirectProduct.inl
        (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  rw [← SemidirectProduct.inl_aut, SemidirectProduct.inl_inj]
  exact Multiplicative.toAdd.injective (normOneMulAction_apply p q u s)

/-- **BG Appendix C, Lemma C.3, Step 1 semidirect form**: fixing a nonzero
prime-field line `𝔽_p s`, every element of the concrete `P ⋊ U` can be written
as `u s₁ v` with `u, v ∈ U` and `s₁ ∈ 𝔽_p s`. -/
theorem normOneFrobenius_exists_inr_primeLine_inr [Fact p.Prime]
    (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) (g : normOneFrobeniusGroup p q) :
    ∃ c : ZMod p, ∃ u v : normOneUnits p q,
      g = (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
        SemidirectProduct.inl
          (Multiplicative.ofAdd ((algebraMap (ZMod p) (GaloisField p q) c) * s)) *
        SemidirectProduct.inr v := by
  obtain ⟨c, u, hx⟩ :=
    exists_normOne_mul_primeLine_eq p q hq hA (s := s) (x := g.left.toAdd) hs
  refine ⟨c, u, u⁻¹ * g.right, ?_⟩
  let y : GaloisField p q := (algebraMap (ZMod p) (GaloisField p q) c) * s
  have hleft :
      (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) =
        (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd y) * SemidirectProduct.inr u⁻¹ := by
    rw [normOneFrobenius_conj_inl p q u y]
    simp [y, ofAdd_toAdd, ← hx]
  calc
    g = (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) *
          SemidirectProduct.inr g.right := (SemidirectProduct.inl_left_mul_inr_right g).symm
    _ = ((SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd y) * SemidirectProduct.inr u⁻¹) *
          SemidirectProduct.inr g.right := by rw [hleft]
    _ = (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd y) *
          SemidirectProduct.inr (u⁻¹ * g.right) := by
      simp [mul_assoc]

/-- The BG pair condition `u*s + v*s = 2*s`, already used in
`normOnePairSetAt`, is exactly the assertion that the corresponding two elements
of the additive kernel `P ≤ H = P ⋊ U` multiply to `2*s`.  This is the concrete
entry point for the q≥5 class-sum structure constant calculation. -/
theorem mem_normOnePairSetAt_iff_inl_mul_inl [Fact p.Prime] (s : GaloisField p q)
    (u v : normOneUnits p q) :
    (u, v) ∈ normOnePairSetAt p q s ↔
      (SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q) *
        SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) =
        SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) := by
  dsimp [normOnePairSetAt]
  rw [← map_mul (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q),
    SemidirectProduct.inl_inj]
  exact Iff.rfl

/-- **BG Appendix C, Lemma C.3, Step 2 semidirect form**: on a nonzero
prime-field line `𝔽_p s`, if `s₁ u s₂` lies in the complement `U` inside the
concrete `P ⋊ U`, then either both prime-line factors are trivial or `u=1` and
the two prime-line factors multiply to the identity. -/
theorem normOneFrobenius_generatorRelation_step2_primeLine [Fact p.Prime]
    (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {s : GaloisField p q} (hs : s ≠ 0) {c d : ZMod p} (u : normOneUnits p q)
    (hmem :
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd ((algebraMap (ZMod p) (GaloisField p q) c) * s)) :
            normOneFrobeniusGroup p q) *
        SemidirectProduct.inr u *
        SemidirectProduct.inl
          (Multiplicative.ofAdd ((algebraMap (ZMod p) (GaloisField p q) d) * s))) ∈
      (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  let x : GaloisField p q := (algebraMap (ZMod p) (GaloisField p q) c) * s
  let y : GaloisField p q := (algebraMap (ZMod p) (GaloisField p q) d) * s
  obtain ⟨v, hv⟩ := hmem
  have hleft : x + (((u : (GaloisField p q)ˣ) : GaloisField p q) * y) = 0 := by
    have hcongr := congrArg (fun g : normOneFrobeniusGroup p q => g.left.toAdd) hv
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, map_one, one_mul, mul_one, toAdd_mul, toAdd_ofAdd,
      normOneMulAction_apply] at hcongr
    simpa [x, y, add_comm] using hcongr.symm
  exact generatorRelation_step2_primeLine p q hq hA hs (c := c) (d := d) u
    (by simpa [x, y] using hleft)

/-- **BG Appendix C, Lemma C.3, Step 4 final paragraph, concrete form**:
if the first `k = 3` equation of `(C.5)` has middle prime-line factor `s^{-1}`,
then reading the additive coordinate in `P ⋊ U` gives the generator relation
`N(2*w-1)=1` for the middle complement element `w`. -/
theorem normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition
    [Fact p.Prime] (hq : q ≠ 0) (w u₁ v₁ : normOneUnits p q)
    (hdec :
      (SemidirectProduct.inl
          (Multiplicative.ofAdd (1 : GaloisField p q)) : normOneFrobeniusGroup p q) *
          SemidirectProduct.inr w *
        SemidirectProduct.inl
          (Multiplicative.ofAdd (-(2 : GaloisField p q))) =
      (SemidirectProduct.inr u₁ : normOneFrobeniusGroup p q) *
        SemidirectProduct.inl
          (Multiplicative.ofAdd (-(1 : GaloisField p q))) *
          SemidirectProduct.inr v₁) :
    normN p q
      ((2 : GaloisField p q) *
          (((w : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) - 1) = 1 := by
  let F := GaloisField p q
  let H := normOneFrobeniusGroup p q
  let wF : F := (((w : normOneUnits p q) : (GaloisField p q)ˣ) : F)
  let u₁F : F := (((u₁ : normOneUnits p q) : (GaloisField p q)ˣ) : F)
  have hleft := congrArg (fun g : H => g.left.toAdd) hdec
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul, mul_one,
    toAdd_mul, toAdd_ofAdd, normOneMulAction_apply] at hleft
  have hleft' : (1 : F) - 2 * wF = -u₁F := by
    simpa [F, wF, u₁F, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hleft
  have hu₁F : u₁F = (2 : F) * wF - 1 := by
    calc
      u₁F = -(-u₁F) := by ring
      _ = -((1 : F) - 2 * wF) := by rw [← hleft']
      _ = (2 : F) * wF - 1 := by ring
  rw [show ((2 : GaloisField p q) *
        (((w : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) - 1) =
        (((u₁ : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) by
      simpa [F, wF, u₁F] using hu₁F.symm]
  exact (mem_normOneUnits_iff_normN p q hq (u₁ : (GaloisField p q)ˣ)).mp u₁.property

/-- The additive subgroup `W ≤ P` inside the concrete Frobenius group `P ⋊ U`. -/
noncomputable def normOneFrobeniusSubspaceKernel [Fact p.Prime]
    (W : Submodule (ZMod p) (GaloisField p q)) :
    Subgroup (normOneFrobeniusGroup p q) :=
  W.toAddSubgroup.toSubgroup.map
    (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q)

/-- Membership in the embedded additive subspace is exactly membership in `W`. -/
@[simp] theorem mem_normOneFrobeniusSubspaceKernel_inl [Fact p.Prime]
    (W : Submodule (ZMod p) (GaloisField p q)) (s : GaloisField p q) :
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈
      normOneFrobeniusSubspaceKernel p q W ↔ s ∈ W := by
  unfold normOneFrobeniusSubspaceKernel
  constructor
  · intro h
    rcases h with ⟨x, hxW, hx⟩
    have hx' : x = Multiplicative.ofAdd s := SemidirectProduct.inl_injective hx
    simpa [hx'] using hxW
  · intro hs
    exact ⟨Multiplicative.ofAdd s, by simpa using hs, rfl⟩

/-- The subgroup generated by an additive subspace `W ≤ P` and the norm-one
complement `U` inside the concrete Frobenius group `P ⋊ U`. -/
noncomputable def normOneFrobeniusSubspaceGroup [Fact p.Prime]
    (W : Submodule (ZMod p) (GaloisField p q)) :
    Subgroup (normOneFrobeniusGroup p q) :=
  normOneFrobeniusSubspaceKernel p q W ⊔
    (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range

/-- **BG Appendix C, Lemma C.3, Step 3 semidirect input**: under condition (A),
if a nonzero additive subspace `W ≤ P` is invariant under `U`, then `W` together
with `U` generates the whole concrete Frobenius group `P ⋊ U`.  This packages
the irreducibility step used when `(P ∩ X)U` is larger than `U`. -/
theorem normOneFrobeniusSubspaceGroup_eq_top_of_ne_bot [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (W : Submodule (ZMod p) (GaloisField p q))
    (hU : ∀ u : normOneUnits p q, ∀ x : GaloisField p q, x ∈ W →
      (((u : (GaloisField p q)ˣ) : GaloisField p q) * x) ∈ W)
    (hne : W ≠ ⊥) :
    normOneFrobeniusSubspaceGroup p q W = ⊤ := by
  classical
  have hW := normOneUnits_invariant_submodule_eq_top_of_ne_bot p q hq hA W hU hne
  apply le_antisymm le_top
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  unfold normOneFrobeniusSubspaceGroup
  refine Subgroup.mul_mem_sup ?_ ?_
  · unfold normOneFrobeniusSubspaceKernel
    refine ⟨x.left, ?_, rfl⟩
    rw [hW]
    simp
  · exact ⟨x.right, rfl⟩

/-- Additive-kernel preimage of a subgroup `X ≤ P ⋊ U`. -/
noncomputable def normOneFrobeniusKernelPreimageAddSubgroup [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q)) : AddSubgroup (GaloisField p q) where
  carrier := {s | (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X}
  zero_mem' := by
    simp
  add_mem' := by
    intro a b ha hb
    have hmul := X.mul_mem ha hb
    simpa [← map_mul, ofAdd_add] using hmul
  neg_mem' := by
    intro a ha
    have hinv := X.inv_mem ha
    simpa using hinv

/-- The additive-kernel preimage of `X ≤ P ⋊ U`, viewed as an `𝔽_p`-subspace. -/
noncomputable def normOneFrobeniusKernelPreimageSubmodule [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q)) : Submodule (ZMod p) (GaloisField p q) :=
  AddSubgroup.toZModSubmodule (n := p) (normOneFrobeniusKernelPreimageAddSubgroup p q X)

/-- Membership in the kernel-preimage subspace is membership of the corresponding
embedded additive element in `X`. -/
@[simp] theorem mem_normOneFrobeniusKernelPreimageSubmodule [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q)) (s : GaloisField p q) :
    s ∈ normOneFrobeniusKernelPreimageSubmodule p q X ↔
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X := by
  rfl

/-- If `X` contains the norm-one complement `U`, then its additive-kernel preimage
is stable under the `U` action. -/
theorem normOneFrobeniusKernelPreimageSubmodule_invariant_of_inr_range_le [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hUle : (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range ≤ X) :
    ∀ u : normOneUnits p q, ∀ x : GaloisField p q,
      x ∈ normOneFrobeniusKernelPreimageSubmodule p q X →
        (((u : (GaloisField p q)ˣ) : GaloisField p q) * x) ∈
          normOneFrobeniusKernelPreimageSubmodule p q X := by
  intro u x hx
  have hu : (SemidirectProduct.inr u : normOneFrobeniusGroup p q) ∈ X := hUle ⟨u, rfl⟩
  have hxX :
      (SemidirectProduct.inl (Multiplicative.ofAdd x) : normOneFrobeniusGroup p q) ∈ X := by
    simpa using hx
  have huinv : (SemidirectProduct.inr u⁻¹ : normOneFrobeniusGroup p q) ∈ X := by
    simpa using X.inv_mem hu
  have hconj :
      (SemidirectProduct.inr u : normOneFrobeniusGroup p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd x) * SemidirectProduct.inr u⁻¹ ∈ X := by
    exact X.mul_mem (X.mul_mem hu hxX) huinv
  rw [normOneFrobenius_conj_inl p q u x] at hconj
  simpa using hconj

/-- A subgroup `X ≤ P ⋊ U` with a nontrivial additive-kernel element has nonzero
additive-kernel preimage. -/
theorem normOneFrobeniusKernelPreimageSubmodule_ne_bot_of_exists_inl [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hker : ∃ s : GaloisField p q, s ≠ 0 ∧
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X) :
    normOneFrobeniusKernelPreimageSubmodule p q X ≠ ⊥ := by
  rcases hker with ⟨s, hs0, hsX⟩
  intro hbot
  have hsW : s ∈ normOneFrobeniusKernelPreimageSubmodule p q X := hsX
  rw [hbot] at hsW
  exact hs0 hsW

/-- **BG Appendix C, Lemma C.3, Step 3 subgroup form**: in the concrete
`P ⋊ U`, any subgroup containing the complement `U` and one nontrivial
additive-kernel element is all of `P ⋊ U`.  This is the formal version of the
irreducibility step `X ≠ U ⇒ X = PU`. -/
theorem normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_exists_inl
    [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hUle : (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range ≤ X)
    (hker : ∃ s : GaloisField p q, s ≠ 0 ∧
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X) :
    X = ⊤ := by
  classical
  let W := normOneFrobeniusKernelPreimageSubmodule p q X
  have hU : ∀ u : normOneUnits p q, ∀ x : GaloisField p q, x ∈ W →
      (((u : (GaloisField p q)ˣ) : GaloisField p q) * x) ∈ W := by
    simpa [W] using normOneFrobeniusKernelPreimageSubmodule_invariant_of_inr_range_le p q X hUle
  have hne : W ≠ ⊥ := by
    simpa [W] using normOneFrobeniusKernelPreimageSubmodule_ne_bot_of_exists_inl p q X hker
  have hWtop := normOneUnits_invariant_submodule_eq_top_of_ne_bot p q hq hA W hU hne
  apply le_antisymm le_top
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  have hleft : (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) ∈ X := by
    have hgW : g.left.toAdd ∈ W := by
      rw [hWtop]
      simp
    simpa [W, ofAdd_toAdd] using hgW
  have hright : (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q) ∈ X :=
    hUle ⟨g.right, rfl⟩
  exact X.mul_mem hleft hright

/-- **BG Appendix C, Lemma C.3, Step 3 subgroup dichotomy**: in the concrete
`P ⋊ U`, any subgroup containing the complement `U` is either exactly `U` or all
of `P ⋊ U`.  This is the direct semidirect-product form of BG's `X ≠ U ⇒ X=PU`
step. -/
theorem normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
    [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (X : Subgroup (normOneFrobeniusGroup p q))
    (hUle : (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range ≤ X)
    (hne : X ≠
      (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range) :
    X = ⊤ := by
  classical
  let U : Subgroup (normOneFrobeniusGroup p q) :=
    (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range
  have hnot_le : ¬ X ≤ U := by
    intro hXle
    exact hne (le_antisymm hXle hUle)
  change ¬ ∀ g, g ∈ X → g ∈ U at hnot_le
  rw [not_forall] at hnot_le
  obtain ⟨g, hg⟩ := hnot_le
  obtain ⟨hgX, hgU⟩ := Classical.not_imp.mp hg
  have hgleft_ne : g.left.toAdd ≠ 0 := by
    intro hzero
    apply hgU
    refine ⟨g.right, ?_⟩
    rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [← ofAdd_toAdd g.left, hzero]
    simp
  have hright : (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q) ∈ X :=
    hUle ⟨g.right, rfl⟩
  have hleftX : (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q) ∈ X := by
    have hprod :
        g * (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q)⁻¹ ∈ X :=
      X.mul_mem hgX (X.inv_mem hright)
    have hprod_eq :
        g * (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q)⁻¹ =
          SemidirectProduct.inl g.left := by
      simpa [SemidirectProduct.inl_left_mul_inr_right g] using
        (mul_inv_cancel_right
          (SemidirectProduct.inl g.left : normOneFrobeniusGroup p q)
          (SemidirectProduct.inr g.right : normOneFrobeniusGroup p q))
    rwa [hprod_eq] at hprod
  refine normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_exists_inl
    p q hq hA X hUle ?_
  exact ⟨g.left.toAdd, hgleft_ne, by simpa [ofAdd_toAdd] using hleftX⟩

/-! ## Lemma C.1 machinery: the Möbius iterate and the sequence `d_k` -/

/-- `N(0) = 0` (the `i = 0` factor `0^{p^0} = 0` makes the product vanish). -/
lemma normN_zero [Fact p.Prime] (hq : 0 < q) :
    normN p q (0 : GaloisField p q) = 0 := by
  simp only [normN]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hq) (by simp)

/-- An element of `E` is nonzero (its norm is `1 ≠ 0`). -/
lemma ne_zero_of_mem_normSetE [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : a ≠ 0 := by
  intro h
  have := ha.1
  rw [h, normN_zero p q hq] at this
  exact zero_ne_one this

/-- For `a ∈ E`, `2 - a ≠ 0` (its norm is `1 ≠ 0`), so `(2-a)⁻¹` is genuine. -/
lemma two_sub_ne_zero_of_mem_normSetE [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : (2 : GaloisField p q) - a ≠ 0 := by
  intro h
  have := ha.2
  rw [h, normN_zero p q hq] at this
  exact zero_ne_one this

/-- Coerce an element of `E` to the corresponding norm-one unit. -/
noncomputable def normOneUnitOfMemNormSetE [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) : normOneUnits p q :=
  let u : (GaloisField p q)ˣ := Units.mk0 a (ne_zero_of_mem_normSetE p q hq ha)
  ⟨u, (mem_normOneUnits_iff_normN p q hq.ne' u).mpr ha.1⟩

@[simp] theorem normOneUnitOfMemNormSetE_coe [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    (((normOneUnitOfMemNormSetE p q hq ha : normOneUnits p q) :
        (GaloisField p q)ˣ) : GaloisField p q) = a := by
  rfl

/-- The pair `(a, 2-a)` attached to `a ∈ E`, viewed as a pair of norm-one
units. -/
noncomputable def normOnePairOfMemNormSetE [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    normOneUnits p q × normOneUnits p q :=
  (normOneUnitOfMemNormSetE p q hq ha,
    normOneUnitOfMemNormSetE p q hq (two_sub_mem_normSetE p q ha))

@[simp] theorem normOnePairOfMemNormSetE_fst_coe [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    ((((normOnePairOfMemNormSetE p q hq ha).1 : normOneUnits p q) :
        (GaloisField p q)ˣ) : GaloisField p q) = a := by
  rfl

@[simp] theorem normOnePairOfMemNormSetE_snd_coe [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    ((((normOnePairOfMemNormSetE p q hq ha).2 : normOneUnits p q) :
        (GaloisField p q)ˣ) : GaloisField p q) = (2 : GaloisField p q) - a := by
  rfl

/-- The pair attached to `a ∈ E` lies in the BG pair set `u + v = 2`. -/
theorem normOnePairOfMemNormSetE_mem_normOnePairSet [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    normOnePairOfMemNormSetE p q hq ha ∈ normOnePairSet p q := by
  dsimp [normOnePairOfMemNormSetE, normOnePairSet]
  change (a + ((2 : GaloisField p q) - a)) = 2
  ring

/-- The pair attached to `a ∈ E` also lies in the translated BG pair set
`u*s + v*s = 2*s` for every nonzero `s`. -/
theorem normOnePairOfMemNormSetE_mem_normOnePairSetAt [Fact p.Prime] (hq : 0 < q)
    {a s : GaloisField p q} (ha : a ∈ normSetE p q) (hs : s ≠ 0) :
    normOnePairOfMemNormSetE p q hq ha ∈ normOnePairSetAt p q s := by
  rw [normOnePairSetAt_eq_normOnePairSet_of_ne_zero p q hs]
  exact normOnePairOfMemNormSetE_mem_normOnePairSet p q hq ha

/-- The product norm sends inverses to inverses. -/
lemma normN_inv [Fact p.Prime] (a : GaloisField p q) :
    normN p q a⁻¹ = (normN p q a)⁻¹ := by
  simp [normN, inv_pow, Finset.prod_inv_distrib]

/-- **BG Appendix C, Lemma C.3, Step 4 field-step form**: the
one-step output over field elements.  This matches the line in BG that obtains
`(a⁻¹)^{t^3} ∈ E` for every `a ∈ E`, before coercing nonzero elements of `E` to
units for the final odd-iterate argument. -/
def normSetETwistedFieldStep [Fact p.Prime] (hq : 0 < q)
    (φ : MulAut (GaloisField p q)ˣ) : Prop :=
  ∀ a : GaloisField p q, ∀ ha : a ∈ normSetE p q,
    ((twistedInv φ (Units.mk0 a (ne_zero_of_mem_normSetE p q hq ha)) :
        (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q

/-- The field-element one-step output implies the unit one-step output used by
`inv_mem_of_twistedInv_step`. -/
theorem twisted_unit_step_of_twisted_field_step [Fact p.Prime] (hq : 0 < q)
    (φ : MulAut (GaloisField p q)ˣ)
    (hstep : normSetETwistedFieldStep p q hq φ) :
    ∀ u : (GaloisField p q)ˣ,
      ((u : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q →
        ((twistedInv φ u : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q := by
  intro u hu
  have hmk : Units.mk0 ((u : (GaloisField p q)ˣ) : GaloisField p q)
      (ne_zero_of_mem_normSetE p q hq hu) = u := by
    ext
    rfl
  simpa [hmk] using hstep ((u : (GaloisField p q)ˣ) : GaloisField p q) hu

/-- **BG Appendix C, Lemma C.3, Step 4 norm-one form**: the one-step output
only needs an automorphism of the norm-one unit group, since every element of
`E` has norm `1`. -/
def normSetETwistedNormOneStep [Fact p.Prime] (φ : MulAut (normOneUnits p q)) : Prop :=
  ∀ u : normOneUnits p q,
    (((u : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q →
      (((twistedInv φ u : normOneUnits p q) : (GaloisField p q)ˣ) :
          GaloisField p q) ∈ normSetE p q

/-- **BG Appendix C, Lemma C.3, Step 4 tail for the norm-one group**: the
odd-iterate argument works inside `U`, avoiding an unnecessary extension of the
`t`-action to the full unit group. -/
theorem normSetE_eq_inv_of_twisted_normOne_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (normOneUnits p q)) (hφp : φ ^ p = 1)
    (hstep : normSetETwistedNormOneStep p q φ) :
    normSetE p q = (normSetE p q)⁻¹ := by
  classical
  let EUnits : Set (normOneUnits p q) :=
    {u | (((u : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) ∈
      normSetE p q}
  have hinv_units : ∀ u : normOneUnits p q, u ∈ EUnits → u⁻¹ ∈ EUnits := by
    exact inv_mem_of_twistedInv_step φ EUnits hpodd hφp hstep
  ext a
  constructor
  · intro ha
    rw [Set.mem_inv]
    let u0 : (GaloisField p q)ˣ := Units.mk0 a (ne_zero_of_mem_normSetE p q hq ha)
    have hu0 : u0 ∈ normOneUnits p q := by
      rw [mem_normOneUnits_iff_normN p q hq.ne' u0]
      simpa [u0] using ha.1
    let u : normOneUnits p q := ⟨u0, hu0⟩
    have hu : u ∈ EUnits := by
      simpa [EUnits, u, u0] using ha
    have hui := hinv_units u hu
    simpa [EUnits, u, u0] using hui
  · intro ha
    rw [Set.mem_inv] at ha
    let u0 : (GaloisField p q)ˣ := Units.mk0 a⁻¹ (ne_zero_of_mem_normSetE p q hq ha)
    have hu0 : u0 ∈ normOneUnits p q := by
      rw [mem_normOneUnits_iff_normN p q hq.ne' u0]
      simpa [u0] using ha.1
    let u : normOneUnits p q := ⟨u0, hu0⟩
    have hu : u ∈ EUnits := by
      simpa [EUnits, u, u0] using ha
    have hui := hinv_units u hu
    simpa [EUnits, u, u0] using hui

/-- **BG Appendix C, Lemma C.3, Step 4 tail for the norm set**: if an
automorphism of the unit group has odd `p`-th power equal to the identity and
sends every `u ∈ E` to `φ(u⁻¹) ∈ E`, then the norm set is inverse-closed.
This is the finite-field target of BG's final induction after the generator
relations have produced the one-step twisted inverse. -/
theorem normSetE_eq_inv_of_twisted_unit_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (GaloisField p q)ˣ) (hφp : φ ^ p = 1)
    (hstep : ∀ u : (GaloisField p q)ˣ,
      ((u : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q →
        ((twistedInv φ u : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q) :
    normSetE p q = (normSetE p q)⁻¹ := by
  classical
  let EUnits : Set (GaloisField p q)ˣ :=
    {u | ((u : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q}
  have hinv_units : ∀ u : (GaloisField p q)ˣ, u ∈ EUnits → u⁻¹ ∈ EUnits := by
    exact inv_mem_of_twistedInv_step φ EUnits hpodd hφp hstep
  ext a
  constructor
  · intro ha
    rw [Set.mem_inv]
    let u : (GaloisField p q)ˣ := Units.mk0 a (ne_zero_of_mem_normSetE p q hq ha)
    have hu : u ∈ EUnits := by simpa [EUnits, u] using ha
    have hui := hinv_units u hu
    simpa [EUnits, u] using hui
  · intro ha
    rw [Set.mem_inv] at ha
    let u : (GaloisField p q)ˣ := Units.mk0 a⁻¹ (ne_zero_of_mem_normSetE p q hq ha)
    have hu : u ∈ EUnits := by simpa [EUnits, u] using ha
    have hui := hinv_units u hu
    simpa [EUnits, u] using hui

/-- **BG Appendix C, Lemma C.3, Step 4 field-step adapter**: the
field-element one-step twisted inverse output implies inverse-closure of `E`. -/
theorem normSetE_eq_inv_of_twisted_field_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (GaloisField p q)ˣ) (hφp : φ ^ p = 1)
    (hstep : normSetETwistedFieldStep p q hq φ) :
    normSetE p q = (normSetE p q)⁻¹ :=
  normSetE_eq_inv_of_twisted_unit_step p q hq hpodd φ hφp
    (twisted_unit_step_of_twisted_field_step p q hq φ hstep)

/-- Algebraic tail of **BG Appendix C, Lemma C.3**: once the generator-relation
calculation has produced `N(2 * a - 1) = 1`, an element `a ∈ E` has inverse in
`E`.  Indeed `2 - a⁻¹ = a⁻¹ * (2 * a - 1)`. -/
lemma inv_mem_normSetE_of_normN_two_mul_sub_one [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q)
    (hrel : normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    a⁻¹ ∈ normSetE p q := by
  have ha0 : a ≠ 0 := ne_zero_of_mem_normSetE p q hq ha
  refine ⟨?_, ?_⟩
  · rw [normN_inv, ha.1, inv_one]
  · have hcalc :
        (2 : GaloisField p q) - a⁻¹ = a⁻¹ * ((2 : GaloisField p q) * a - 1) := by
      field_simp [ha0]
    rw [hcalc, normN_mul, normN_inv, ha.1, inv_one, one_mul, hrel]

/-- A C.3 generator-relation output in the form `N(2 * a - 1) = 1` for every
`a ∈ E` implies the usual inversion closure `E = E⁻¹`. -/
theorem normSetE_eq_inv_of_forall_normN_two_mul_sub_one [Fact p.Prime] (hq : 0 < q)
    (hrel : ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    normSetE p q = (normSetE p q)⁻¹ := by
  ext a
  constructor
  · intro ha
    rw [Set.mem_inv]
    exact inv_mem_normSetE_of_normN_two_mul_sub_one p q hq ha (hrel a ha)
  · intro ha
    rw [Set.mem_inv] at ha
    simpa using inv_mem_normSetE_of_normN_two_mul_sub_one p q hq ha (hrel a⁻¹ ha)

/-- Conversely, inverse-closure of `E` gives the generator-relation norm
identity used by the Peterfalvi Section 16 interface.  This is the algebraic
tail `2 * a - 1 = a * (2 - a⁻¹)`. -/
theorem forall_normN_two_mul_sub_one_of_normSetE_eq_inv [Fact p.Prime] (hq : 0 < q)
    (hEinv : normSetE p q = (normSetE p q)⁻¹) :
    ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1 := by
  intro a ha
  have ha0 : a ≠ 0 := ne_zero_of_mem_normSetE p q hq ha
  have hainv : a⁻¹ ∈ normSetE p q := by
    have ha_invset : a ∈ (normSetE p q)⁻¹ := by
      rw [← hEinv]
      exact ha
    rwa [Set.mem_inv] at ha_invset
  have hcalc :
      (2 : GaloisField p q) * a - 1 = a * ((2 : GaloisField p q) - a⁻¹) := by
    field_simp [ha0]
  rw [hcalc, normN_mul, ha.1, hainv.2, one_mul]

/-- **BG Appendix C, Lemma C.3, Step 4 field-step adapter**: the
field-element one-step twisted inverse output implies the concrete norm identity
`N(2 * a - 1) = 1` for every `a ∈ E`. -/
theorem forall_normN_two_mul_sub_one_of_twisted_field_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (GaloisField p q)ˣ) (hφp : φ ^ p = 1)
    (hstep : normSetETwistedFieldStep p q hq φ) :
    ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1 :=
  forall_normN_two_mul_sub_one_of_normSetE_eq_inv p q hq
    (normSetE_eq_inv_of_twisted_field_step p q hq hpodd φ hφp hstep)

/-- **BG Appendix C, Lemma C.3, Step 4 adapter**: the one-step twisted inverse
output produced by the generator-relation calculation implies the concrete
norm identity `N(2 * a - 1) = 1` for every `a ∈ E`. -/
theorem forall_normN_two_mul_sub_one_of_twisted_unit_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (GaloisField p q)ˣ) (hφp : φ ^ p = 1)
    (hstep : ∀ u : (GaloisField p q)ˣ,
      ((u : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q →
        ((twistedInv φ u : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q) :
    ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1 := by
  exact forall_normN_two_mul_sub_one_of_normSetE_eq_inv p q hq
    (normSetE_eq_inv_of_twisted_unit_step p q hq hpodd φ hφp hstep)

/-- The norm-one one-step output implies the concrete norm relation used by BG's
final contradiction. -/
theorem forall_normN_two_mul_sub_one_of_twisted_normOne_step [Fact p.Prime] (hq : 0 < q)
    (hpodd : Odd p) (φ : MulAut (normOneUnits p q)) (hφp : φ ^ p = 1)
    (hstep : normSetETwistedNormOneStep p q φ) :
    ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1 := by
  exact forall_normN_two_mul_sub_one_of_normSetE_eq_inv p q hq
    (normSetE_eq_inv_of_twisted_normOne_step p q hq hpodd φ hφp hstep)

/-- **BG Appendix C, Lemma C.3, note (`p = 3`)**: in characteristic three the
generator-relation argument is unnecessary.  Since `2 * a - 1 = 2 - a`, every
`a ∈ E` already satisfies the relation needed to put `a⁻¹` back in `E`. -/
theorem normSetE_eq_inv_of_p_eq_three [Fact (Nat.Prime 3)] (hq : 0 < q) :
    normSetE 3 q = (normSetE 3 q)⁻¹ := by
  apply normSetE_eq_inv_of_forall_normN_two_mul_sub_one (p := 3) (q := q) hq
  intro a ha
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hthree : (3 : GaloisField 3 q) = 0 := by
    change ((3 : ℕ) : GaloisField 3 q) = 0
    rw [CharP.cast_eq_zero_iff (GaloisField 3 q) 3]
  have hcalc : ((2 : GaloisField 3 q) * a - 1) = 2 - a := by
    linear_combination (a - 1) * hthree
  simpa [hcalc] using ha.2

/-- BG Appendix C, Lemma C.2 structure-constant bridge: the norm set `E` is in
bijection with pairs `(u, v) ∈ U × U` satisfying `u + v = 2`.  This is the
finite-field counting identity used before the `q ≥ 5` character calculation. -/
theorem normOnePairSet_ncard_eq_normSetE_ncard [Fact p.Prime] (hq : q ≠ 0) :
    (normOnePairSet p q).ncard = (normSetE p q).ncard := by
  classical
  let F := GaloisField p q
  refine Set.ncard_congr
    (fun uv _ => (((uv.1 : normOneUnits p q) : Fˣ) : F)) ?maps_to ?inj ?surj
  · rintro ⟨u, v⟩ huv
    have hu : normN p q ((u : Fˣ) : F) = 1 :=
      (mem_normOneUnits_iff_normN p q hq (u : Fˣ)).mp u.property
    have hv : normN p q ((v : Fˣ) : F) = 1 :=
      (mem_normOneUnits_iff_normN p q hq (v : Fˣ)).mp v.property
    refine ⟨hu, ?_⟩
    have hvval : (2 : F) - ((u : Fˣ) : F) = ((v : Fˣ) : F) := by
      rw [← huv]
      ring
    rw [hvval]
    exact hv
  · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h₁ h₂ hu
    change ((u₁ : Fˣ) : F) = ((u₂ : Fˣ) : F) at hu
    have hv : ((v₁ : Fˣ) : F) = ((v₂ : Fˣ) : F) := by
      calc
        ((v₁ : Fˣ) : F) = (2 : F) - ((u₁ : Fˣ) : F) := by
          rw [← h₁]
          ring
        _ = (2 : F) - ((u₂ : Fˣ) : F) := by rw [hu]
        _ = ((v₂ : Fˣ) : F) := by
          rw [← h₂]
          ring
    exact Prod.ext (Subtype.ext (Units.ext hu)) (Subtype.ext (Units.ext hv))
  · intro a ha
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let u : Fˣ := Units.mk0 a (ne_zero_of_mem_normSetE p q hqpos ha)
    let v : Fˣ := Units.mk0 (2 - a) (two_sub_ne_zero_of_mem_normSetE p q hqpos ha)
    have hu : u ∈ normOneUnits p q :=
      (mem_normOneUnits_iff_normN p q hq u).mpr ha.1
    have hv : v ∈ normOneUnits p q :=
      (mem_normOneUnits_iff_normN p q hq v).mpr ha.2
    refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_, ?_⟩
    · change (a + (2 - a) : F) = 2
      ring
    · rfl

/-- BG Appendix C, Lemma C.2 structure-constant bridge in the form used in the
class-sum calculation: for any nonzero `s`, the number of norm-one pairs with
`u * s + v * s = 2 * s` is exactly `|E|`. -/
theorem normOnePairSetAt_ncard_eq_normSetE_ncard [Fact p.Prime] (hq : q ≠ 0)
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOnePairSetAt p q s).ncard = (normSetE p q).ncard := by
  rw [normOnePairSetAt_eq_normOnePairSet_of_ne_zero p q hs,
    normOnePairSet_ncard_eq_normSetE_ncard p q hq]

/-- The sequence `d_k := (k+1) - k·a = (1-a)·k + 1` of BG Lemma C.1. -/
noncomputable def dSeq [Fact p.Prime] (a : GaloisField p q) (k : ℕ) : GaloisField p q :=
  (k : GaloisField p q) + 1 - (k : GaloisField p q) * a

@[simp] lemma dSeq_zero [Fact p.Prime] (a : GaloisField p q) : dSeq p q a 0 = 1 := by
  simp [dSeq]

lemma dSeq_one [Fact p.Prime] (a : GaloisField p q) : dSeq p q a 1 = 2 - a := by
  simp only [dSeq, Nat.cast_one, one_mul]; ring

/-- The three-term recurrence `d_{k+2} = 2·d_{k+1} - d_k`. -/
lemma dSeq_recurrence [Fact p.Prime] (a : GaloisField p q) (k : ℕ) :
    dSeq p q a (k + 2) = 2 * dSeq p q a (k + 1) - dSeq p q a k := by
  simp only [dSeq]
  push_cast
  ring

/-- The Möbius iterate `a₀ = a`, `a_{k+1} = (2 - aₖ)⁻¹` of BG Lemma C.1. -/
noncomputable def tauIter [Fact p.Prime] (a : GaloisField p q) (k : ℕ) : GaloisField p q :=
  Nat.rec a (fun _ prev => (2 - prev)⁻¹) k

@[simp] lemma tauIter_zero [Fact p.Prime] (a : GaloisField p q) : tauIter p q a 0 = a := rfl

lemma tauIter_succ [Fact p.Prime] (a : GaloisField p q) (k : ℕ) :
    tauIter p q a (k + 1) = (2 - tauIter p q a k)⁻¹ := rfl

/-- Every iterate `aₖ` lies in `E` (using `E = E⁻¹`). -/
lemma tauIter_mem [Fact p.Prime] {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, tauIter p q a k ∈ normSetE p q := by
  intro k
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [tauIter_succ]
    have h2 : (2 - tauIter p q a k) ∈ normSetE p q := two_sub_mem_normSetE p q ih
    rw [hEinv] at h2
    rwa [Set.mem_inv] at h2

/-- Closed form of the iterate: `a_{k+1} = d_k / d_{k+1}`, with `d_{k+1} ≠ 0`. -/
lemma tauIter_eq_dSeq_div [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, dSeq p q a (k + 1) ≠ 0 ∧
      tauIter p q a (k + 1) = dSeq p q a k / dSeq p q a (k + 1) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [dSeq_one]; exact two_sub_ne_zero_of_mem_normSetE p q hq ha
    · rw [tauIter_succ, tauIter_zero, dSeq_zero, dSeq_one, one_div]
  | succ k ih =>
    obtain ⟨hd1, htau⟩ := ih
    have hmem : tauIter p q a (k + 1) ∈ normSetE p q := tauIter_mem p q hEinv ha (k + 1)
    have hne : (2 : GaloisField p q) - tauIter p q a (k + 1) ≠ 0 :=
      two_sub_ne_zero_of_mem_normSetE p q hq hmem
    have hkey : (2 : GaloisField p q) - tauIter p q a (k + 1)
        = dSeq p q a (k + 2) / dSeq p q a (k + 1) := by
      rw [htau, dSeq_recurrence]
      field_simp
    refine ⟨?_, ?_⟩
    · intro hcontra
      apply hne
      rw [hkey, hcontra, zero_div]
    · rw [tauIter_succ, hkey, inv_div]

/-- The multiplied form `a_{k+1} · d_{k+1} = d_k`. -/
lemma tauIter_mul_dSeq [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) (k : ℕ) :
    tauIter p q a (k + 1) * dSeq p q a (k + 1) = dSeq p q a k := by
  obtain ⟨hd1, htau⟩ := tauIter_eq_dSeq_div p q hq hEinv ha k
  rw [htau, div_mul_cancel₀ _ hd1]

/-- **Key telescoping output**: `N(d_k) = 1` for every `k`, since each
`a_{k+1} = d_k/d_{k+1} ∈ E` has norm `1` and the norm is multiplicative. -/
lemma normN_dSeq_eq_one [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, normN p q (dSeq p q a k) = 1 := by
  intro k
  induction k with
  | zero => rw [dSeq_zero]; exact normN_one p q
  | succ k ih =>
    have hmul := tauIter_mul_dSeq p q hq hEinv ha k
    have h1 : normN p q (tauIter p q a (k + 1)) = 1 := (tauIter_mem p q hEinv ha (k + 1)).1
    have hcong := congrArg (normN p q) hmul
    rw [normN_mul, h1, one_mul] at hcong
    rw [hcong]; exact ih

/-- Elements of the prime field `𝔽_p ⊆ 𝔽_{p^q}` are fixed by every power of the
Frobenius: `(k : 𝔽_{p^q})^{p^i} = (k : 𝔽_{p^q})`. -/
lemma natCast_pow_pPow [Fact p.Prime] (k i : ℕ) :
    ((k : GaloisField p q)) ^ (p ^ i) = (k : GaloisField p q) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_mul, ih]
    have hk : ((k : ℕ) : GaloisField p q)
        = algebraMap (ZMod p) (GaloisField p q) (k : ZMod p) := (map_natCast _ k).symm
    rw [hk, ← map_pow, ZMod.pow_card]

/-! ## Lemma C.1 -/

/-- **BG Appendix C, Lemma C.1** (mmd L4911): if the norm set is closed under
inversion and has at least two elements, then `p ≤ q`.

Proof (to be formalized, issue 3000): for `a ∈ E^#`, the map `τ(a) = 1/(2-a)`
sends `E` to `E` (using `E = E⁻¹`), and `∏_{j≤k} τ^j(a) = 1/((k+1)-ka)`
telescopes, giving `N((1-a)k+1) = 1` for all `k ∈ 𝔽_p`. The degree-`q` polynomial
`∏_{i<q} ((1-a)^{p^i} X + 1) - 1` (leading coefficient `N(1-a) ≠ 0`) then has all
`p` elements of `𝔽_p` as roots, so `p ≤ q`. -/
theorem lemmaC1 [Fact p.Prime] (hq : q.Prime)
    (hEinv : normSetE p q = (normSetE p q)⁻¹)
    (hcard : 2 ≤ (normSetE p q).ncard) :
    p ≤ q := by
  classical
  -- Start from `a ∈ E^#`.
  obtain ⟨a, ha, hane⟩ := exists_mem_normSetE_ne_one p q hcard
  have h1a : (1 : GaloisField p q) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hane)
  haveI : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]; exact ZMod.charP p
  -- The norm polynomial `P(X) = ∏_{i<q} ((1-a)^{p^i} X + 1) - 1`.
  set P : (GaloisField p q)[X] :=
    (∏ i ∈ Finset.range q, (C ((1 - a) ^ (p ^ i)) * X + C 1)) - C 1 with hP_def
  have hcne : ∀ i, ((1 - a) ^ (p ^ i) : GaloisField p q) ≠ 0 := fun i => pow_ne_zero _ h1a
  have hfac_ne : ∀ i ∈ Finset.range q,
      (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]) ≠ 0 := by
    intro i _ hz
    have hd1 := natDegree_linear (a := (1 - a) ^ (p ^ i)) (b := (1 : GaloisField p q)) (hcne i)
    rw [hz, natDegree_zero] at hd1
    exact one_ne_zero hd1.symm
  -- `P` has degree exactly `q`.
  have hdeg : P.natDegree = q := by
    rw [hP_def, natDegree_sub_C, natDegree_prod _ _ hfac_ne,
      Finset.sum_congr rfl (fun i _ => natDegree_linear (b := (1 : GaloisField p q)) (hcne i)),
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  -- Hence `P ≠ 0`.
  have hPne : P ≠ 0 := by
    intro hz
    have h0 := hdeg
    rw [hz, natDegree_zero] at h0
    have := hq.pos
    omega
  -- Every element of `𝔽_p` is a root of `P`.
  have heval : ∀ k : ℕ, P.eval ((k : ℕ) : GaloisField p q) = 0 := by
    intro k
    rw [hP_def, eval_sub, eval_C, eval_prod]
    have hprod : ∏ i ∈ Finset.range q,
        (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval ((k : ℕ) : GaloisField p q)
          = 1 := by
      have hstep : ∀ i ∈ Finset.range q,
          (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval
            ((k : ℕ) : GaloisField p q)
            = ((1 - a) * ((k : ℕ) : GaloisField p q) + 1) ^ (p ^ i) := by
        intro i _
        simp only [eval_add, eval_mul, eval_C, eval_X]
        rw [add_pow_char_pow, mul_pow, one_pow, natCast_pow_pPow]
      rw [Finset.prod_congr rfl hstep, ← normN]
      have hd : (1 - a) * ((k : ℕ) : GaloisField p q) + 1 = dSeq p q a k := by
        rw [dSeq]; ring
      rw [hd]
      exact normN_dSeq_eq_one p q hq.pos hEinv ha k
    rw [hprod]; ring
  -- `𝔽_p` is a `p`-element finset of roots, and `#roots ≤ deg P = q`.
  have hinj : Set.InjOn ((Nat.cast : ℕ → GaloisField p q))
      (↑(Finset.range p)) := by
    rw [Finset.coe_range]; exact CharP.natCast_injOn_Iio (GaloisField p q) p
  have hScard : ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hSsub : (Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))
      ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hPne, heval k⟩
  calc p = ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card := hScard.symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hSsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = q := hdeg

/-! ## Lemma C.2 machinery (`q = 3` case): the cubic `f_c` -/

/-- **BG Lemma C.2** (`q = 3`), pigeonhole step (mmd L4948): for some `c ∈ 𝔽_p` the
cubic `f_c(x) = x(x-2)(x-c) + (x-1)` has no root in `𝔽_p`.

If every `f_c` had a root `d`, then `d ∉ {0, 2}` (as `f_c(0) = -1`, `f_c(2) = 1`),
and `c` is determined by `d` (`d(d-2)(d-c) = -(d-1)` with `d(d-2) ≠ 0`), so
`c ↦ d` is injective from `𝔽_p` into `𝔽_p ∖ {0, 2}` — impossible by cardinality. -/
lemma exists_rootFree_cubic [Fact p.Prime] (hpodd : Odd p) :
    ∃ c : ZMod p, ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0 := by
  have h3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    rcases hpodd with ⟨k, hk⟩; omega
  haveI : NeZero p := ⟨by omega⟩
  have h02 : (0 : ZMod p) ≠ 2 := by
    intro h
    have h2cast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h.symm
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h2cast
    have := Nat.le_of_dvd (by norm_num) h2cast
    omega
  by_contra hcon
  push Not at hcon
  choose g hg using hcon
  -- `g c ≠ 0` and `g c ≠ 2`, since `f_c(0) = -1`, `f_c(2) = 1`.
  have hg0 : ∀ c, g c ≠ 0 := by
    intro c h
    have hgc := hg c; rw [h] at hgc
    exact one_ne_zero (by linear_combination -hgc)
  have hg2 : ∀ c, g c ≠ 2 := by
    intro c h
    have hgc := hg c; rw [h] at hgc
    exact one_ne_zero (by linear_combination hgc)
  -- `c ↦ g c` is injective (`c` is determined by the common root `d = g c`).
  have hinj : Function.Injective g := by
    intro c1 c2 h
    have e1 := hg c1
    have e2 := hg c2
    rw [h] at e1
    have hdne : g c2 * (g c2 - 2) ≠ 0 := mul_ne_zero (hg0 c2) (sub_ne_zero.mpr (hg2 c2))
    have hfactor : g c2 * (g c2 - 2) * (g c2 - c1) = g c2 * (g c2 - 2) * (g c2 - c2) := by
      linear_combination e1 - e2
    have hsub := mul_left_cancel₀ hdne hfactor
    linear_combination -hsub
  -- Cardinality contradiction: injective map into `𝔽_p ∖ {0,2}` (size `p-2`).
  have himg : Finset.univ.image g ⊆ (Finset.univ : Finset (ZMod p)) \ {0, 2} := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨c, rfl⟩ := hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨hg0 c, hg2 c⟩
  have hc1 : (Finset.univ.image g).card = p := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hcard02 : ({0, 2} : Finset (ZMod p)).card = 2 := Finset.card_pair h02
  have hdisj : Disjoint (Finset.univ.image g) ({0, 2} : Finset (ZMod p)) := by
    rw [Finset.disjoint_left]
    intro a ha ha2
    have := himg ha
    rw [Finset.mem_sdiff] at this
    exact this.2 ha2
  have key : (Finset.univ.image g).card + ({0, 2} : Finset (ZMod p)).card ≤ p :=
    calc (Finset.univ.image g).card + ({0, 2} : Finset (ZMod p)).card
        = (Finset.univ.image g ∪ {0, 2}).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  rw [hc1, hcard02] at key
  omega

/-- The cubic `f_c(X) = X(X-2)(X-c) + (X-1)` of BG Lemma C.2 (`q = 3`). -/
noncomputable def fCubic (c : ZMod p) : (ZMod p)[X] :=
  X * (X - C 2) * (X - C c) + (X - C 1)

lemma fCubic_eval (c x : ZMod p) :
    (fCubic p c).eval x = x * (x - 2) * (x - c) + (x - 1) := by
  simp [fCubic]

lemma fCubic_natDegree [Fact p.Prime] (c : ZMod p) : (fCubic p c).natDegree = 3 := by
  unfold fCubic
  compute_degree!

/-- A root-free `f_c` is irreducible over `𝔽_p` (a cubic with no root). -/
lemma fCubic_irreducible [Fact p.Prime] (c : ZMod p)
    (h : ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0) :
    Irreducible (fCubic p c) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, fCubic_natDegree]; omega
  · intro x hx
    rw [IsRoot, fCubic_eval] at hx
    exact h x hx

/-- An irreducible cubic over `𝔽_p` has a root in `𝔽_{p^3} = GaloisField p 3`
(its root field has cardinality `p^3`, hence is isomorphic to `GaloisField p 3`). -/
lemma exists_root_fCubic [Fact p.Prime] (c : ZMod p) (hirr : Irreducible (fCubic p c)) :
    ∃ a : GaloisField p 3, (Polynomial.aeval a) (fCubic p c) = 0 := by
  haveI : Fact (Irreducible (fCubic p c)) := ⟨hirr⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hne : fCubic p c ≠ 0 := hirr.ne_zero
  haveI : FiniteDimensional (ZMod p) (AdjoinRoot (fCubic p c)) :=
    (AdjoinRoot.powerBasis hne).basis.finiteDimensional_of_finite
  haveI : Finite (AdjoinRoot (fCubic p c)) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot (fCubic p c)) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod p) (AdjoinRoot (fCubic p c)) = 3 := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, fCubic_natDegree]
  have hcard : Nat.card (AdjoinRoot (fCubic p c)) = p ^ 3 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), hfr, ZMod.card]
  let e := GaloisField.algEquivGaloisField p 3 hcard
  refine ⟨e (AdjoinRoot.root (fCubic p c)), ?_⟩
  rw [Polynomial.aeval_algHom_apply]
  have hr : (Polynomial.aeval (AdjoinRoot.root (fCubic p c))) (fCubic p c) = 0 := by
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root (fCubic p c)
  rw [hr, map_zero]

/-- Frobenius propagation: for `f` over `𝔽_p` and `a ∈ 𝔽_{p^q}`,
`f(a)^p = f(a^p)` (the `p`-power map fixes the `𝔽_p`-coefficients of `f`). -/
lemma aeval_pow_p [Fact p.Prime] (a : GaloisField p q) (f : (ZMod p)[X]) :
    (Polynomial.aeval a f) ^ p = Polynomial.aeval (a ^ p) f := by
  haveI : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]; exact ZMod.charP p
  have key : (frobenius (GaloisField p q) p).comp (Polynomial.aeval (R := ZMod p) a).toRingHom
      = (Polynomial.aeval (R := ZMod p) (a ^ p)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.aeval_C, frobenius_def]
      rw [← map_pow, ZMod.pow_card]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.aeval_X, frobenius_def]
  have h := RingHom.congr_fun key f
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, frobenius_def]
    using h

/-- A root `a ∈ 𝔽_{p^3}` of a root-free `f_c` does not lie in the prime field `𝔽_p`
(else `f_c` would have a root in `𝔽_p`). -/
lemma root_not_mem_range [Fact p.Prime] {c : ZMod p} {a : GaloisField p 3}
    (hroot : (Polynomial.aeval a) (fCubic p c) = 0)
    (hrf : ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0) :
    a ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)) := by
  rintro ⟨b, rfl⟩
  refine hrf b ?_
  rw [← fCubic_eval, ← Polynomial.coe_aeval_eq_eval]
  exact (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
    (algebraMap (ZMod p) (GaloisField p 3)).injective).mp hroot

/-- The Frobenius-fixed elements of `𝔽_{p^q}` are exactly the prime field: if
`x^p = x` then `x ∈ 𝔽_p` (the `p` roots of `X^p - X` are the prime field). -/
lemma mem_range_of_pow_p_eq_self [Fact p.Prime] {x : GaloisField p q} (hx : x ^ p = x) :
    x ∈ Set.range (algebraMap (ZMod p) (GaloisField p q)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  set f : (GaloisField p q)[X] := X ^ p - X with hf
  have hfne : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ (Fact.out : p.Prime).one_lt
  have hfdeg : f.natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq _ (Fact.out : p.Prime).one_lt
  have hsub : (Finset.univ.image (algebraMap (ZMod p) (GaloisField p q))) ⊆ f.roots.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨b, _, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfne, Polynomial.IsRoot, hf]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← map_pow, ZMod.pow_card, sub_self]
  have hxroot : x ∈ f.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfne, Polynomial.IsRoot, hf]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx, sub_self]
  have hcardimg : (Finset.univ.image (algebraMap (ZMod p) (GaloisField p q))).card = p := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) (GaloisField p q)).injective,
      Finset.card_univ, ZMod.card]
  have hcardroots : f.roots.toFinset.card ≤ p :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans_eq hfdeg)
  have heq : Finset.univ.image (algebraMap (ZMod p) (GaloisField p q)) = f.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardimg]; exact hcardroots)
  rw [← heq, Finset.mem_image] at hxroot
  obtain ⟨b, _, hb⟩ := hxroot
  exact ⟨b, hb⟩

/-- The cubic `f_c` is monic. -/
lemma fCubic_monic [Fact p.Prime] (c : ZMod p) : (fCubic p c).Monic := by
  unfold fCubic; monicity!

/-- `normN` over `𝔽_{p^3}` is the product of the three Frobenius conjugates. -/
lemma normN_three [Fact p.Prime] (a : GaloisField p 3) :
    normN p 3 a = a * a ^ p * a ^ (p ^ 2) := by
  rw [normN, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
  simp only [pow_zero, pow_one]

/-- **BG Lemma C.2** (`q = 3`), the lift: a root-free `f_c` yields an element of `E`
that is `≠ 1` (its Frobenius conjugates give `N(a) = N(2-a) = 1`). -/
lemma exists_mem_normSetE_three [Fact p.Prime] (hpodd : Odd p) :
    ∃ a : GaloisField p 3, a ∈ normSetE p 3 ∧ a ≠ 1 := by
  classical
  obtain ⟨c, hrf⟩ := exists_rootFree_cubic p hpodd
  have hirr := fCubic_irreducible p c hrf
  obtain ⟨a, hroot⟩ := exists_root_fCubic p c hirr
  have ha_notmem := root_not_mem_range p hroot hrf
  haveI : Fintype (GaloisField p 3) := Fintype.ofFinite _
  haveI : CharP (GaloisField p 3) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p 3) p]; exact ZMod.charP p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  -- `a^{p^3} = a` and the Frobenius orbit relations.
  have hpow3 : a ^ (p ^ 3) = a := by
    have hc3 : Fintype.card (GaloisField p 3) = p ^ 3 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p 3 (by norm_num)]
    rw [← hc3]; exact FiniteField.pow_card a
  have hb1 : a ^ (p ^ 2) = (a ^ p) ^ p := by rw [← pow_mul, pow_two]
  have hb2p : (a ^ (p ^ 2)) ^ p = a := by
    rw [← pow_mul, show p ^ 2 * p = p ^ 3 from by ring, hpow3]
  -- `a, a^p, a^{p²}` are distinct.
  have hd01 : a ^ p ≠ a := fun h => ha_notmem (mem_range_of_pow_p_eq_self p 3 h)
  have hd02 : a ^ (p ^ 2) ≠ a := fun h => hd01 (by have := hb2p; rwa [h] at this)
  have hd12 : a ^ p ≠ a ^ (p ^ 2) := fun h => hd02 (by
    calc a ^ (p ^ 2) = (a ^ p) ^ p := hb1
      _ = (a ^ (p ^ 2)) ^ p := by rw [h]
      _ = a := hb2p)
  -- The mapped cubic `g` is monic of degree 3 with roots `a, a^p, a^{p²}`.
  set g : (GaloisField p 3)[X] := (fCubic p c).map (algebraMap (ZMod p) (GaloisField p 3)) with hg
  have hgeval : ∀ x : GaloisField p 3, g.eval x = (Polynomial.aeval x) (fCubic p c) := by
    intro x; rw [hg, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hgmonic : g.Monic := (fCubic_monic p c).map _
  have hgne : g ≠ 0 := hgmonic.ne_zero
  have hgdeg : g.natDegree = 3 := by rw [hg, (fCubic_monic p c).natDegree_map, fCubic_natDegree]
  have haevalp : (Polynomial.aeval (a ^ p)) (fCubic p c) = 0 := by
    rw [← aeval_pow_p, hroot, zero_pow hp0]
  have haevalp2 : (Polynomial.aeval (a ^ (p ^ 2))) (fCubic p c) = 0 := by
    rw [hb1, ← aeval_pow_p, haevalp, zero_pow hp0]
  have hra : g.eval a = 0 := by rw [hgeval]; exact hroot
  have hrap : g.eval (a ^ p) = 0 := by rw [hgeval]; exact haevalp
  have hrap2 : g.eval (a ^ (p ^ 2)) = 0 := by rw [hgeval]; exact haevalp2
  -- The roots multiset of `g` is exactly `{a, a^p, a^{p²}}`.
  set s : Multiset (GaloisField p 3) := {a, a ^ p, a ^ (p ^ 2)} with hs
  have hs_card : s.card = 3 := rfl
  have hs_nodup : s.Nodup := by
    simp only [hs, Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton, not_or, and_true]
    exact ⟨⟨fun h => hd01 h.symm, fun h => hd02 h.symm⟩, fun h => hd12 h⟩
  have hs_le : s ≤ g.roots := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases hx : x ∈ s
    · rw [Multiset.count_eq_one_of_mem hs_nodup hx]
      refine Multiset.one_le_count_iff_mem.mpr ?_
      rw [Polynomial.mem_roots hgne]
      simp only [hs, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hra
      · exact hrap
      · exact hrap2
    · rw [Multiset.count_eq_zero.mpr hx]; exact Nat.zero_le _
  have hcard_le : g.roots.card ≤ s.card := by
    rw [hs_card]; exact (Polynomial.card_roots' g).trans_eq hgdeg
  have hgroots : g.roots = s := (Multiset.eq_of_le_of_card_le hs_le hcard_le).symm
  have hgprod : g = (s.map (fun r => X - C r)).prod := by
    rw [← hgroots]
    exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hgmonic
      (by rw [hgroots, hs_card]; exact hgdeg.symm)).symm
  -- Evaluate at 0 and 2: `g(0) = -(a a^p a^{p²}) = -N(a)`, `g(2) = N(2-a)`.
  have hprodeval : ∀ x : GaloisField p 3,
      g.eval x = (x - a) * (x - a ^ p) * (x - a ^ (p ^ 2)) := by
    intro x
    rw [hgprod, hs]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have h2pow : (2 : GaloisField p 3) ^ p = 2 := by
    rw [show (2 : GaloisField p 3) = algebraMap (ZMod p) (GaloisField p 3) 2 from
      (map_ofNat _ 2).symm, ← map_pow, ZMod.pow_card]
  have hfc0 : (fCubic p c).eval 0 = -1 := by rw [fCubic_eval]; ring
  have hfc2 : (fCubic p c).eval 2 = 1 := by rw [fCubic_eval]; ring
  have hN_a : normN p 3 a = 1 := by
    have h0 : g.eval 0 = -1 := by
      rw [hgeval,
        show (0 : GaloisField p 3) = algebraMap (ZMod p) (GaloisField p 3) 0 from
          (map_zero _).symm,
        Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval, hfc0, map_neg, map_one]
    rw [hprodeval] at h0
    rw [normN_three]
    linear_combination -h0
  have hN_2a : normN p 3 (2 - a) = 1 := by
    have h2 : g.eval 2 = 1 := by
      rw [hgeval,
        show (2 : GaloisField p 3) = algebraMap (ZMod p) (GaloisField p 3) 2 from
          (map_ofNat _ 2).symm,
        Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval, hfc2, map_one]
    rw [hprodeval] at h2
    rw [normN_three]
    have e1 : (2 - a) ^ p = 2 - a ^ p := by rw [sub_pow_char, h2pow]
    have e2 : (2 - a) ^ (p ^ 2) = 2 - a ^ (p ^ 2) := by
      have hpp : (2 - a) ^ (p ^ 2) = ((2 - a) ^ p) ^ p := by rw [← pow_mul, pow_two]
      rw [hpp, e1, sub_pow_char, h2pow, ← hb1]
    rw [e1, e2]
    linear_combination h2
  exact ⟨a, ⟨hN_a, hN_2a⟩, fun h => ha_notmem ⟨1, by rw [h]; simp⟩⟩

/-! ## Lemma C.2 -/

/-- **BG Appendix C, Lemma C.2, `q = 3` branch**: the cubic argument
exhibits an element of `E` distinct from `1`, hence the norm set has at least
two elements. -/
theorem normSetE_ncard_ge_two_of_eq_three [Fact p.Prime] (hpodd : Odd p) :
    2 ≤ (normSetE p 3).ncard := by
  obtain ⟨a, ha, hane⟩ := exists_mem_normSetE_three p hpodd
  have hsub : ({1, a} : Set (GaloisField p 3)) ⊆ normSetE p 3 := by
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨one_mem_normSetE p 3, ha⟩
  calc
    (2 : ℕ) = ({1, a} : Set (GaloisField p 3)).ncard :=
      (Set.ncard_pair (Ne.symm hane)).symm
    _ ≤ (normSetE p 3).ncard := Set.ncard_le_ncard hsub (normSetE p 3).toFinite

end OddOrder.BG.AppC.NormSet
