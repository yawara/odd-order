/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic

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
  push_neg at h
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
  push_neg at hcon
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
    FiniteDimensional.of_fintype_basis (AdjoinRoot.powerBasis hne).basis
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

/-- **BG Appendix C, Lemma C.2** (mmd L4923): the norm set has at least two
elements (assuming only that `p`, `q` are odd primes satisfying condition (A)).

Proof (to be formalized, issue 3000): for `q ≥ 5` via the character theory of the
Frobenius group `H = P ⋊ U` (`|E|` is a structure constant bounded below by
`p^{q-2} - p^{q/2} > 1` through the orthogonality relations); for `q = 3` via the
cubic `f_c(x) = x(x-2)(x-c) + (x-1)`, some `c` of which has no root in `𝔽_p`,
yielding a root `a ∈ 𝔽_{p^3}` with `N(a) = N(2-a) = 1`, so `a, 1 ∈ E`. -/
theorem lemmaC2 [Fact p.Prime] (hpodd : Odd p) (hq : q.Prime) (hqodd : Odd q)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    2 ≤ (normSetE p q).ncard := by
  rcases eq_or_ne q 3 with rfl | hq3
  · -- `q = 3`: the cubic argument exhibits an element of `E` distinct from `1`.
    obtain ⟨a, ha, hane⟩ := exists_mem_normSetE_three p hpodd
    have hsub : ({1, a} : Set (GaloisField p 3)) ⊆ normSetE p 3 := by
      rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨one_mem_normSetE p 3, ha⟩
    calc (2 : ℕ) = ({1, a} : Set (GaloisField p 3)).ncard := (Set.ncard_pair (Ne.symm hane)).symm
      _ ≤ (normSetE p 3).ncard := Set.ncard_le_ncard hsub (normSetE p 3).toFinite
  · -- `q ≥ 5`: the character theory of the Frobenius group `H = P ⋊ U`. TODO (issue 3000).
    sorry

end OddOrder.BG.AppC.NormSet
