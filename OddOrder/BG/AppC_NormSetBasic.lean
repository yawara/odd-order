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
# BG Appendix C — the norm set: basics, Remark (I), the Frobenius product

The norm and the norm set with their basic algebra, Remark (I)
(condition (A) ⟺ `q ∤ (p-1)`), the generator-relation finite-field helpers, the
Frobenius stability of the norm set (Lemma C.3 Step 4), and the Frobenius
semidirect product `P ⋊ U` for Lemmas C.2/C.3.

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
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

/-- The additive kernel `P` in the concrete Frobenius group `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusKernel [Fact p.Prime] :
    Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q).range

/-- The norm-one complement `U` in the concrete Frobenius group `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusComplement [Fact p.Prime] :
    Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range

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


end OddOrder.BG.AppC.NormSet
