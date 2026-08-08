/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot

/-!
# Counting monic irreducible polynomials over a prime field

An upper bound for the number of monic irreducible polynomials of a fixed degree `r ≥ 2` over
`𝔽_p`:
$$ r \cdot \#\{\text{monic irreducible of degree } r\} \le p^r - p. $$

The proof is the classical one.  Each such polynomial has exactly `r` distinct roots in
`GF(p^r)`; distinct monic irreducibles have disjoint root sets; and no such root lies in the
prime field, because an element of the prime field has minimal polynomial of degree `1 < r`.
So the root sets are `#ι` pairwise disjoint `r`-element subsets of `GF(p^r) ∖ 𝔽_p`, a set with
`p^r - p` elements.

The three field-theoretic inputs all come from mathlib: every finite field is perfect
(`PerfectField.ofFinite`), so irreducible polynomials are separable; every extension of a finite
field is Galois (the instance in `Mathlib/FieldTheory/Finite/GaloisField.lean`), hence normal, so
minimal polynomials split; and `Polynomial.card_rootSet_eq_natDegree` then counts the roots.

The bound is phrased for an arbitrary finite indexing family rather than for "the set of monic
irreducible polynomials of degree `r`", which would need a `Fintype` structure on a subtype of
`(ZMod p)[X]`.  This is the form the consumer needs (BG Appendix C Remark (IV), issue 0179):
there the family is indexed by the points of an affine space that fail to have norm one.
-/

namespace OddOrder.FiniteFieldCount

open Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- A monic irreducible polynomial of degree `r ≠ 0` over `𝔽_p` has a root in `GF(p^r)`.

`AdjoinRoot` of it is an extension of `𝔽_p` of degree `r`, and `GF(p^r)` also has degree `r`, so
`FiniteField.nonempty_algHom_of_finrank_dvd` provides an `𝔽_p`-algebra map between them; the
image of the tautological root is the root sought. -/
theorem exists_isRoot_galoisField {r : ℕ} (hr : r ≠ 0) {f : (ZMod p)[X]} (hmonic : f.Monic)
    (hirr : Irreducible f) (hdeg : f.natDegree = r) :
    ∃ lam : GaloisField p r, (aeval lam) f = 0 := by
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  have hne : f ≠ 0 := hmonic.ne_zero
  have hfr : Module.finrank (ZMod p) (AdjoinRoot f) = r := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := AdjoinRoot f) (L := GaloisField p r)
    (by rw [hfr, GaloisField.finrank p hr])
  refine ⟨φ (AdjoinRoot.root f), ?_⟩
  rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

/-- A monic irreducible polynomial of degree `r ≠ 0` over `𝔽_p` splits in `GF(p^r)`.

It has a root there, hence *is* the minimal polynomial of that root, and minimal polynomials
split because every extension of a finite field is normal. -/
theorem splits_galoisField {r : ℕ} (hr : r ≠ 0) {f : (ZMod p)[X]} (hmonic : f.Monic)
    (hirr : Irreducible f) (hdeg : f.natDegree = r) :
    Splits (f.map (algebraMap (ZMod p) (GaloisField p r))) := by
  obtain ⟨lam, hlam⟩ := exists_isRoot_galoisField p hr hmonic hirr hdeg
  have hmin : f = minpoly (ZMod p) lam := minpoly.eq_of_irreducible_of_monic hirr hlam hmonic
  have hnormal : Normal (ZMod p) (GaloisField p r) := inferInstance
  rw [hmin]
  exact (hnormal.out lam).2

/-- A monic irreducible polynomial of degree `r ≠ 0` over `𝔽_p` has exactly `r` roots in
`GF(p^r)`: it splits there, and it is separable because finite fields are perfect. -/
theorem card_rootSet_galoisField {r : ℕ} (hr : r ≠ 0) {f : (ZMod p)[X]} (hmonic : f.Monic)
    (hirr : Irreducible f) (hdeg : f.natDegree = r) :
    Fintype.card (f.rootSet (GaloisField p r)) = r := by
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hcard := card_rootSet_eq_natDegree (F := ZMod p) (K := GaloisField p r)
    hsep (splits_galoisField p hr hmonic hirr hdeg)
  rw [hcard, hdeg]

/-- An element of `GF(p^r)` that is a root of a monic irreducible polynomial of degree `r ≥ 2`
does not lie in the prime field. -/
theorem notMem_range_algebraMap_of_isRoot {r : ℕ} (hr : 2 ≤ r) {f : (ZMod p)[X]}
    (hmonic : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = r)
    {x : GaloisField p r} (hx : (aeval x) f = 0) :
    x ∉ Set.range (algebraMap (ZMod p) (GaloisField p r)) := by
  rintro ⟨c, rfl⟩
  have hpoly : minpoly (ZMod p) (algebraMap (ZMod p) (GaloisField p r) c) = X - C c := by
    refine (minpoly.eq_of_irreducible_of_monic (irreducible_X_sub_C c) ?_ (monic_X_sub_C c)).symm
    simp
  have h1 : (minpoly (ZMod p) (algebraMap (ZMod p) (GaloisField p r) c)).natDegree = 1 := by
    rw [hpoly, natDegree_X_sub_C]
  rw [← minpoly.eq_of_irreducible_of_monic hirr hx hmonic, hdeg] at h1
  omega

/-- **The counting bound.**  For `r ≥ 2`, an injective family of monic irreducible polynomials of
degree `r` over `𝔽_p`, indexed by a finite type `ι`, satisfies `r * #ι ≤ p^r - p`. -/
theorem mul_card_le {r : ℕ} (hr : 2 ≤ r) {ι : Type*} [Fintype ι]
    (f : ι → (ZMod p)[X]) (hmonic : ∀ i, (f i).Monic) (hirr : ∀ i, Irreducible (f i))
    (hdeg : ∀ i, (f i).natDegree = r) (hinj : Function.Injective f) :
    r * Fintype.card ι ≤ p ^ r - p := by
  classical
  have hr0 : r ≠ 0 := by omega
  haveI : Fintype (GaloisField p r) := Fintype.ofFinite _
  set R : ι → Finset (GaloisField p r) := fun i => ((f i).rootSet (GaloisField p r)).toFinset
    with hRdef
  have hRmem : ∀ (i : ι) (x : GaloisField p r), x ∈ R i ↔ (aeval x) (f i) = 0 := by
    intro i x
    rw [hRdef]
    simp only [Set.mem_toFinset]
    rw [mem_rootSet]
    exact ⟨fun h => h.2, fun h => ⟨(hmonic i).ne_zero, h⟩⟩
  have hRcard : ∀ i, (R i).card = r := by
    intro i
    rw [hRdef]
    simp only [Set.toFinset_card]
    exact card_rootSet_galoisField p hr0 (hmonic i) (hirr i) (hdeg i)
  -- Distinct polynomials have disjoint root sets: a common root would have both as its minimal
  -- polynomial.
  have hRdisj : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      Disjoint (R i) (R j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [hRmem] at hxi
    rw [hRmem] at hxj
    exact hij (hinj (by
      rw [minpoly.eq_of_irreducible_of_monic (hirr i) hxi (hmonic i),
        minpoly.eq_of_irreducible_of_monic (hirr j) hxj (hmonic j)]))
  -- No root lies in the prime field.
  set PF : Finset (GaloisField p r) :=
    Finset.univ.image (algebraMap (ZMod p) (GaloisField p r)) with hPFdef
  have hPFcard : PF.card = p := by
    rw [hPFdef, Finset.card_image_of_injective _
      (algebraMap (ZMod p) (GaloisField p r)).injective, Finset.card_univ, ZMod.card p]
  have hRavoid : ∀ i, R i ⊆ Finset.univ \ PF := by
    intro i x hx
    rw [hRmem] at hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    rw [hPFdef, Finset.mem_image] at hmem
    obtain ⟨c, _, hc⟩ := hmem
    exact notMem_range_algebraMap_of_isRoot p hr (hmonic i) (hirr i) (hdeg i) hx ⟨c, hc⟩
  -- Put the count together.
  have hbi : (Finset.univ.biUnion R).card = Fintype.card ι * r := by
    rw [Finset.card_biUnion hRdisj, Finset.sum_congr rfl fun i _ => hRcard i, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have hsdiff : (Finset.univ \ PF : Finset (GaloisField p r)).card
      = Fintype.card (GaloisField p r) - p := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hPFcard]
  have hsub : Finset.univ.biUnion R ⊆ Finset.univ \ PF :=
    Finset.biUnion_subset.mpr fun i _ => hRavoid i
  have hle := Finset.card_le_card hsub
  rw [hbi, hsdiff] at hle
  have hLcard : Fintype.card (GaloisField p r) = p ^ r := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p r hr0
  rw [hLcard] at hle
  rw [mul_comm]
  exact hle

end OddOrder.FiniteFieldCount
