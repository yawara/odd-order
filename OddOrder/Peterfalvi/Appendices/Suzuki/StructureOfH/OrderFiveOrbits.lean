/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.TConjugateTriple
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.SquareRootFibres
import OddOrder.GroupTheory.FreeActionOrbitCount

/-!
# The `K`-orbits of `S#` in the case `orderOf (st) = 5`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 118:

> It is thus sufficient to show that `s`, `r`, `r⁻¹` and the elements `r r^{-k}`
> for `k ∈ K#` form a system of representatives for the `K`-orbits of `S#`, or,
> since `|S#|/|K| = q + 1 = |K#| + 3`, that these elements are pairwise
> non-conjugate under the action of `K`.

This file sets up that counting: the index type `Fin 3 ⊕ K#`, the family
`orbitRepVal` it names, and the cardinality identity
`|ι| · |K| + 1 = |Q|` which case (b) supplies through `|Q| = |Q₀|²` and
`|K| = |Q₀| − 1`.

## Main results

* `Hypothesis.orbitRepVal` — the book's family of representatives.
* `Hypothesis.card_orbitReprIndex_mul_card_K_succ` — the counting identity.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- The index type of the book's system of representatives: three special
elements `s`, `r`, `r⁻¹`, and one for each `1 ≠ k ∈ K`. -/
abbrev OrbitReprIndex : Type _ := Fin 3 ⊕ {k : ↥hyp.K // k ≠ 1}

/-- The book's family of representatives, as elements of `G`. -/
noncomputable def orbitRepVal : hyp.OrbitReprIndex → G
  | Sum.inl i =>
      ![hyp.distinguishedInvolution, hyp.structureConjugator,
        hyp.structureConjugator⁻¹] i
  | Sum.inr k =>
      hyp.structureConjugator *
        ((k : G)⁻¹ * hyp.structureConjugator⁻¹ * (k : G))

lemma orbitRepVal_mem_Q (i : hyp.OrbitReprIndex) : hyp.orbitRepVal i ∈ hyp.Q := by
  cases i with
  | inl i =>
    fin_cases i
    · exact hyp.distinguishedInvolution_mem_Q
    · exact hyp.structureConjugator_mem_Q
    · exact hyp.Q.inv_mem hyp.structureConjugator_mem_Q
  | inr k =>
    exact hyp.structureConjugator_mul_conj_inv_mem
      (by rw [← hyp.coe_K]; exact k.1.2)

lemma orbitRepVal_ne_one (i : hyp.OrbitReprIndex) : hyp.orbitRepVal i ≠ 1 := by
  cases i with
  | inl i =>
    fin_cases i
    · exact hyp.distinguishedInvolution_ne_one
    · exact hyp.structureConjugator_ne_one
    · exact inv_ne_one.mpr hyp.structureConjugator_ne_one
  | inr k =>
    exact hyp.structureConjugator_mul_conj_inv_ne_one
      (by rw [← hyp.coe_K]; exact k.1.2) (fun h => k.2 (Subtype.ext h))

lemma orbitRepVal_mem_orbitReprSet (i : hyp.OrbitReprIndex) :
    hyp.orbitRepVal i ∈ hyp.orbitReprSet := by
  cases i with
  | inl i =>
    refine Or.inl ?_
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  | inr k =>
    exact Or.inr ⟨(k : G), k.1.2, (fun h => k.2 (Subtype.ext h)), rfl⟩

/-- `|K#| = |K| − 1`. -/
lemma card_K_ne_one : Nat.card {k : ↥hyp.K // k ≠ 1} = Nat.card ↥hyp.K - 1 := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥hyp.K))
  rw [Finite.card_option] at h
  omega

/-- **The counting identity** `(|K#| + 3) · |K| + 1 = |Q|` of Peterfalvi
Part II, Ch. III §2, p. 118, in case (b): there `|Q| = q²` and `|K| = q − 1`,
so the left-hand side is `(q + 1)(q − 1) + 1 = q²`. -/
lemma card_orbitReprIndex_mul_card_K_succ
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2) :
    Nat.card hyp.OrbitReprIndex * Nat.card ↥hyp.K + 1 = Nat.card ↥hyp.Q := by
  have hKcard : Nat.card ↥hyp.K = Nat.card ↥hyp.Q0 - 1 :=
    hyp.card_K_eq_card_Q0_sub_one
  have hQ0 : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  have hidx : Nat.card hyp.OrbitReprIndex = 3 + (Nat.card ↥hyp.K - 1) := by
    rw [OrbitReprIndex, Nat.card_sum, hyp.card_K_ne_one, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥hyp.Q0 = d + 2 := ⟨Nat.card ↥hyp.Q0 - 2, by omega⟩
  have hK : Nat.card ↥hyp.K = d + 1 := by rw [hKcard, hd]; omega
  have hidx' : Nat.card hyp.OrbitReprIndex = d + 3 := by rw [hidx, hK]; omega
  have hsq : (d + 2) ^ 2 = d * d + 4 * d + 4 := by ring
  have hprod : (d + 3) * (d + 1) = d * d + 4 * d + 3 := by ring
  rw [hidx', hK, hQcard, hd, hsq, hprod]

@[simp] lemma orbitRepVal_inl_zero :
    hyp.orbitRepVal (Sum.inl 0) = hyp.distinguishedInvolution := rfl

@[simp] lemma orbitRepVal_inl_one :
    hyp.orbitRepVal (Sum.inl 1) = hyp.structureConjugator := rfl

@[simp] lemma orbitRepVal_inl_two :
    hyp.orbitRepVal (Sum.inl 2) = hyp.structureConjugator⁻¹ := rfl

@[simp] lemma orbitRepVal_inr (k : {k : ↥hyp.K // k ≠ 1}) :
    hyp.orbitRepVal (Sum.inr k)
      = hyp.structureConjugator *
          ((k : G)⁻¹ * hyp.structureConjugator⁻¹ * (k : G)) := rfl

lemma structureConjugator_inv_notMem_Q0 (hr2 : hyp.structureConjugator ^ 2 ≠ 1) :
    hyp.structureConjugator⁻¹ ∉ hyp.Q0 := by
  intro h
  refine hr2 ?_
  have h2 : (hyp.structureConjugator⁻¹) ^ 2 = 1 := h.1
  rw [inv_pow, inv_eq_one] at h2
  exact h2

/-- Conjugates of `s` stay in `Q₀`, so `s` is not `K`-conjugate to anything
outside `Q₀`. -/
lemma not_conj_distinguishedInvolution_of_notMem_Q0 {y a : G} (ha : a ∈ hyp.KSet)
    (hy : y ∉ hyp.Q0) : a⁻¹ * hyp.distinguishedInvolution * a ≠ y := fun h =>
  hy (h ▸ hyp.conj_distinguishedInvolution_mem_Q0 ha)

/-- …and conversely. -/
lemma not_conj_of_notMem_Q0_distinguishedInvolution {y a : G} (ha : a ∈ hyp.KSet)
    (hy : y ∉ hyp.Q0) : a⁻¹ * y * a ≠ hyp.distinguishedInvolution := by
  intro h
  refine hy ?_
  have h2 : y = a * hyp.distinguishedInvolution * a⁻¹ := by rw [← h]; group
  rw [h2]
  have := hyp.conj_mem_Q0_of_mem_KSet (hyp.inv_mem_KSet ha)
    hyp.distinguishedInvolution_mem_Q0
  rwa [inv_inv] at this

/-- **The representatives are pairwise non-conjugate under `K`** (Peterfalvi
Part II, Ch. III §2, p. 118), granted the last pair (the `r r^{-k}` among
themselves, which is the field computation of p. 119).

The four families are told apart by three `K`-orbit invariants — membership of
`y`, of `g(y)` and of `f(y)` in `Q₀` — whose values are `(T, F, F)` at `s`,
`(F, F, T)` at `r`, `(F, T, F)` at `r⁻¹` and `(F, F, F)` at `r r^{-k}`. -/
theorem orbitRepVal_pairwise (hr2 : hyp.structureConjugator ^ 2 ≠ 1)
    (hpair : ∀ k₁ k₂ a : G, k₁ ∈ hyp.KSet → k₁ ≠ 1 → k₂ ∈ hyp.KSet → k₂ ≠ 1 →
      a ∈ hyp.KSet →
      a⁻¹ * (hyp.structureConjugator * (k₁⁻¹ * hyp.structureConjugator⁻¹ * k₁)) * a
        = hyp.structureConjugator * (k₂⁻¹ * hyp.structureConjugator⁻¹ * k₂) →
      k₁ = k₂)
    (i j : hyp.OrbitReprIndex) {a : G} (ha : a ∈ hyp.KSet)
    (hij : a⁻¹ * hyp.orbitRepVal i * a = hyp.orbitRepVal j) : i = j := by
  have hai : a⁻¹ ∈ hyp.KSet := hyp.inv_mem_KSet ha
  have hji' : (a⁻¹)⁻¹ * hyp.orbitRepVal j * a⁻¹ = hyp.orbitRepVal i := by
    rw [inv_inv, ← hij]; group
  have hrQ0 := hyp.structureConjugator_notMem_Q0 hr2
  have hriQ0 := hyp.structureConjugator_inv_notMem_Q0 hr2
  have hkQ0 : ∀ k : {k : ↥hyp.K // k ≠ 1},
      hyp.orbitRepVal (Sum.inr k) ∉ hyp.Q0 := fun k =>
    hyp.structureConjugator_mul_conj_inv_notMem_Q0 hr2
      (by rw [← hyp.coe_K]; exact k.1.2) (fun h => k.2 (Subtype.ext h))
  rcases i with i | k <;> rcases j with j | l
  · fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij (hyp.not_conj_distinguishedInvolution_of_notMem_Q0 ha hrQ0)
    · exact absurd hij (hyp.not_conj_distinguishedInvolution_of_notMem_Q0 ha hriQ0)
    · exact absurd hij (hyp.not_conj_of_notMem_Q0_distinguishedInvolution ha hrQ0)
    · rfl
    · exact absurd hij (hyp.structureConjugator_not_conj_inv hr2 ha)
    · exact absurd hij (hyp.not_conj_of_notMem_Q0_distinguishedInvolution ha hriQ0)
    · exact absurd hji' (hyp.structureConjugator_not_conj_inv hr2 hai)
    · rfl
  · exfalso
    have hlK : (l : G) ∈ hyp.KSet := by rw [← hyp.coe_K]; exact l.1.2
    have hl1 : (l : G) ≠ 1 := fun h => l.2 (Subtype.ext h)
    fin_cases i
    · exact hyp.conj_distinguishedInvolution_ne_structureConjugator_mul_conj_inv
        hr2 hlK hl1 ha hij
    · exact hyp.conj_structureConjugator_ne_mul_conj_inv hr2 hlK hl1 ha hij
    · exact hyp.conj_structureConjugator_inv_ne_mul_conj_inv hr2 hlK hl1 ha hij
  · exfalso
    have hkK : (k : G) ∈ hyp.KSet := by rw [← hyp.coe_K]; exact k.1.2
    have hk1 : (k : G) ≠ 1 := fun h => k.2 (Subtype.ext h)
    fin_cases j
    · exact hyp.not_conj_of_notMem_Q0_distinguishedInvolution ha (hkQ0 k) hij
    · exact hyp.conj_structureConjugator_ne_mul_conj_inv hr2 hkK hk1 hai hji'
    · exact hyp.conj_structureConjugator_inv_ne_mul_conj_inv hr2 hkK hk1 hai hji'
  · have hkK : (k : G) ∈ hyp.KSet := by rw [← hyp.coe_K]; exact k.1.2
    have hk1 : (k : G) ≠ 1 := fun h => k.2 (Subtype.ext h)
    have hlK : (l : G) ∈ hyp.KSet := by rw [← hyp.coe_K]; exact l.1.2
    have hl1 : (l : G) ≠ 1 := fun h => l.2 (Subtype.ext h)
    exact congrArg Sum.inr (Subtype.ext (Subtype.ext
      (hpair (k : G) (l : G) a hkK hk1 hlK hl1 ha hij)))

/-- **The book's list meets every `K`-orbit of `S#`** (Peterfalvi Part II,
Ch. III §2, p. 118), granted the last non-conjugacy `hpair` of p. 119.

`K` acts on `Q` by conjugation, fixing only `1` (Ch. I §2 Proposition 1(a)), and
the list has `|ι| · |K| + 1 = |Q|` members in pairwise distinct orbits, so
`exists_mem_orbit_of_card_mul_succ_eq` applies. -/
theorem orbitReprSet_covers (hr2 : hyp.structureConjugator ^ 2 ≠ 1)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (hpair : ∀ k₁ k₂ a : G, k₁ ∈ hyp.KSet → k₁ ≠ 1 → k₂ ∈ hyp.KSet → k₂ ≠ 1 →
      a ∈ hyp.KSet →
      a⁻¹ * (hyp.structureConjugator * (k₁⁻¹ * hyp.structureConjugator⁻¹ * k₁)) * a
        = hyp.structureConjugator * (k₂⁻¹ * hyp.structureConjugator⁻¹ * k₂) →
      k₁ = k₂)
    {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) :
    ∃ a ∈ hyp.K, ∃ y ∈ hyp.orbitReprSet, x = a⁻¹ * y * a := by
  letI : MulAction ↥hyp.K ↥hyp.Q := MulAction.compHom _ hyp.conjQByK
  have hsmul : ∀ (a : ↥hyp.K) (y : ↥hyp.Q),
      ((a • y : ↥hyp.Q) : G) = (a : G) * (y : G) * (a : G)⁻¹ := fun _ _ => rfl
  set rep : hyp.OrbitReprIndex → ↥hyp.Q :=
    fun i => ⟨hyp.orbitRepVal i, hyp.orbitRepVal_mem_Q i⟩ with hrepdef
  have hmemKSet : ∀ a : ↥hyp.K, (a : G) ∈ hyp.KSet := fun a => by
    rw [← hyp.coe_K]; exact a.2
  have hone : ∀ a : ↥hyp.K, a • (1 : ↥hyp.Q) = 1 := fun a => map_one (hyp.conjQByK a)
  have hfree : ∀ (a : ↥hyp.K) (y : ↥hyp.Q), y ≠ 1 → a • y = y → a = 1 := by
    intro a y hy hfix
    by_contra hane
    exact hy (hyp.conjQByK_fixed_eq_one hane hfix)
  have hrepne : ∀ i, rep i ≠ 1 := fun i h =>
    hyp.orbitRepVal_ne_one i (congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) h)
  have hrep : ∀ (i j : hyp.OrbitReprIndex) (a : ↥hyp.K), a • rep i = rep j → i = j := by
    intro i j a h
    refine hyp.orbitRepVal_pairwise hr2 hpair i j (hyp.inv_mem_KSet (hmemKSet a)) ?_
    have hval := congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) h
    rw [hsmul a (rep i)] at hval
    rw [inv_inv]
    exact hval
  obtain ⟨i, a, hia⟩ :=
    OddOrder.GroupTheory.FreeActionOrbitCount.exists_mem_orbit_of_card_mul_succ_eq
    rep 1 hone hfree hrepne hrep
    (hyp.card_orbitReprIndex_mul_card_K_succ hQcard)
    (x := (⟨x, hx⟩ : ↥hyp.Q)) (fun h => hx1 (congrArg
      (Subtype.val (p := fun z => z ∈ hyp.Q)) h))
  refine ⟨(a : G)⁻¹, hyp.K.inv_mem a.2, hyp.orbitRepVal i,
    hyp.orbitRepVal_mem_orbitReprSet i, ?_⟩
  have hval := congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) hia
  rw [hsmul a (rep i)] at hval
  rw [inv_inv]
  exact hval.symm

/-- **`h(x) ∈ K` for every `x ∈ Q ∖ {1}`** (Peterfalvi Part II, Ch. III §2,
p. 118), granted the last non-conjugacy of p. 119.  This *is* the Proposition of
§2: `t x t = g(x) h(x) t f(x)` with `h(x) ∈ K` says `t S t ⊆ S K t S`. -/
theorem tConjMiddle_mem_K (hr2 : hyp.structureConjugator ^ 2 ≠ 1)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (hpair : ∀ k₁ k₂ a : G, k₁ ∈ hyp.KSet → k₁ ≠ 1 → k₂ ∈ hyp.KSet → k₂ ≠ 1 →
      a ∈ hyp.KSet →
      a⁻¹ * (hyp.structureConjugator * (k₁⁻¹ * hyp.structureConjugator⁻¹ * k₁)) * a
        = hyp.structureConjugator * (k₂⁻¹ * hyp.structureConjugator⁻¹ * k₂) →
      k₁ = k₂)
    {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) : hyp.tConjMiddle x ∈ hyp.K :=
  hyp.tConjMiddle_mem_K_of_orbitReprSet_covers
    (fun _ hy hy1 => hyp.orbitReprSet_covers hr2 hQcard hpair hy hy1) hx hx1

/-- **The Proposition of §2 in the book's hypotheses** (Peterfalvi Part II,
Ch. III §2, p. 118): case (b) of §1 gives `orderOf (st) = 5`, whence `r² ≠ 1`,
and `|Q| = |Q₀|²` (`S` of type A). -/
theorem tConjMiddle_mem_K_of_orderOf_st_eq_five
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (hpair : ∀ k₁ k₂ a : G, k₁ ∈ hyp.KSet → k₁ ≠ 1 → k₂ ∈ hyp.KSet → k₂ ≠ 1 →
      a ∈ hyp.KSet →
      a⁻¹ * (hyp.structureConjugator * (k₁⁻¹ * hyp.structureConjugator⁻¹ * k₁)) * a
        = hyp.structureConjugator * (k₂⁻¹ * hyp.structureConjugator⁻¹ * k₂) →
      k₁ = k₂)
    {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) : hyp.tConjMiddle x ∈ hyp.K :=
  hyp.tConjMiddle_mem_K (hyp.structureConjugator_sq_ne_one h5) hQcard hpair hx hx1

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
