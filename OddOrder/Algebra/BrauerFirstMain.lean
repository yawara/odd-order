/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BrauerDefect
import OddOrder.Algebra.ClassSum
import OddOrder.Algebra.DefectGroupConjugacy
import OddOrder.Algebra.GroupAlgebraDefectGroup

/-!
# `Br_D` does not kill a block idempotent with defect group `D`

`BrauerDefect` shows that `Br_P(e) ≠ 0` forces `P` into a conjugate of the defect group.  Here is
the converse at `P = D` itself: for a primitive idempotent `e` of `Z(k[G])` with defect group `D`,

`Br_D(e) ≠ 0`.

Together the two say that the defect groups of a block are exactly the maximal `p`-subgroups `P`
with `Br_P(e) ≠ 0` — Brauer's characterisation, and the reason `Br_D` can be used to transport
blocks between `G` and `N_G(D)`.

The proof runs entirely in the class-sum basis of `Z(k[G])`:

* a class sum `K̂` lies in `A^G_S` for `S` a Sylow `p`-subgroup of the centraliser of a point of
  `K` — because `K̂ = Tr^G_{C_G(x)}(x)` and the index `[C_G(x) : S]` is invertible;
* if `Br_D(e) = 0` then the coefficient of `e` at every class meeting `C_G(D)` vanishes, so `e` is
  a combination of class sums `K̂` with `D ≰ ᵍS_K` for every `g`;
* multiplying by `e` and using `A^G_D · A^G_{S} ⊆ ∑_g A^G_{D ∩ ᵍS}` puts `e` in a sum of trace
  ideals from subgroups *strictly* smaller than `D`;
* Rosenberg's lemma then puts `e` in a single one of them, contradicting minimality of `D`.

## Main results

* `OddOrder.GroupAlgebra.exists_isPGroup_le_centralizer_classSum_mem`
* `OddOrder.GroupAlgebra.brauerProj_ne_zero_of_isDefectGroup`
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra OddOrder.GAlgebra

open scoped OddOrder.Conjugation Pointwise

variable {G : Type*} [Group G]

section Smul

variable {k : Type*} [CommRing k] [Finite G]

/-- The relative trace is `k`-linear. -/
theorem relTrace_smul (K H : Subgroup G) (r : k) (a : MonoidAlgebra k G) :
    relTrace K H (r • a) = r • relTrace K H a := by
  letI : Fintype (↥H ⧸ K.subgroupOf H) := Fintype.ofFinite _
  have hl : relTrace K H (r • a)
      = ∑ x : ↥H ⧸ K.subgroupOf H, (((x.out : ↥H) : G)) • (r • a) := rfl
  have hr : relTrace K H a = ∑ x : ↥H ⧸ K.subgroupOf H, (((x.out : ↥H) : G)) • a := rfl
  rw [hl, hr, Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => conj_smul_smul _ r a

/-- The relative trace ideals are `k`-submodules. -/
theorem smul_mem_relTraceIdeal {K H : Subgroup G} {x : MonoidAlgebra k G}
    (hx : x ∈ relTraceIdeal K H) (r : k) : r • x ∈ relTraceIdeal K H := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨r • a, fun g hg => by rw [conj_smul_smul, ha g hg], relTrace_smul K H r a⟩

end Smul

section Centralizer

open scoped Pointwise in
/-- If `D` lies inside a conjugate of a subgroup of `C_G(x)`, then the corresponding conjugate of
`x` centralises `D`. -/
theorem mem_centralizer_of_le_conj {D S : Subgroup G} {x g : G}
    (hSC : S ≤ Subgroup.centralizer ({x} : Set G)) (hD : D ≤ MulAut.conj g • S) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
  have hmem : g⁻¹ * d * g ∈ S := by
    have := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp (hD hd)
    simpa using this
  have hcomm := Subgroup.mem_centralizer_iff.mp (hSC hmem) x (Set.mem_singleton x)
  calc d * (g * x * g⁻¹) = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * x * g⁻¹) * d := by group

end Centralizer

section ClassSum

variable {k : Type*} [Field k] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **A class sum is a relative trace from a `p`-subgroup of a centraliser.**  Indeed
`K̂ = Tr^G_{C_G(x)}(x)`, and inside `C_G(x)` the index of a Sylow `p`-subgroup `S` is invertible,
so `x` is already a trace from `S`. -/
theorem exists_isPGroup_le_centralizer_classSum_mem (x : G) :
    ∃ S : Subgroup G, S ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup p ↥S ∧
      classSum k x ∈ relTraceIdeal S ⊤ := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  obtain ⟨T⟩ : Nonempty (Sylow p ↥C) := inferInstance
  refine ⟨T.1.map C.subtype, ?_, ?_, ?_⟩
  · rintro y ⟨z, -, rfl⟩
    exact z.2
  · exact T.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ _ C.subtype_injective)
  · -- The index of `S` in `C` is prime to `p`, hence invertible.
    have hSC : T.1.map C.subtype ≤ C := by rintro y ⟨z, -, rfl⟩; exact z.2
    have hsub : (T.1.map C.subtype).subgroupOf C = T.1 := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    have hindex : ¬ p ∣ (T.1.map C.subtype).relIndex C := by
      rw [Subgroup.relIndex, hsub]
      exact T.not_dvd_index
    obtain ⟨v, hv, hvinv⟩ :=
      exists_fixed_nsmul_one_inv (k := k) (G := G) (p := p) hindex
    have hxfix : ∀ u ∈ C, u • (single x (1 : k) : MonoidAlgebra k G) = single x 1 :=
      fun _ hu => smul_single_of_mem_centralizer hu 1
    obtain ⟨w, hw, hwe⟩ :=
      mem_relTraceIdeal_of_index_inv hSC hxfix (fun u _ => hv u) hvinv
    refine ⟨w, hw, ?_⟩
    rw [← relTrace_single_eq_classSum, ← hwe]
    exact (relTrace_trans hSC le_top hw).symm

end ClassSum

section Main

variable {k : Type*} [Field k] [Finite G]

open scoped Classical in
/-- **`Br_D` does not kill a block idempotent with defect group `D`.**

If it did, `e` would be a combination of class sums whose classes avoid `C_G(D)`; each such class
sum lies in `A^G_S` for a `p`-subgroup `S` with `D ≰ ᵍS`, so multiplying by `e` and using
`A^G_D · A^G_S ⊆ ∑_g A^G_{D ∩ ᵍS}` writes `e` as a sum of traces from subgroups strictly inside
`D`.  Rosenberg's lemma then puts `e` in one of them, contradicting minimality. -/
theorem brauerProj_ne_zero_of_isDefectGroup (p : ℕ) [Fact p.Prime] [CharP k p]
    {e : MonoidAlgebra k G}
    (hefix : ∀ g : G, g • e = e) (he : IsIdempotentElem e) (he0 : e ≠ 0)
    (hprim : ∀ u : MonoidAlgebra k G, (∀ g : G, g • u = u) → IsIdempotentElem u → e * u = u →
      u = 0 ∨ u = e)
    {D : Subgroup G} (hD : IsDefectGroup e D) : brauerProj D e ≠ 0 := by
  classical
  intro hbr
  letI : Fintype G := Fintype.ofFinite G
  haveI : Finite (ConjClasses G) := Quotient.finite _
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  -- Choose, for each class, a `p`-subgroup of a centraliser that the class sum is a trace from.
  choose S hSC _hSp hSmem using
    fun x : G => exists_isPGroup_le_centralizer_classSum_mem (k := k) (p := p) x
  -- The classes that meet `C_G(D)` have coefficient `0` in `e`.
  set T : Finset (ConjClasses G) :=
    Finset.univ.filter fun C => ∀ g : G, ¬ D ≤ MulAut.conj g • S C.out with hT
  have hcoeff : ∀ C : ConjClasses G, C ∉ T → e C.out = 0 := by
    intro C hCT
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
      Classical.not_not] at hCT
    obtain ⟨g, hg⟩ := hCT
    have hmemc : g * C.out * g⁻¹ ∈ Subgroup.centralizer (D : Set G) :=
      mem_centralizer_of_le_conj (hSC C.out) hg
    have h0 : e (g * C.out * g⁻¹) = 0 := by
      rw [← brauerProj_apply_of_mem hmemc e, hbr]; rfl
    rwa [apply_eq_of_isConj hefix (isConj_iff.mpr ⟨g, rfl⟩)]
  -- So `e` is a combination of the surviving class sums.
  have hesum : e = ∑ C ∈ T, e C.out • classSum k C.out := by
    refine (eq_sum_classSum hefix).trans
      (Finset.sum_subset (f := fun C : ConjClasses G => e C.out • classSum k C.out)
        (Finset.subset_univ T) fun C _ hCT => ?_).symm
    rw [hcoeff C hCT, zero_smul]
  -- Multiplying by `e` and applying Mackey puts `e` in a sum of trace ideals from proper
  -- subgroups of `D`.
  have hterm : ∀ C ∈ T, ∃ (s : Finset G) (c : G → MonoidAlgebra k G),
      (∀ g ∈ s, c g ∈ relTraceIdeal (D ⊓ MulAut.conj g • S C.out) ⊤) ∧
        e * (e C.out • classSum k C.out) = ∑ g ∈ s, c g := by
    intro C _
    exact exists_mul_eq_sum_relTraceIdeal_inf hD.mem
      (smul_mem_relTraceIdeal (hSmem C.out) (e C.out))
  choose ss cc hcc hccsum using hterm
  -- Assemble the doubly-indexed sum.
  set U : Finset (Σ _ : ConjClasses G, G) := T.sigma (fun C => if h : C ∈ T then ss C h else ∅)
    with hU
  have hUsum : ∑ x ∈ U, (fun x : Σ _ : ConjClasses G, G =>
      if h : x.1 ∈ T then cc x.1 h x.2 else 0) x = e := by
    rw [hU, Finset.sum_sigma]
    have : ∀ C ∈ T, (∑ g ∈ (if h : C ∈ T then ss C h else ∅),
        (if h : C ∈ T then cc C h g else 0)) = e * (e C.out • classSum k C.out) := by
      intro C hC
      simp only [dif_pos hC]
      exact (hccsum C hC).symm
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← hesum, he.eq]
  -- Rosenberg.
  obtain ⟨x, hxU, hxmem⟩ :=
    exists_mem_relTraceIdeal_of_sum_eq (Q := fun x : Σ _ : ConjClasses G, G =>
        if h : x.1 ∈ T then D ⊓ MulAut.conj x.2 • S x.1.out else ⊥)
      hefix he he0
      (N := fun z => IsNilpotent z ∧ ∀ g : G, g • z = z)
      (fun x y hx hy => ⟨Commute.isNilpotent_add
          (commute_of_forall_smul_eq hx.2) hx.1 hy.1,
        fun g => by rw [smul_add, hx.2 g, hy.2 g]⟩)
      (fun h => not_isNilpotent_of_isIdempotentElem he he0 h.1)
      (fun z hz => by
        have hbx : e * z * e = e * z := by
          rw [mul_assoc, (commute_of_forall_smul_eq hz (y := e)).eq, ← mul_assoc, he.eq]
        rw [hbx]
        rcases isNilpotent_or_exists_fixed_mul_eq hefix he hprim hz with h | ⟨u, hu, hub⟩
        · exact Or.inl ⟨h, fun g => by rw [smul_mul', hefix g, hz g]⟩
        · exact Or.inr ⟨u, hu, hub⟩)
      (fun x hx => by
        rw [hU, Finset.mem_sigma] at hx
        simp only [dif_pos hx.1]
        have hxs : x.2 ∈ ss x.1 hx.1 := by simpa only [dif_pos hx.1] using hx.2
        exact hcc x.1 hx.1 x.2 hxs)
      hUsum
  -- The surviving subgroup is strictly smaller than `D`, contradicting minimality.
  rw [hU, Finset.mem_sigma] at hxU
  rw [dif_pos hxU.1] at hxmem
  refine hD.minimal _ (lt_of_le_of_ne inf_le_left fun heq => ?_) hxmem
  have hle : D ≤ MulAut.conj x.2 • S x.1.out := heq ▸ inf_le_right
  simp only [hT, Finset.mem_filter] at hxU
  exact hxU.1.2 x.2 hle

end Main

end OddOrder.GroupAlgebra
