/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.IsMetacyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Normal type-`(p,p)` subgroups inside a normal elementary abelian subgroup

`OddOrder.GroupTheory` shared module.  If a finite `p`-group `R` has a **normal**
elementary abelian subgroup `V` with `p² ≤ |V|`, then `R` has a **normal** subgroup
of order `p²` and exponent `p` (a subgroup of *type `(p,p)`*) contained in `V`.

This is the "unipotent invariant subspace" step: `R` acts by conjugation on the
`𝔽_p`-space `V`, and a `p`-group of linear transformations over `𝔽_p` fixes a
nonzero vector (Gorenstein "Finite Groups" §2.6, Lemma 6).  We phrase it purely
group-theoretically, using twice that a nontrivial normal subgroup of a `p`-group
meets the centre (`CriticalSubgroup.exists_mem_center_of_normal_ne_bot`): once in
`R` to get a central `z ∈ V` of order `p`, and once in `R/⟨z⟩` to get `v ∈ V` whose
image is central in `R/⟨z⟩`.  Then `⟨z, v⟩ ⊴ R` is the desired type-`(p,p)`
subgroup.

## Main results

* `exists_normal_isElementaryAbelian_card_prime_sq_le_of_normal`: the statement
  above (input: `V ⊴ R` elementary abelian with `p² ≤ |V|`).
* `exists_normal_isElementaryAbelian_card_prime_sq_of_normal_not_isCyclic`: the
  same conclusion from a **noncyclic normal abelian** subgroup `A ⊴ R` (take
  `V = Ω₁(A)`).  This removes the *central* hypothesis from the abelian-center case
  of BG Lemma 4.5(a) and is the invariant-subspace half of Gorenstein 5.4.10.

Downstream: the odd-`p` case of Gorenstein 5.4.10 (BG Lemma 4.5(a), which unblocks
Peterfalvi Appendix I/B, `Huppert.pGroup_cyclic_fixedPointFree`) reduces — via a
critical subgroup — to producing a noncyclic normal abelian subgroup, at which
point the corollary here supplies the normal type-`(p,p)`.
-/

namespace OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

omit [Finite R] in
/-- A subgroup of the centre is normal. -/
private theorem normal_of_le_center {H : Subgroup R} (hH : H ≤ Subgroup.center R) :
    H.Normal :=
  ⟨fun n hn g => by
    rw [(Subgroup.mem_center_iff.mp (hH hn) g), mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩

omit [Finite R] in
/-- An element of order dividing `p`, if nontrivial, generates a subgroup of order
`p`. -/
private theorem card_zpowers_eq_prime_of_pow {z : R} (hzp : z ^ p = 1) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.zpowers z) = p := by
  have hord_ne : orderOf z ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact hz1
  have hord : orderOf z = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hzp)).resolve_left hord_ne
  rw [Nat.card_zpowers, hord]

/-- **Invariant type-`(p,p)` inside a normal elementary abelian subgroup.**
A finite `p`-group `R` with a normal elementary abelian subgroup `V` of order at
least `p²` has a *normal* subgroup of order `p²` and exponent `p` contained in `V`.

`R` acts on the `𝔽_p`-space `V`; a `p`-group action fixes a line, and two nested
applications of "nontrivial normal ⟹ meets centre" build the invariant
`2`-dimensional subspace `⟨z, v⟩`. -/
theorem exists_normal_isElementaryAbelian_card_prime_sq_le_of_normal
    (hR : IsPGroup p R) {V : Subgroup R} [V.Normal]
    (hVea : V.IsElementaryAbelian p) (hVcard : p ^ 2 ≤ Nat.card V) :
    ∃ B : Subgroup R, B.Normal ∧ B ≤ V ∧ B.IsElementaryAbelian p ∧
      Nat.card B = p ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  -- `V ≠ ⊥` since `|V| ≥ p² > 1`.
  have hV_ne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVcard
    nlinarith [hp.two_le, hp.one_lt]
  -- (1) a central `z ∈ V` of order `p`.
  obtain ⟨z, hzV, hzC, hz1⟩ := exists_mem_center_of_normal_ne_bot hR hV_ne
  have hzp : z ^ p = 1 := by
    simpa using congrArg (Subtype.val) (hVea.pow_eq_one ⟨z, hzV⟩)
  set Z : Subgroup R := Subgroup.zpowers z with hZdef
  have hZleV : Z ≤ V := (Subgroup.zpowers_le).mpr hzV
  have hZleC : Z ≤ Subgroup.center R := (Subgroup.zpowers_le).mpr hzC
  haveI hZnormal : Z.Normal := normal_of_le_center hZleC
  have hZcard : Nat.card Z = p := card_zpowers_eq_prime_of_pow hzp hz1
  -- (2) pass to `Q = R/Z`; the image of `V` is a nontrivial normal subgroup.
  let mk : R →* R ⧸ Z := QuotientGroup.mk' Z
  have hmk_surj : Function.Surjective mk := QuotientGroup.mk'_surjective Z
  have hker : ∀ x : R, mk x = 1 ↔ x ∈ Z := fun x => QuotientGroup.eq_one_iff x
  set Vbar : Subgroup (R ⧸ Z) := V.map mk with hVbardef
  haveI hVbar_normal : Vbar.Normal := Subgroup.Normal.map inferInstance mk hmk_surj
  have hQ_pgroup : IsPGroup p (R ⧸ Z) := hR.to_quotient Z
  -- `Vbar ≠ ⊥`: else `V ≤ Z`, contradicting `|V| ≥ p² > p = |Z|`.
  have hVbar_ne : Vbar ≠ ⊥ := by
    intro h
    have hVleZ : V ≤ Z := by
      intro x hx
      have hmem : mk x ∈ Vbar := Subgroup.mem_map_of_mem mk hx
      rw [h, Subgroup.mem_bot, hker] at hmem
      exact hmem
    have hle : Nat.card V ≤ Nat.card Z := Subgroup.card_le_of_le hVleZ
    rw [hZcard] at hle
    nlinarith [hp.two_le, hp.one_lt, le_trans hVcard hle]
  -- (3) a `Q`-central `v̄ ∈ Vbar`, `v̄ ≠ 1`; lift to `v ∈ V`.
  obtain ⟨vbar, hvbarV, hvbarC, hvbar1⟩ :=
    exists_mem_center_of_normal_ne_bot hQ_pgroup hVbar_ne
  obtain ⟨v, hvV, hvmk⟩ := Subgroup.mem_map.mp hvbarV
  have hvnotZ : v ∉ Z := by
    intro hvZ
    exact hvbar1 (hvmk ▸ (hker v).mpr hvZ)
  have hvp : v ^ p = 1 := by
    simpa using congrArg (Subtype.val) (hVea.pow_eq_one ⟨v, hvV⟩)
  have hv1 : v ≠ 1 := fun h => hvnotZ (h ▸ Subgroup.one_mem Z)
  set Y : Subgroup R := Subgroup.zpowers v with hYdef
  have hYleV : Y ≤ V := (Subgroup.zpowers_le).mpr hvV
  have hYcard : Nat.card Y = p := card_zpowers_eq_prime_of_pow hvp hv1
  -- (4) `B = Z ⊔ Y = ⟨z, v⟩`.
  set B : Subgroup R := Z ⊔ Y with hBdef
  have hBleV : B ≤ V := sup_le hZleV hYleV
  have hzB : z ∈ B := (le_sup_left : Z ≤ B) (Subgroup.mem_zpowers z)
  have hvB : v ∈ B := (le_sup_right : Y ≤ B) (Subgroup.mem_zpowers v)
  -- `Z ⊓ Y = ⊥` (both order `p`, distinct since `v ∉ Z`).
  have hInf_bot : Z ⊓ Y = ⊥ := by
    have hInf_dvd : Nat.card (Z ⊓ Y : Subgroup R) ∣ p :=
      hYcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hInf_dvd with hc | hc
    · exact Subgroup.eq_bot_of_card_eq _ hc
    · exfalso
      have h1 : Z ⊓ Y = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZcard, hc])
      have h2 : Z ⊓ Y = Y := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hYcard, hc])
      exact hvnotZ ((h2.symm.trans h1) ▸ (Subgroup.mem_zpowers v : v ∈ Y))
  -- `|B| = p²`.
  have hBcard : Nat.card B = p ^ 2 := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card (H := Z) (K := Y)
    rw [← Subgroup.normal_mul Z Y, hInf_bot, Subgroup.card_bot, hZcard, hYcard,
      mul_one] at hcard
    simpa [hBdef, pow_two] using hcard
  -- `B` elementary abelian (subgroup of `V`).
  have hBea : B.IsElementaryAbelian p :=
    (hVea.to_subgroup (B.subgroupOf V)).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBleV)
  -- `g v g⁻¹ ∈ B` for all `g` (from `v̄ ∈ Z(Q)`).
  have hgvg : ∀ g : R, g * v * g⁻¹ ∈ B := by
    intro g
    have hcentral : mk g * mk v = mk v * mk g :=
      Subgroup.mem_center_iff.mp (hvmk.symm ▸ hvbarC) (mk g)
    have hmkeq : mk (g * v * g⁻¹) = mk v := by
      rw [map_mul, map_mul, map_inv, hcentral, mul_assoc, mul_inv_cancel, mul_one]
    -- so `g v g⁻¹ * v⁻¹ ∈ Z`
    have hmem : g * v * g⁻¹ * v⁻¹ ∈ Z := by
      rw [← hker]; rw [map_mul, map_inv, hmkeq, mul_inv_cancel]
    rw [show g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v by group]
    exact B.mul_mem ((le_sup_left : Z ≤ B) hmem) hvB
  -- normality: `B = closure {z, v}`, conjugation preserves the generators.
  have hBclosure : B = Subgroup.closure ({z, v} : Set R) := by
    rw [hBdef, hZdef, hYdef, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
  have hBnormal : B.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hBclosure] at hn ⊢
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · rw [(Subgroup.mem_center_iff.mp hzC g), mul_assoc, mul_inv_cancel, mul_one]
          exact Subgroup.subset_closure (by simp)
        · rw [← hBclosure]; exact hgvg g
    | one => simp
    | mul a b _ _ ha hb =>
        rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
        exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
        rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ ha
  exact ⟨B, hBnormal, hBleV, hBea, hBcard⟩

/-- **Noncyclic form.** A finite `p`-group `R` with a *noncyclic* normal elementary
abelian subgroup `V` has a normal subgroup of order `p²` and exponent `p`
(type `(p,p)`) contained in `V`.

This is the invariant-subspace half of Gorenstein "Finite Groups" 5.4.10 (BG Lemma
4.5(a)): once a noncyclic normal abelian subgroup is found, its `Ω₁` is a noncyclic
normal elementary abelian subgroup, and this supplies the normal type-`(p,p)`. -/
theorem exists_normal_isElementaryAbelian_card_prime_sq_of_normal_not_isCyclic
    (hR : IsPGroup p R) {V : Subgroup R} [V.Normal]
    (hVea : V.IsElementaryAbelian p) (hVnc : ¬ IsCyclic V) :
    ∃ B : Subgroup R, B.Normal ∧ B ≤ V ∧ B.IsElementaryAbelian p ∧
      Nat.card B = p ^ 2 := by
  have hp : p.Prime := Fact.out
  refine exists_normal_isElementaryAbelian_card_prime_sq_le_of_normal hR hVea ?_
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hVea.isPGroup
  rw [hk]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hlt
  push Not at hlt
  interval_cases k
  · exact hVnc (by
      haveI : Subsingleton V := (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
      exact isCyclic_of_subsingleton)
  · exact hVnc (isCyclic_of_prime_card (p := p) (by rw [hk, pow_one]))

/-! ## Cyclic self-centralizing normal subgroups force metacyclic (odd `p`) -/

/-- A finite `p`-group (`p` odd) with a **cyclic self-centralizing normal** subgroup
`A` is metacyclic.

Conjugation gives `R →* MulAut A` with kernel `C_R(A) = A`, so `R/A ↪ MulAut A`.
For `A` a cyclic `p`-group with `p` odd, `MulAut A ≅ (ℤ/p^m)ˣ` is cyclic
(`IsCyclic.mulAutMulEquiv` + `ZMod.isCyclic_units_of_prime_pow`); a subgroup of a
cyclic group is cyclic, so `R/A` is cyclic and `⟨A, R/A⟩` witnesses metacyclicity.

This is the reduction used in Gorenstein "Finite Groups" 5.4.10 / BG Lemma 4.5(a):
if the maximal abelian normal subgroup is cyclic, `R` is metacyclic. -/
theorem isMetacyclic_of_isCyclic_selfCentralizing_normal
    (hR : IsPGroup p R) (hp2 : p ≠ 2)
    {A : Subgroup R} [hAn : A.Normal] (hAcyc : IsCyclic A)
    (hself : Subgroup.centralizer (A : Set R) = A) :
    IsMetacyclic R := by
  haveI : IsCyclic A := hAcyc
  -- `MulAut A` is cyclic.
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (hR.to_subgroup A)
  haveI hMulAutCyc : IsCyclic (MulAut A) := by
    have e : MulAut A ≃* (ZMod (Nat.card A))ˣ := IsCyclic.mulAutMulEquiv A
    rw [hm] at e
    haveI : IsCyclic (ZMod (p ^ m))ˣ :=
      ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 m
    exact isCyclic_of_surjective e.symm e.symm.surjective
  -- `ker (conjNormal) = C_R(A) = A`.
  have hker : (MulAut.conjNormal (H := A)).ker = A := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg
      rw [← hself, Subgroup.mem_centralizer_iff]
      intro h hh
      have key : g * h * g⁻¹ = h := by
        have h1 : (MulAut.conjNormal (H := A) g) ⟨h, hh⟩ = ⟨h, hh⟩ := by rw [hg]; rfl
        calc g * h * g⁻¹ = ((MulAut.conjNormal (H := A) g ⟨h, hh⟩ : A) : R) :=
              (MulAut.conjNormal_apply g ⟨h, hh⟩).symm
          _ = ((⟨h, hh⟩ : A) : R) := by rw [h1]
          _ = h := rfl
      exact (mul_inv_eq_iff_eq_mul.mp key).symm
    · intro hg
      rw [← hself, Subgroup.mem_centralizer_iff] at hg
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      have hc := hg (h : R) h.2
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
      rfl
  -- `R/A ≅ range (conjNormal) ≤ MulAut A` is cyclic.
  haveI hker_cyc : IsCyclic (R ⧸ (MulAut.conjNormal (H := A)).ker) := by
    have e := QuotientGroup.quotientKerEquivRange (MulAut.conjNormal (H := A))
    haveI : IsCyclic (MulAut.conjNormal (H := A)).range := inferInstance
    exact isCyclic_of_surjective e.symm e.symm.surjective
  haveI hQcyc : IsCyclic (R ⧸ A) :=
    isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hker)
      (QuotientGroup.quotientMulEquivOfEq hker).surjective
  exact ⟨A, hAn, hAcyc, hQcyc⟩

end OddOrder.GroupTheory
