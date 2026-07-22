/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.TISubset

/-!
# The `(6.7)` central-character congruence for a normal Hall TI-subgroup

This is the **Hall analogue** of the Sylow congruence `peterfalvi_67`
(`ClassSumAlgebra.lean`) / `peterfalvi_67_of_odd` (`SylowTICongruence.lean`).
Peterfalvi's Appendix IV, step (7), reuses the (6.7) class-algebra congruence
verbatim, but with the modulus `|Q|` for a **normal Hall subgroup** `Q ⊴ H`
whose nonidentity elements form a TI-subset of `G` (bound `H`), rather than a
Sylow `p`-subgroup.

The entire (6.7.2)/(6.7.3) machinery is modulus-agnostic and lives in
`ClassSumCongruence`/`ClassSumAlgebra`: the general
`centralCharacterOfRep_classSum_mul_cong` takes the class-sum divisibility as a
hypothesis, the collapse `centralCharacterOfRep_sum_inZ_eq_identity_add_nonidentity`
is a pure identity, and `peterfalvi_673` is pure algebraic-integer arithmetic.
Only two ingredients are Sylow-specific in the original:

* the **fixed-point-free** action of `P` on the pair set (which gives
  `|P| ∣ a_{ijs}`), proved from the `p`-element structure — here replaced by
  `fixedPointFree_classPair_hall`, which uses the **Hall** containment
  "a `π(Q)`-element of `H` lies in `Q`" (`mem_of_orderOf_coprime_relindex`);
* the coprimality `(|C₁|, |P|) = 1` — for `Q` it comes from `Q ⊆ C_G(z)`
  (supplied by the caller).

`fixedPointFree_classPair_hall` is the reusable crux; the assembly
`peterfalvi_67_hall` mirrors `peterfalvi_67` with `P ↝ Q`, `N_G(P) ↝ H`.
-/

namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra
open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **A `π(Q)`-element of `H` lies in the normal Hall subgroup `Q ⊴ H`.**  If
`Q.subgroupOf H` is normal and `y ∈ H` has order coprime to the index
`[H : Q] = |H ⧸ Q|`, then `y ∈ Q`: the image of `y` in `H ⧸ Q` has order
dividing both `orderOf y` and `|H ⧸ Q|`, hence order `1`. -/
theorem mem_of_orderOf_coprime_relindex {H Q : Subgroup G} [Finite ↥H]
    (hQnormal : (Q.subgroupOf H).Normal) {y : G} (hyH : y ∈ H)
    (hcop : Nat.Coprime (orderOf y) (Nat.card (↥H ⧸ Q.subgroupOf H))) :
    y ∈ Q := by
  set N : Subgroup ↥H := Q.subgroupOf H with hN
  set yy : ↥H := ⟨y, hyH⟩ with hyy
  have hyyord : orderOf yy = orderOf y := Subgroup.orderOf_mk y hyH
  have h1 : orderOf (QuotientGroup.mk' N yy) ∣ orderOf yy := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h2 : orderOf (QuotientGroup.mk' N yy) ∣ Nat.card (↥H ⧸ N) := orderOf_dvd_natCard _
  have hord1 : orderOf (QuotientGroup.mk' N yy) = 1 := by
    have hg : Nat.gcd (orderOf y) (Nat.card (↥H ⧸ N)) = 1 := hcop
    have : orderOf (QuotientGroup.mk' N yy) ∣ 1 := by
      rw [← hg]; exact Nat.dvd_gcd (hyyord ▸ h1) h2
    exact Nat.dvd_one.mp this
  have hmk1 : QuotientGroup.mk' N yy = 1 := orderOf_eq_one_iff.mp hord1
  have hyN : yy ∈ N := by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk1
  exact Subgroup.mem_subgroupOf.mp hyN

/-- **Hall fixed-point-free action** (Peterfalvi (6.7.1), Hall form).  Let `Q ⊴ H`
be a normal Hall subgroup of `H ≤ G` (`(|Q|, [H:Q]) = 1`) whose nonidentity
elements `Q^# = Q ∖ {1}` form a TI-subset of `G` with bound `H`, and let `Z ≤ Q`
be normal in `H`.  If the classes satisfy `C_i ∩ Z^# ≠ ∅`, `C_j ∩ Z^# ≠ ∅`, and
`C_s ∩ Z = ∅`, then `Q` acts fixed-point-freely on the pair set
`Ω = {(u,v) ∈ C_i × C_j ∣ uv ∈ C_s}`.

The argument mirrors the Sylow case, with the two Sylow steps replaced: an element
`x ∈ Q^#` fixing `(u,v)` centralizes `u, v`, so `u, v ∈ C_G(x) ⊆ H`
(`IsTISubset.centralizer_le`); each of `u, v` is `G`-conjugate to a nonidentity
element of `Z ≤ Q`, hence a `π(Q)`-element of `H`, so `u, v ∈ Q`
(`mem_of_orderOf_coprime_relindex`); a second TI application
(`IsTISubset.mem_of_conj_mem_conj`) carries the conjugator into `H`, and `Z ⊴ H`
forces `u, v ∈ Z`, whence `uv ∈ Z` contradicts `C_s ∩ Z = ∅`. -/
theorem fixedPointFree_classPair_hall [Finite G] {H Q Z : Subgroup G}
    (hQH : Q ≤ H) (hZQ : Z ≤ Q)
    (hQnormal : (Q.subgroupOf H).Normal) (hZnormal : (Z.subgroupOf H).Normal)
    (hti : IsTISubset ((Q : Set G) \ {1}) H)
    (hHall : Nat.Coprime (Nat.card ↥Q) (Nat.card (↥H ⧸ Q.subgroupOf H)))
    {Ci Cj Cs : ConjClasses G}
    (hCi : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Ci)
    (hCj : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Cj)
    (hCs : ∀ w : G, ConjClasses.mk w = Cs → w ∉ Z) :
    ∀ x : (Q : Subgroup G), (x : G) ≠ 1 → ∀ q : ClassPair Ci Cj Cs, x • q ≠ q := by
  classical
  -- `Z ≤ H`, and `Z ⊴ H` read at the `G` level.
  have hZH : ∀ a : G, a ∈ Z → a ∈ H := fun a ha => hQH (hZQ ha)
  have hZconj : ∀ c : G, c ∈ H → ∀ a : G, a ∈ Z → c * a * c⁻¹ ∈ Z := by
    intro c hc a ha
    have := hZnormal.conj_mem ⟨a, hZH a ha⟩ ha ⟨c, hc⟩
    simpa [Subgroup.mem_subgroupOf] using this
  intro x hx q hfix
  obtain ⟨⟨u, v⟩, hq⟩ := q
  obtain ⟨hqi, hqj, hqs⟩ := hq
  set xg : G := (x : G) with hxg
  have hcoe := congrArg (Subtype.val) hfix
  rw [classPairSMul_coe] at hcoe
  simp only [Prod.mk.injEq] at hcoe
  obtain ⟨hxu, hxv⟩ := hcoe
  have hxA : xg ∈ ((Q : Set G) \ {1}) := ⟨x.2, by simpa [hxg] using hx⟩
  -- Anything centralizing `xg ∈ Q^#` lands in `H` (TI).
  have hcentH : ∀ y : G, xg * y * xg⁻¹ = y → y ∈ H := by
    intro y hy
    have hyc : y ∈ Subgroup.centralizer ({xg} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun g hg => by
        rw [Set.mem_singleton_iff] at hg; subst hg
        exact mul_inv_eq_iff_eq_mul.mp hy
    exact hti.centralizer_le hxA hyc
  -- The core sub-step: a member `y` centralized by `xg`, conjugate to `z ∈ Z^#`, lies in `Z`.
  have hmem_Z : ∀ {y z : G}, xg * y * xg⁻¹ = y → z ∈ Z → z ≠ 1 → IsConj z y → y ∈ Z := by
    intro y z hxy hzZ hzne hconj
    have hyH : y ∈ H := hcentH y hxy
    have hzQ : z ∈ Q := hZQ hzZ
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hsc : SemiconjBy c z y := mul_inv_eq_iff_eq_mul.mp hc
    -- `y` is a `π(Q)`-element of `H` (conjugate to `z ∈ Z ≤ Q`), hence `y ∈ Q`.
    have hyQ : y ∈ Q := by
      refine mem_of_orderOf_coprime_relindex hQnormal hyH ?_
      have hoz : orderOf y = orderOf z := (SemiconjBy.orderOf_eq c hsc).symm
      rw [hoz]
      have hzdvd : orderOf z ∣ Nat.card ↥Q := by
        rw [← Subgroup.orderOf_mk z hzQ]; exact orderOf_dvd_natCard _
      exact hHall.coprime_dvd_left hzdvd
    have hyne : y ≠ 1 := by
      rintro rfl
      apply hzne
      have : c * z * c⁻¹ = 1 := hc
      simpa [mul_eq_one_iff_eq_inv] using this
    have hyA : y ∈ ((Q : Set G) \ {1}) := ⟨hyQ, by simpa using hyne⟩
    have hzA : z ∈ ((Q : Set G) \ {1}) := ⟨hzQ, by simpa using hzne⟩
    -- `c z c⁻¹ = y = 1·y·1⁻¹`, so the TI conjugator ratio `c ∈ H`; then `Z ⊴ H` gives `y ∈ Z`.
    have hcH : c ∈ H := by
      have hconjeq : c * z * c⁻¹ = (1 : G) * y * (1 : G)⁻¹ := by simpa using hc
      have := hti.mem_of_conj_mem_conj hzA hyA hconjeq
      simpa using this
    have := hZconj c hcH z hzZ
    rwa [hc] at this
  -- Apply to `u`, `v`; then `u·v ∈ Z` contradicts `C_s ∩ Z = ∅`.
  obtain ⟨zi, hziZ, hzine, hzic⟩ := hCi
  obtain ⟨zj, hzjZ, hzjne, hzjc⟩ := hCj
  have huconj : IsConj zi u := ConjClasses.mk_eq_mk_iff_isConj.mp (hzic.trans hqi.symm)
  have hvconj : IsConj zj v := ConjClasses.mk_eq_mk_iff_isConj.mp (hzjc.trans hqj.symm)
  have huZ : u ∈ Z := hmem_Z hxu hziZ hzine huconj
  have hvZ : v ∈ Z := hmem_Z hxv hzjZ hzjne hvconj
  exact hCs (u * v) hqs (Z.mul_mem huZ hvZ)

/-- **Coprimality atom `(|C₁|, |Q|) = 1`, Hall form** (Peterfalvi (6.7.3)).  If `z` is centralized
by all of `Q` (`Q ⊆ C_G(z)`, e.g. `z ∈ Z(Q)`) and `Q` is a Hall subgroup of `G`
(`(|Q|, [G:Q]) = 1`), then the size `|C₁| = |⟦z⟧|` of the conjugacy class of `z` is coprime to
`|Q|`: `|⟦z⟧| = [G : C_G(z)] ∣ [G : Q]` (`Q ⊆ C_G(z)`), which is coprime to `|Q|`.

Hall analogue of `coprime_card_class_card_sylow`; the Sylow `p ∤ [G:P]` is replaced by the Hall
coprimality `(|Q|, [G:Q]) = 1`. -/
theorem coprime_card_class_card_hall [Finite G] {Q : Subgroup G} {z : G}
    (hQz : Q ≤ Subgroup.centralizer ({z} : Set G))
    (hHall : Nat.Coprime (Nat.card ↥Q) Q.index) :
    IsCoprime (Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } : ℤ)
      (Nat.card ↥Q : ℤ) := by
  have hdvd : Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } ∣ Q.index := by
    rw [card_class_eq_index_centralizer]
    exact Subgroup.index_dvd_of_le hQz
  have hcopN : Nat.Coprime (Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z })
      (Nat.card ↥Q) := Nat.Coprime.coprime_dvd_left hdvd hHall.symm
  exact_mod_cast hcopN.isCoprime

section Assembly
open OddOrder.AlgInt

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

local notation3 "ω" ρ:max C:max => centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩

/-- **Hall collapse of the `(6.7.2)` congruence** (modulus `|Q|`).  Combines the modulus-generic
`centralCharacterOfRep_classSum_mul_cong` (fed the class-sum divisibility from the Hall
fixed-point-free action) with the generic collapse identity
`centralCharacterOfRep_sum_inZ_eq_identity_add_nonidentity`. -/
theorem centralCharacterOfRep_classSum_mul_cong_collapse_hall [Finite G]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] {H Q Z : Subgroup G}
    (hQH : Q ≤ H) (hZQ : Z ≤ Q)
    (hQnormal : (Q.subgroupOf H).Normal) (hZnormal : (Z.subgroupOf H).Normal)
    (hti : IsTISubset ((Q : Set G) \ {1}) H)
    (hHall : Nat.Coprime (Nat.card ↥Q) (Nat.card (↥H ⧸ Q.subgroupOf H)))
    {Ci Cj : ConjClasses G}
    (hCi : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Ci)
    (hCj : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Cj)
    {α : ℂ} (hα : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ω ρ(ConjClasses.mk w) = α) :
    ρ.character 1 * ((ω ρ Ci) * (ω ρ Cj))
      ≡ ρ.character 1 *
          (((classSum Ci * classSum Cj) (1 : G) : ℂ)
            + nonidentityZClassCoeffSum Z Ci Cj * α)
        [ALGMOD (Nat.card ↥Q : ℤ)] := by
  classical
  have hm : ((Nat.card ↥Q : ℤ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℕ) < Nat.card ↥Q := Nat.card_pos
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr hpos.ne'
  have hmul := centralCharacterOfRep_classSum_mul_cong ρ Ci Cj
    (fun Cs => ∃ w : G, ConjClasses.mk w = Cs ∧ w ∈ Z) ?_ hm
  · rw [centralCharacterOfRep_sum_inZ_eq_identity_add_nonidentity ρ Z Ci Cj hα] at hmul
    exact hmul
  · intro Cs hCs
    have hCsZ : ∀ w : G, ConjClasses.mk w = Cs → w ∉ Z := fun w hw hwZ => hCs ⟨w, hw, hwZ⟩
    have hfree := fixedPointFree_classPair_hall hQH hZQ hQnormal hZnormal hti hHall hCi hCj hCsZ
    exact_mod_cast card_dvd_classSumCoeff_of_fixedPointFree (Q : Subgroup G) Ci Cj Cs hfree

/-- **Peterfalvi (6.7), Hall form** (Appendix IV, step (7)).  For a normal Hall subgroup `Q ⊴ H`
whose nonidentity elements are a TI-subset of `G` (bound `H`), a subgroup `Z ≤ Q` normal in `H`,
and an irreducible `ρ` constant on `Z^#` (with the `(6.7)` normalizer–centralizer constancy), the
central-character values collapse and Peterfalvi's `(6.7.3)` arithmetic gives
`ψ(z) ≡ ψ(1) (mod |Q|)`.

Mirror of `peterfalvi_67` with `P ↝ Q`, `N_G(P) ↝ H`; the coprimality `(|C₁|, |Q|) = 1`
(from `Q ⊆ C_G(z)` in the caller) is taken as `hcop`. -/
theorem peterfalvi_67_hall [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {H Q Z : Subgroup G} (hQH : Q ≤ H) (hZQ : Z ≤ Q)
    (hQnormal : (Q.subgroupOf H).Normal) (hZnormal : (Z.subgroupOf H).Normal)
    (hti : IsTISubset ((Q : Set G) \ {1}) H)
    (hHall : Nat.Coprime (Nat.card ↥Q) (Nat.card (↥H ⧸ Q.subgroupOf H)))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hcop : IsCoprime (Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } : ℤ)
      (Nat.card ↥Q : ℤ))
    (hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z)
    (hconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(H ⊓ Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(H ⊓ Subgroup.centralizer ({z} : Set G)))
    (hone : nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z)
      ≡ 1 + nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
        [ALGMOD (Nat.card ↥Q : ℤ)]) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥Q : ℤ)] := by
  classical
  let C₁ : ConjClasses G := ConjClasses.mk z
  let C₂ : ConjClasses G := ConjClasses.mk z⁻¹
  let α : ℂ := ω ρ C₁
  let a₁₁ : ℂ := nonidentityZClassCoeffSum Z C₁ C₁
  let a₁₂ : ℂ := nonidentityZClassCoeffSum Z C₁ C₂
  let q : ℤ := Nat.card { x : G // ConjClasses.mk x = C₁ }
  have hzQ : z ∈ Q := hZQ hzZ
  have hzA : z ∈ (Q : Set G) \ {1} := ⟨hzQ, by simpa using hz1⟩
  have hωconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ω ρ (ConjClasses.mk w) = α := by
    intro w hwZ hw1
    have hwA : w ∈ (Q : Set G) \ {1} := ⟨hZQ hwZ, by simpa using hw1⟩
    rcases hconst hwZ hw1 with ⟨hchar, hcard⟩
    exact centralCharacterOfRep_eq_of_tiSubset_card_eq_of_character_eq ρ hti hwA hzA hcard hchar
  have hC₁ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₁ := ⟨z, hzZ, hz1, rfl⟩
  have hC₂ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₂ :=
    ⟨z⁻¹, Z.inv_mem hzZ, inv_ne_one.mpr hz1, rfl⟩
  have hcoeff11 : (classSum C₁ * classSum C₁) (1 : G) = 0 := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₁ 1 = 0 by simpa [C₁] using classSumCoeff_self_one_eq_zero z hreal]
    norm_num
  have hcoeff12 : (classSum C₁ * classSum C₂) (1 : G) = (q : ℂ) := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₂ 1 = Nat.card { x : G // ConjClasses.mk x = C₁ } by
      simpa [C₁, C₂] using classSumCoeff_self_inv_one_eq_card z]
    simp [q]
  have h11raw := centralCharacterOfRep_classSum_mul_cong_collapse_hall ρ hQH hZQ hQnormal hZnormal
    hti hHall hC₁ hC₁ (α := α) hωconst
  have h12raw := centralCharacterOfRep_classSum_mul_cong_collapse_hall ρ hQH hZQ hQnormal hZnormal
    hti hHall hC₁ hC₂ (α := α) hωconst
  have hωC₂ : ω ρ C₂ = α := by
    simpa [C₂] using hωconst (Z.inv_mem hzZ) (inv_ne_one.mpr hz1)
  have h11 : ρ.character 1 * α ^ 2 ≡ ρ.character 1 * (a₁₁ * α)
      [ALGMOD (Nat.card ↥Q : ℤ)] := by
    simpa [C₁, α, a₁₁, pow_two, hcoeff11] using h11raw
  have h12 : ρ.character 1 * α ^ 2 ≡ ρ.character 1 * ((q : ℂ) + a₁₂ * α)
      [ALGMOD (Nat.card ↥Q : ℤ)] := by
    simpa [C₁, C₂, α, a₁₂, q, pow_two, hcoeff12, hωC₂] using h12raw
  have hsubst : ρ.character 1 * α = (q : ℂ) * ρ.character z := by
    simpa [C₁, α, q] using character_one_mul_centralCharacterOfRep_mk ρ z
  have hψz : IsIntegral ℤ (ρ.character z) := character_isIntegral ρ z
  have hψ1 : IsIntegral ℤ (ρ.character 1) := character_isIntegral ρ 1
  have ha₁₁ : IsIntegral ℤ a₁₁ := by
    simpa [a₁₁, C₁] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₁
  have ha₁₂ : IsIntegral ℤ a₁₂ := by
    simpa [a₁₂, C₁, C₂] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₂
  have hone' : a₁₁ ≡ 1 + a₁₂ [ALGMOD (Nat.card ↥Q : ℤ)] := by
    simpa [a₁₁, a₁₂, C₁, C₂] using hone
  exact peterfalvi_673 hcop hψz hψ1 ha₁₁ ha₁₂ h11 h12 hsubst hone'

end Assembly

end OddOrder.RepresentationTheory
