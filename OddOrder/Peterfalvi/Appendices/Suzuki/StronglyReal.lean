/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionNonSimple

/-!
# Peterfalvi Part II, Ch. I §3: strongly real elements

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, p. 107.

Lemma 3 identifies every strongly real `x` with `x ^ 2 ≠ 1`, up to
conjugacy, as `u * t` for a nonidentity involution `u ∈ Q₀`.  It then proves
that `C_G(x)` has odd order.  The first conclusion follows from transitivity
on triples consisting of two distinct point stabilizers and an involution in
the second.  The parity conclusion is the source's odd-dihedral conjugacy
argument inside `N_G(⟨x⟩)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction
open scoped Pointwise

section /- §3, Lemma 3: generic group lemmas -/

variable {G : Type*} [Group G]

/-- Peterfalvi's terminology: a strongly real element is a product of two
nonidentity involutions. -/
def IsStronglyReal (x : G) : Prop :=
  ∃ u ∈ involutionSet G, ∃ v ∈ involutionSet G, x = u * v

/-- If two involutions normalize a subgroup and their product has odd order,
the standard dihedral conjugator between them also lies in that normalizer. -/
lemma exists_mem_normalizer_conj_of_odd_orderOf
    {X : Subgroup G} {s v : G} (hs : s * s = 1) (hv : v * v = 1)
    (hodd : Odd (orderOf (s * v)))
    (hsN : s ∈ Subgroup.normalizer (X : Set G))
    (hvN : v ∈ Subgroup.normalizer (X : Set G)) :
    ∃ z ∈ Subgroup.normalizer (X : Set G), z⁻¹ * s * z = v := by
  obtain ⟨j, hj⟩ := hodd
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hinv_s : ∀ z ∈ Subgroup.zpowers (s * v), s * z * s = z⁻¹ := by
    intro z hz
    refine OddOrder.Isaacs.Ch02.inv_by_two_involutions hv hs ?_
    rwa [show v * s = (s * v)⁻¹ by rw [mul_inv_rev, hvinv, hsinv],
      Subgroup.zpowers_inv]
  have hkey := hinv_s _
    (Subgroup.pow_mem _ (Subgroup.mem_zpowers (s * v)) (j + 1))
  let z := s * (s * v) ^ (j + 1)
  have hz2 : z * z = 1 := by
    dsimp [z]
    calc
      (s * (s * v) ^ (j + 1)) * (s * (s * v) ^ (j + 1)) =
          (s * (s * v) ^ (j + 1) * s) * (s * v) ^ (j + 1) := by group
      _ = ((s * v) ^ (j + 1))⁻¹ * (s * v) ^ (j + 1) := by rw [hkey]
      _ = 1 := inv_mul_cancel _
  have hexp : (s * v) ^ (j + 1) * (s * v) ^ (j + 1) =
      (s * v) ^ (orderOf (s * v)) * (s * v) := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hzconj : z⁻¹ * s * z = v := by
    rw [inv_eq_of_mul_eq_one_right hz2]
    dsimp [z]
    calc
      (s * (s * v) ^ (j + 1)) * s * (s * (s * v) ^ (j + 1)) =
          s * ((s * v) ^ (j + 1) * (s * s) * (s * v) ^ (j + 1)) := by group
      _ = s * ((s * v) ^ (j + 1) * (s * v) ^ (j + 1)) := by rw [hs, mul_one]
      _ = s * ((s * v) ^ (orderOf (s * v)) * (s * v)) := by rw [hexp]
      _ = s * (s * v) := by rw [pow_orderOf_eq_one, one_mul]
      _ = v := by rw [← mul_assoc, hs, one_mul]
  refine ⟨z, ?_, hzconj⟩
  exact mul_mem hsN (Subgroup.pow_mem _ (mul_mem hsN hvN) _)

/-- An involution which inverts `x` normalizes the cyclic subgroup `⟨x⟩`. -/
lemma mem_normalizer_zpowers_of_inverts
    {x a : G} (ha2 : a * a = 1) (hax : a * x * a = x⁻¹) :
    a ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (a * x * a⁻¹) = Subgroup.zpowers x
  rw [inv_eq_of_mul_eq_one_right ha2, hax, Subgroup.zpowers_inv]

/-- Commuting with a generator is equivalent to centralizing its powers; this
direction supplies membership in `C_G(⟨x⟩)`. -/
lemma mem_centralizer_zpowers_of_commute {x a : G} (hax : Commute a x) :
    a ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact (hax.zpow_right n).eq.symm

/-- If `x = u * t` is not an involution and both factors are involutions,
then the left factor does not centralize `⟨x⟩`. -/
lemma not_mem_centralizer_zpowers_left_factor
    {u t x : G} (hu2 : u * u = 1) (ht2 : t * t = 1)
    (hx : x = u * t) (hx2 : x ^ 2 ≠ 1) :
    u ∉ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  intro huC
  have hcomm : Commute u x := by
    rw [Subgroup.mem_centralizer_iff] at huC
    have h := huC x (Subgroup.mem_zpowers x)
    exact h.symm
  apply hx2
  rw [hx, pow_two]
  have hut : Commute u t := by
    apply mul_right_cancel (b := u)
    calc
      (u * t) * u = u * (u * t) := by simpa [hx] using hcomm.eq.symm
      _ = t := by rw [← mul_assoc, hu2, one_mul]
      _ = (t * u) * u := by rw [mul_assoc, hu2, mul_one]
  calc
    u * t * (u * t) = u * (t * u) * t := by group
    _ = u * (u * t) * t := by rw [hut.eq.symm]
    _ = u * u * (t * t) := by group
    _ = 1 := by rw [hu2, ht2, one_mul]

/-- Conjugate elements have centralizers of the same cardinality. -/
lemma natCard_centralizer_eq_of_isConj {x y : G} (hxy : IsConj x y) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hC := OddOrder.Isaacs.Ch04.centralizer_singleton_conj g x
  rw [hg] at hC
  calc
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) =
        Nat.card ↥((Subgroup.centralizer ({x} : Set G)).map
          (MulAut.conj g : G →* G)) :=
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
    _ = Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
      rw [← hC]

/-- A nontrivial square condition transports across conjugacy. -/
lemma pow_ne_one_of_isConj {x y : G} (hxy : IsConj x y)
    (hx2 : x ^ 2 ≠ 1) : y ^ 2 ≠ 1 := by
  intro hy2
  apply hx2
  apply isConj_one_left.mp
  simpa [hy2] using hxy.pow 2

end

section /- §3, Lemma 3: odd centralizer of the normal form -/

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp

/-- Every involution fixes a point in the doubly transitive action. -/
lemma exists_fixedPoint_of_involution {s : G}
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    ∃ omega : Ω, s • omega = omega := by
  obtain ⟨u, huQ, hu2, hu1⟩ := hyp.exists_involution_mem_Q
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (hyp.isConj_of_involutions hu2 hu1 hs2 hs1)
  refine ⟨g • hyp.basept, ?_⟩
  rw [← hg]
  calc
    (g * u * g⁻¹) • g • hyp.basept = (g * u) • hyp.basept := by
      rw [← mul_smul]
      congr 1
      group
    _ = g • (u • hyp.basept) := mul_smul _ _ _
    _ = g • hyp.basept := by
      rw [hyp.smul_basept_eq_of_mem_H (hyp.Q_le_H huQ)]

/-- Two involutions whose product does not square to one cannot fix the
same point. -/
lemma fixedPoints_ne_of_mul_sq_ne_one {a b : G}
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hab2 : (a * b) ^ 2 ≠ 1) {alpha beta : Ω}
    (ha : a • alpha = alpha) (hb : b • beta = beta) :
    alpha ≠ beta := by
  intro hab
  subst beta
  letI : IsMultiplyPretransitive G Ω 2 := hyp.doubly_transitive
  letI : IsPretransitive G Ω :=
    isPretransitive_of_is_two_pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G alpha hyp.basept
  have haH : g * a * g⁻¹ ∈ hyp.H := by
    rw [hyp.H_def, mem_stabilizer_iff]
    calc
      (g * a * g⁻¹) • hyp.basept =
          (g * a * g⁻¹) • (g • alpha) := by rw [hg]
      _ = (g * a) • alpha := by
        rw [← mul_smul]
        congr 1
        group
      _ = g • (a • alpha) := mul_smul _ _ _
      _ = g • alpha := by rw [ha]
      _ = hyp.basept := hg
  have hbH : g * b * g⁻¹ ∈ hyp.H := by
    rw [hyp.H_def, mem_stabilizer_iff]
    calc
      (g * b * g⁻¹) • hyp.basept =
          (g * b * g⁻¹) • (g • alpha) := by rw [hg]
      _ = (g * b) • alpha := by
        rw [← mul_smul]
        congr 1
        group
      _ = g • (b • alpha) := mul_smul _ _ _
      _ = g • alpha := by rw [hb]
      _ = hyp.basept := hg
  have ha2' : (g * a * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ha2]
    simp
  have hb2' : (g * b * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hb2]
    simp
  have haQ0 : g * a * g⁻¹ ∈ hyp.Q0 := ⟨ha2', haH⟩
  have hbQ0 : g * b * g⁻¹ ∈ hyp.Q0 := ⟨hb2', hbH⟩
  have hcomm := hyp.commute_of_mem_Q0 haQ0 hbQ0
  have habcomm : b * a = a * b := by
    apply conj_injective (x := g)
    simpa only [conj_mul] using hcomm.eq.symm
  apply hab2
  calc
    (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; group
    _ = a * (a * b) * b := by rw [habcomm]
    _ = a ^ 2 * b ^ 2 := by rw [sq, sq]; group
    _ = 1 := by rw [ha2, hb2, mul_one]

/-- Transitivity on Peterfalvi's triples `(H₁,H₂,v)`: an ordered pair
of distinct fixed-point stabilizers and an involution in the second one. -/
lemma exists_smul_pair_and_conj_involution
    {alpha beta alpha' beta' : Ω} {s s' : G}
    (hab : alpha ≠ beta) (hab' : alpha' ≠ beta')
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hsfix : s • beta = beta)
    (hs2' : s' ^ 2 = 1) (hs1' : s' ≠ 1)
    (hsfix' : s' • beta' = beta') :
    ∃ g : G, g • alpha = alpha' ∧ g • beta = beta' ∧
      g * s * g⁻¹ = s' := by
  have hstd : hyp.t • hyp.basept ≠ hyp.basept :=
    hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
  obtain ⟨ga, hga, hgb⟩ :=
    (is_two_pretransitive_iff.mp hyp.doubly_transitive) hab hstd
  obtain ⟨gc, hgc, hgd⟩ :=
    (is_two_pretransitive_iff.mp hyp.doubly_transitive) hab' hstd
  set sa : G := ga * s * ga⁻¹ with hsa
  set sc : G := gc * s' * gc⁻¹ with hsc
  have hsa2 : sa ^ 2 = 1 := by
    rw [hsa, conj_pow, hs2]
    simp
  have hsc2 : sc ^ 2 = 1 := by
    rw [hsc, conj_pow, hs2']
    simp
  have hsa1 : sa ≠ 1 := by
    intro h
    apply hs1
    apply conj_injective (x := ga)
    simpa [hsa] using h
  have hsc1 : sc ≠ 1 := by
    intro h
    apply hs1'
    apply conj_injective (x := gc)
    simpa [hsc] using h
  have hsaH : sa ∈ hyp.H := by
    rw [hyp.H_def, mem_stabilizer_iff, hsa]
    calc
      (ga * s * ga⁻¹) • hyp.basept =
          (ga * s * ga⁻¹) • (ga • beta) := by rw [hgb]
      _ = (ga * s) • beta := by
        rw [← mul_smul]
        congr 1
        group
      _ = ga • (s • beta) := mul_smul _ _ _
      _ = ga • beta := by rw [hsfix]
      _ = hyp.basept := hgb
  have hscH : sc ∈ hyp.H := by
    rw [hyp.H_def, mem_stabilizer_iff, hsc]
    calc
      (gc * s' * gc⁻¹) • hyp.basept =
          (gc * s' * gc⁻¹) • (gc • beta') := by rw [hgd]
      _ = (gc * s') • beta' := by
        rw [← mul_smul]
        congr 1
        group
      _ = gc • (s' • beta') := mul_smul _ _ _
      _ = gc • beta' := by rw [hsfix']
      _ = hyp.basept := hgd
  have hscmem : sc ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} :=
    ⟨hsc2, hsc1, hscH⟩
  rw [← hyp.image_conj_KSet_eq_involutions_H hsaH hsa2 hsa1] at hscmem
  obtain ⟨k, hkK, hk⟩ := hscmem
  change k⁻¹ * sa * k = sc at hk
  have hkD : k ∈ hyp.D := hkK.1
  have hkinvD : k⁻¹ ∈ hyp.D := hyp.D.inv_mem hkD
  refine ⟨gc⁻¹ * k⁻¹ * ga, ?_, ?_, ?_⟩
  · calc
      (gc⁻¹ * k⁻¹ * ga) • alpha =
          gc⁻¹ • (k⁻¹ • (ga • alpha)) := by simp only [mul_smul]
      _ = gc⁻¹ • (k⁻¹ • (hyp.t • hyp.basept)) := by rw [hga]
      _ = gc⁻¹ • (hyp.t • hyp.basept) := by
        rw [hyp.smul_t_basept_eq_of_mem_D hkinvD]
      _ = alpha' := by rw [← hgc, inv_smul_smul]
  · calc
      (gc⁻¹ * k⁻¹ * ga) • beta =
          gc⁻¹ • (k⁻¹ • (ga • beta)) := by simp only [mul_smul]
      _ = gc⁻¹ • (k⁻¹ • hyp.basept) := by rw [hgb]
      _ = gc⁻¹ • hyp.basept := by
        rw [hyp.smul_basept_eq_of_mem_H (hyp.D_le_H hkinvD)]
      _ = beta' := by rw [← hgd, inv_smul_smul]
  · calc
      (gc⁻¹ * k⁻¹ * ga) * s * (gc⁻¹ * k⁻¹ * ga)⁻¹ =
          gc⁻¹ * (k⁻¹ * (ga * s * ga⁻¹) * k) * gc := by group
      _ = gc⁻¹ * (k⁻¹ * sa * k) * gc := by rw [hsa]
      _ = gc⁻¹ * sc * gc := by rw [hk]
      _ = s' := by rw [hsc]; group

/-- **Peterfalvi Part II, Ch. I §3, Lemma 3**, normal-form clause. -/
theorem exists_isConj_mul_t_of_stronglyReal {x : G}
    (hx : IsStronglyReal x) (hx2 : x ^ 2 ≠ 1) :
    ∃ u : G, u ∈ hyp.Q0 ∧ u ≠ 1 ∧ IsConj x (u * hyp.t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  change a ^ 2 = 1 ∧ a ≠ 1 at ha
  change b ^ 2 = 1 ∧ b ≠ 1 at hb
  obtain ⟨alpha, halpha⟩ :=
    hyp.exists_fixedPoint_of_involution ha.1 ha.2
  obtain ⟨beta, hbeta⟩ :=
    hyp.exists_fixedPoint_of_involution hb.1 hb.2
  have hab : alpha ≠ beta :=
    hyp.fixedPoints_ne_of_mul_sq_ne_one ha.1 hb.1 hx2 halpha hbeta
  obtain ⟨beta', hbeta'⟩ :=
    hyp.exists_fixedPoint_of_involution hyp.t_sq hyp.t_ne_one
  have hbase : hyp.basept ≠ beta' := by
    intro h
    apply hyp.t_not_mem_H
    rw [hyp.H_def, mem_stabilizer_iff]
    rw [← h] at hbeta'
    exact hbeta'
  obtain ⟨g, hgalpha, _hgbeta, hgb⟩ :=
    hyp.exists_smul_pair_and_conj_involution hab hbase
      hb.1 hb.2 hbeta hyp.t_sq hyp.t_ne_one hbeta'
  set u : G := g * a * g⁻¹ with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, conj_pow, ha.1]
    simp
  have hu1 : u ≠ 1 := by
    intro h
    apply ha.2
    apply conj_injective (x := g)
    simpa [hu] using h
  have huH : u ∈ hyp.H := by
    rw [hyp.H_def, mem_stabilizer_iff, hu]
    calc
      (g * a * g⁻¹) • hyp.basept =
          (g * a * g⁻¹) • (g • alpha) := by rw [hgalpha]
      _ = (g * a) • alpha := by
        rw [← mul_smul]
        congr 1
        group
      _ = g • (a • alpha) := mul_smul _ _ _
      _ = g • alpha := by rw [halpha]
      _ = hyp.basept := hgalpha
  refine ⟨u, ⟨hu2, huH⟩, hu1, ?_⟩
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  calc
    g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
      rw [conj_mul]
    _ = u * hyp.t := by rw [hu, hgb]


/-- **Peterfalvi Part II, Ch. I §3, Lemma 3**, parity step.  If
`x = u * t` for a nonidentity involution `u ∈ Q₀` and `x ^ 2 ≠ 1`, then
`C_G(x)` has odd cardinality. -/
theorem centralizer_natCard_odd_of_mem_Q0_mul_t
    {u : G} (huQ0 : u ∈ hyp.Q0) (hu1 : u ≠ 1)
    {x : G} (hx : x = u * hyp.t) (hx2 : x ^ 2 ≠ 1) :
    Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨y, hyC, hy2, hy1⟩ := exists_sq_eq_one_of_even_card heven
  have hy_mul : y * y = 1 := by rw [← pow_two]; exact hy2
  have hu_mul : u * u = 1 := by rw [← pow_two]; exact huQ0.1
  have ht_mul : hyp.t * hyp.t = 1 := by rw [← pow_two]; exact hyp.t_sq
  let X : Subgroup G := Subgroup.zpowers x
  have hycomm : Commute y x :=
    Subgroup.mem_centralizer_singleton_iff.mp hyC
  have hyCX : y ∈ Subgroup.centralizer (X : Set G) :=
    mem_centralizer_zpowers_of_commute hycomm
  have hyNX : y ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _ hyCX
  have huinv : u * x * u = x⁻¹ := by
    rw [hx, mul_inv_rev, hyp.t_inv_eq]
    have huinv' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu_mul
    rw [huinv']
    calc
      u * (u * hyp.t) * u = (u * u) * hyp.t * u := by group
      _ = hyp.t * u := by rw [hu_mul, one_mul]
  have huNX : u ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_zpowers_of_inverts hu_mul huinv
  have htinv : hyp.t * x * hyp.t = x⁻¹ := by
    rw [hx, mul_inv_rev, hyp.t_inv_eq]
    have huinv' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu_mul
    rw [huinv']
    calc
      hyp.t * (u * hyp.t) * hyp.t = hyp.t * u * (hyp.t * hyp.t) := by group
      _ = hyp.t * u := by rw [ht_mul, mul_one]
  have htNX : hyp.t ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_zpowers_of_inverts ht_mul htinv
  have hnotuC : u ∉ Subgroup.centralizer (X : Set G) :=
    not_mem_centralizer_zpowers_left_factor hu_mul ht_mul hx hx2
  have hnottC : hyp.t ∉ Subgroup.centralizer (X : Set G) := by
    intro htC
    have htcomm : Commute hyp.t x := by
      rw [Subgroup.mem_centralizer_iff] at htC
      exact (htC x (Subgroup.mem_zpowers x)).symm
    apply hx2
    rw [hx, pow_two]
    have hut : Commute u hyp.t := by
      apply mul_left_cancel (a := hyp.t)
      calc
        hyp.t * (u * hyp.t) = (u * hyp.t) * hyp.t := by
          simpa [hx] using htcomm.eq
        _ = u := by rw [mul_assoc, ht_mul, mul_one]
        _ = hyp.t * (hyp.t * u) := by rw [← mul_assoc, ht_mul, one_mul]
    calc
      u * hyp.t * (u * hyp.t) = u * (hyp.t * u) * hyp.t := by group
      _ = u * (u * hyp.t) * hyp.t := by rw [hut.eq.symm]
      _ = u * u * (hyp.t * hyp.t) := by group
      _ = 1 := by rw [hu_mul, ht_mul, one_mul]
  have conjugate_into_centralizer
      {a b z : G} (haN : a ∈ Subgroup.normalizer (X : Set G))
      (hbC : b ∈ Subgroup.centralizer (X : Set G))
      (hzN : z ∈ Subgroup.normalizer (X : Set G))
      (hz : z⁻¹ * a * z = b) : a ∈ Subgroup.centralizer (X : Set G) := by
    let N := Subgroup.normalizer (X : Set G)
    let C := Subgroup.centralizer (X : Set G)
    let aN : N := ⟨a, haN⟩
    let bN : N := ⟨b, Subgroup.centralizer_le_normalizer _ hbC⟩
    let zN : N := ⟨z, hzN⟩
    have hbsub : bN ∈ C.subgroupOf N := hbC
    have hconj : zN * bN * zN⁻¹ ∈ C.subgroupOf N :=
      (inferInstance : (C.subgroupOf N).Normal).conj_mem bN hbsub zN
    have hab : zN * bN * zN⁻¹ = aN := by
      apply Subtype.ext
      dsimp [aN, bN, zN]
      rw [← hz]
      group
    rwa [hab] at hconj
  by_cases hyH : y ∈ hyp.H
  · have hodd : Odd (orderOf (y * hyp.t)) :=
      hyp.odd_orderOf_mul_involution hyH hy2 hy1 hyp.t_sq hyp.t_not_mem_H
    obtain ⟨z, hzN, hz⟩ := exists_mem_normalizer_conj_of_odd_orderOf
      hy_mul ht_mul hodd hyNX htNX
    have hzN' : z⁻¹ ∈ Subgroup.normalizer (X : Set G) := inv_mem hzN
    have hz' : (z⁻¹)⁻¹ * hyp.t * z⁻¹ = y := by
      rw [inv_inv, ← hz]
      group
    exact hnottC (conjugate_into_centralizer htNX hyCX hzN' hz')
  · have hodd : Odd (orderOf (u * y)) :=
      hyp.odd_orderOf_mul_involution huQ0.2 huQ0.1 hu1 hy2 hyH
    obtain ⟨z, hzN, hz⟩ := exists_mem_normalizer_conj_of_odd_orderOf
      hu_mul hy_mul hodd huNX hyNX
    exact hnotuC (conjugate_into_centralizer huNX hyCX hzN hz)

/-- **Peterfalvi Part II, Ch. I §3, Lemma 3**, centralizer clause for an
arbitrary strongly real element. -/
theorem centralizer_natCard_odd_of_stronglyReal {x : G}
    (hx : IsStronglyReal x) (hx2 : x ^ 2 ≠ 1) :
    Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  obtain ⟨u, huQ0, hu1, hxu⟩ :=
    hyp.exists_isConj_mul_t_of_stronglyReal hx hx2
  have hut2 : (u * hyp.t) ^ 2 ≠ 1 :=
    pow_ne_one_of_isConj hxu hx2
  rw [natCard_centralizer_eq_of_isConj hxu]
  exact hyp.centralizer_natCard_odd_of_mem_Q0_mul_t huQ0 hu1 rfl hut2

/-- **Peterfalvi Part II, Ch. I §3, Lemma 3.**  A strongly real element
which is not an involution is conjugate to `u * t` with `u ∈ Q₀#`, and its
centralizer has odd cardinality. -/
theorem stronglyReal_normalForm_and_centralizer_odd {x : G}
    (hx : IsStronglyReal x) (hx2 : x ^ 2 ≠ 1) :
    (∃ u : G, u ∈ hyp.Q0 ∧ u ≠ 1 ∧ IsConj x (u * hyp.t)) ∧
      Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  exact ⟨hyp.exists_isConj_mul_t_of_stronglyReal hx hx2,
    hyp.centralizer_natCard_odd_of_stronglyReal hx hx2⟩

end Hypothesis

end


end OddOrder.Peterfalvi.Appendices.Suzuki
