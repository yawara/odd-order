/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import OddOrder.GroupTheory.FrattiniPGroup
import OddOrder.GroupTheory.OmegaSubgroup

/-!
# Homocyclic finite abelian 2-groups

This file isolates the homogeneous cyclic-factor argument from Graham Higman,
*Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 1, p. 83.

If every involution of a finite abelian `2`-group has the same height in the
power filtration, the finite abelian decomposition cannot contain cyclic
factors of different orders.  The main theorem below makes this argument
explicit using the `Agemo` filtration.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

/-- Agemo–Nakayama lifting for a finite commutative `p`-group: if a subgroup
together with the first Agemo layer generates the group, it is already the
whole group. The point is that all `p`-th powers lie in the Frattini subgroup. -/
theorem eq_top_of_sup_agemo_one_eq_top
    {P : Type*} [CommGroup P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {U : Subgroup P}
    (hU : U ⊔ Agemo P p 1 = ⊤) : U = ⊤ := by
  apply frattini_nongenerating
  have hagemo : Agemo P p 1 ≤ frattini P := by
    rw [Agemo, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simpa using IsPGroup.pow_mem_frattini hP x
  apply top_unique
  rw [← hU]
  exact sup_le_sup le_rfl hagemo

/-- A product of cyclic groups of order `2 ^ e` has exponent dividing
`2 ^ e`. -/
theorem pow_two_pow_eq_one_of_equiv_pi_zmod
    {A ι : Type*} [CommGroup A] {e : ℕ}
    (ε : A ≃* ((i : ι) → Multiplicative (ZMod (2 ^ e)))) (x : A) :
    x ^ (2 ^ e) = 1 := by
  apply ε.injective
  rw [map_pow, map_one]
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (ε x i), ← ofAdd_nsmul]
  simp

/-- The `e`-th Agemo layer of a product of cyclic groups of order `2 ^ e`
is trivial. -/
theorem agemo_two_eq_bot_of_equiv_pi_zmod
    {A ι : Type*} [CommGroup A] {e : ℕ}
    (ε : A ≃* ((i : ι) → Multiplicative (ZMod (2 ^ e)))) :
    Agemo A 2 e = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := mem_agemo_iff_of_comm.mp hx
  exact pow_two_pow_eq_one_of_equiv_pi_zmod ε y

/-! ## Successive power layers -/

/-- In `ZMod (2 ^ e)`, an element annihilated by `2 ^ (e - 1)` is twice another element. -/
theorem zmod_two_pow_is_two_nsmul_of_annihilated
    {e : ℕ} (he : 0 < e) (z : ZMod (2 ^ e))
    (hz : (2 ^ (e - 1)) • z = 0) :
    ∃ w : ZMod (2 ^ e), z = 2 • w := by
  have hdiv : 2 ^ e ∣ 2 ^ (e - 1) * z.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    simpa [Nat.cast_mul, nsmul_eq_mul, z.natCast_zmod_val] using hz
  have heq : e = (e - 1) + 1 := by omega
  have hpow : 2 ^ e = 2 ^ (e - 1) * 2 := by
    calc
      2 ^ e = 2 ^ ((e - 1) + 1) := congrArg (2 ^ ·) heq
      _ = 2 ^ (e - 1) * 2 := by simp [pow_add]
  have hdiv2 : 2 ^ (e - 1) * 2 ∣ 2 ^ (e - 1) * z.val := by
    simpa only [hpow] using hdiv
  have hz_even : 2 ∣ z.val := by
    exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ (e - 1))).mp hdiv2
  obtain ⟨q, hq⟩ := hz_even
  refine ⟨q, ?_⟩
  rw [← z.natCast_zmod_val, hq]
  simp [nsmul_eq_mul]

/-- Coordinatewise, an element killed by `2 ^ (e - 1)` in a homocyclic product is a square. -/
theorem pi_zmod_two_pow_is_square_of_annihilated
    {ι : Type*} {e : ℕ} (he : 0 < e)
    (x : ι → Multiplicative (ZMod (2 ^ e)))
    (hx : x ^ (2 ^ (e - 1)) = 1) :
    ∃ y : ι → Multiplicative (ZMod (2 ^ e)), x = y ^ 2 := by
  classical
  have hcoord : ∀ i, (2 ^ (e - 1)) • (x i).toAdd = 0 := by
    intro i
    have hi := congrArg (fun f => (f i).toAdd) hx
    simpa [toAdd_pow] using hi
  choose w hw using fun i =>
    zmod_two_pow_is_two_nsmul_of_annihilated he (x i).toAdd (hcoord i)
  refine ⟨fun i => Multiplicative.ofAdd (w i), ?_⟩
  funext i
  apply Multiplicative.ext
  simpa [toAdd_pow] using hw i

/-- Model calculation for the kernel of the power map between successive Agemo layers. -/
theorem mem_agemo_succ_of_mem_and_layer_pow_eq_one_model
    {ι : Type*} {e s : ℕ} (hs : s < e)
    {x : ι → Multiplicative (ZMod (2 ^ e))}
    (hxmem : x ∈ Agemo (ι → Multiplicative (ZMod (2 ^ e))) 2 s)
    (hxpow : x ^ (2 ^ (e - 1 - s)) = 1) :
    x ∈ Agemo (ι → Multiplicative (ZMod (2 ^ e))) 2 (s + 1) := by
  have he : 0 < e := by omega
  obtain ⟨y, rfl⟩ := (mem_agemo_iff_of_comm).mp hxmem
  have hsum : s + (e - 1 - s) = e - 1 := by omega
  have hmul : 2 ^ s * 2 ^ (e - 1 - s) = 2 ^ (e - 1) := by
    rw [← pow_add, hsum]
  have hypow : y ^ (2 ^ (e - 1)) = 1 := by
    simpa only [← pow_mul, hmul] using hxpow
  obtain ⟨z, hz⟩ := pi_zmod_two_pow_is_square_of_annihilated he y hypow
  apply (mem_agemo_iff_of_comm).mpr
  refine ⟨z, ?_⟩
  rw [hz, ← pow_mul]
  congr 1
  simp [pow_succ, mul_comm]

/-- Transported kernel calculation for a group with a homocyclic `ZMod` product model. -/
theorem mem_agemo_succ_of_mem_and_layer_pow_eq_one
    {A : Type*} [CommGroup A] {ι : Type*} {e s : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (hs : s < e)
    {x : A} (hxmem : x ∈ Agemo A 2 s)
    (hxpow : x ^ (2 ^ (e - 1 - s)) = 1) :
    x ∈ Agemo A 2 (s + 1) := by
  obtain ⟨y, hy⟩ := (mem_agemo_iff_of_comm).mp hxmem
  have hemem : ε x ∈ Agemo (ι → Multiplicative (ZMod (2 ^ e))) 2 s := by
    apply (mem_agemo_iff_of_comm).mpr
    exact ⟨ε y, by simpa [map_pow] using congrArg ε hy⟩
  have hepow : (ε x) ^ (2 ^ (e - 1 - s)) = 1 := by
    simpa [map_pow] using congrArg ε hxpow
  have he_succ :=
    mem_agemo_succ_of_mem_and_layer_pow_eq_one_model hs hemem hepow
  obtain ⟨z, hz⟩ := (mem_agemo_iff_of_comm).mp he_succ
  apply (mem_agemo_iff_of_comm).mpr
  refine ⟨ε.symm z, ?_⟩
  apply ε.injective
  simpa [map_pow] using hz


/-- The power map from the `s`-th Agemo layer onto the last nontrivial layer. -/
def agemoLayerPowHom
    {A : Type*} [CommGroup A] {e s : ℕ} (hs : s < e) :
    ↥(Agemo A 2 s) →* ↥(Agemo A 2 (e - 1)) where
  toFun x := ⟨x.1 ^ (2 ^ (e - 1 - s)), by
    obtain ⟨y, hy⟩ := (mem_agemo_iff_of_comm).mp x.2
    apply (mem_agemo_iff_of_comm).mpr
    refine ⟨y, ?_⟩
    have hsum : s + (e - 1 - s) = e - 1 := by omega
    have hmul : 2 ^ s * 2 ^ (e - 1 - s) = 2 ^ (e - 1) := by
      rw [← pow_add, hsum]
    simp only [hy, ← pow_mul, hmul]⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_pow]

/-- The layer power map is surjective. -/
theorem agemoLayerPowHom_surjective
    {A : Type*} [CommGroup A] {e s : ℕ} (hs : s < e) :
    Function.Surjective (agemoLayerPowHom (A := A) hs) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := (mem_agemo_iff_of_comm).mp hx
  refine ⟨⟨y ^ (2 ^ s), Agemo.mem_of_eq_pow y⟩, ?_⟩
  apply Subtype.ext
  change (y ^ (2 ^ s)) ^ (2 ^ (e - 1 - s)) = x
  have hsum : s + (e - 1 - s) = e - 1 := by omega
  have hmul : 2 ^ s * 2 ^ (e - 1 - s) = 2 ^ (e - 1) := by
    rw [← pow_add, hsum]
  simpa only [← pow_mul, hmul] using hy.symm

/-- In a homocyclic product, the kernel of the layer power map is the next Agemo layer. -/
theorem agemoLayerPowHom_ker_eq_succ
    {A : Type*} [CommGroup A] {ι : Type*} {e s : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (hs : s < e) :
    (agemoLayerPowHom (A := A) hs).ker =
      (Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    apply mem_agemo_succ_of_mem_and_layer_pow_eq_one ε hs x.2
    exact congrArg Subtype.val hx
  · intro hx
    obtain ⟨y, hy⟩ := (mem_agemo_iff_of_comm).mp hx
    apply Subtype.ext
    change x.1 ^ (2 ^ (e - 1 - s)) = 1
    rw [hy, ← pow_mul]
    have hsum : (s + 1) + (e - 1 - s) = e := by omega
    have hmul : 2 ^ (s + 1) * 2 ^ (e - 1 - s) = 2 ^ e := by
      rw [← pow_add, hsum]
    rw [hmul]
    exact pow_two_pow_eq_one_of_equiv_pi_zmod ε y

/-- The quotient of two successive Agemo layers is isomorphic to the last nontrivial layer. -/
noncomputable def agemoSuccQuotientEquivLast
    {A : Type*} [CommGroup A] {ι : Type*} {e s : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (hs : s < e) :
    (↥(Agemo A 2 s) ⧸
      (Agemo A 2 (s + 1)).subgroupOf (Agemo A 2 s)) ≃*
        ↥(Agemo A 2 (e - 1)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (agemoLayerPowHom_ker_eq_succ ε hs).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (agemoLayerPowHom (A := A) hs) (agemoLayerPowHom_surjective hs))

/-- Representative formula for `agemoSuccQuotientEquivLast`. -/
@[simp] theorem agemoSuccQuotientEquivLast_mk
    {A : Type*} [CommGroup A] {ι : Type*} {e s : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (hs : s < e)
    (x : ↥(Agemo A 2 s)) :
    agemoSuccQuotientEquivLast ε hs (QuotientGroup.mk x) =
      agemoLayerPowHom (A := A) hs x := by
  rfl

/-- The ambient successor layer viewed inside the current layer is its first Agemo subgroup. -/
theorem agemo_succ_subgroupOf_eq_agemo_one
    {A : Type*} [CommGroup A] {p s : ℕ} :
    (Agemo A p (s + 1)).subgroupOf (Agemo A p s) =
      Agemo (Agemo A p s) p 1 := by
  apply Subgroup.map_injective (Agemo A p s).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (Agemo.anti (Nat.le_succ s)),
    ← agemo_succ_eq_map_agemo_one]

/-- Ambient Agemo–Nakayama lifting from a generated successive layer to subgroup equality. -/
theorem eq_agemo_of_sup_succ_eq
    {A : Type*} [CommGroup A] [Finite A] {p s : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) {U : Subgroup A}
    (hUle : U ≤ Agemo A p s)
    (hgen : U ⊔ Agemo A p (s + 1) = Agemo A p s) :
    U = Agemo A p s := by
  let M := Agemo A p s
  let U' := U.subgroupOf M
  have hU'top : U' ⊔ Agemo M p 1 = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hUle, ← agemo_succ_eq_map_agemo_one,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have hUeq : U' = ⊤ :=
    eq_top_of_sup_agemo_one_eq_top (hA.to_subgroup M) hU'top
  have hmap := congrArg (fun K : Subgroup M => K.map M.subtype) hUeq
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUle,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap


/-- **Higman, Suzuki 2-groups, Lemma 1 — homogeneous-factor part**: a finite
abelian `2`-group whose involutions all have the same Agemo height is a direct
product of cyclic groups of one common order `2 ^ e`.

The index type may be empty, covering the trivial group; in that case we take
`e = 1`. -/
theorem exists_homocyclic_decomposition_of_involution_heights
    {A : Type*} [CommGroup A] [Finite A]
    (hA : IsPGroup 2 A)
    (hheight : ∀ x y : A, orderOf x = 2 → orderOf y = 2 → ∀ s : ℕ,
      (x ∈ Agemo A 2 s ↔ y ∈ Agemo A 2 s)) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ℕ), 0 < e ∧
      Nonempty (A ≃* ((i : ι) → Multiplicative (ZMod (2 ^ e)))) := by
  classical
  obtain ⟨ι, hι, n, hn_gt, ⟨ε⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  letI : Fintype ι := hι
  let B := (i : ι) → Multiplicative (ZMod (n i))
  have hB : IsPGroup 2 B := hA.of_equiv ε
  have hn_pow : ∀ i : ι, ∃ m : ℕ, 0 < m ∧ n i = 2 ^ m := by
    intro i
    let g : B := Pi.mulSingle i (.ofAdd 1)
    have hgord : orderOf g = n i := by
      simp [g, B, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf,
        ZMod.addOrderOf_one]
    obtain ⟨k, hk⟩ := hB g
    obtain ⟨m, _hmk, hm⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp
        (show n i ∣ 2 ^ k by rw [← hgord]; exact orderOf_dvd_of_pow_eq_one hk)
    have hmpos : 0 < m := by
      by_contra hm0
      have : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst m
      have hgt := hn_gt i
      simp at hm
      omega
    exact ⟨m, hmpos, hm⟩
  choose m hmpos hn using hn_pow
  have hgen_order (i : ι) :
      orderOf (Pi.mulSingle i (.ofAdd 1) : B) = 2 ^ m i := by
    simpa [B, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one] using hn i
  let t : ι → B := fun i =>
    (Pi.mulSingle i (.ofAdd 1) : B) ^ (2 ^ (m i - 1))
  have ht_order (i : ι) : orderOf (t i) = 2 := by
    change orderOf ((Pi.mulSingle i (.ofAdd 1) : B) ^ (2 ^ (m i - 1))) = 2
    have htwo_dvd : 2 ∣ orderOf (Pi.mulSingle i (.ofAdd 1) : B) := by
      rw [hgen_order i]
      exact dvd_pow_self 2 (Nat.ne_of_gt (hmpos i))
    have hord_ne : orderOf (Pi.mulSingle i (.ofAdd 1) : B) ≠ 0 := by
      rw [hgen_order i]
      positivity
    have hexp : orderOf (Pi.mulSingle i (.ofAdd 1) : B) / 2 = 2 ^ (m i - 1) := by
      rw [hgen_order i]
      exact (Nat.pow_sub_one (by norm_num) (Nat.ne_of_gt (hmpos i))).symm
    rw [← hexp]
    exact orderOf_pow_orderOf_div hord_ne htwo_dvd
  have hm_eq : ∀ i j : ι, m i = m j := by
    intro i j
    apply le_antisymm
    · by_contra hnot
      have hji : m j < m i := Nat.lt_of_not_ge hnot
      let xi : A := ε.symm (t i)
      let xj : A := ε.symm (t j)
      have hxi_order : orderOf xi = 2 := by
        simpa [xi] using ht_order i
      have hxj_order : orderOf xj = 2 := by
        simpa [xj] using ht_order j
      have hxi_agemo : xi ∈ Agemo A 2 (m i - 1) := by
        rw [mem_agemo_iff_of_comm]
        refine ⟨ε.symm (Pi.mulSingle i (.ofAdd 1) : B), ?_⟩
        simp [xi, t]
      have hxj_agemo : xj ∈ Agemo A 2 (m i - 1) :=
        (hheight xi xj hxi_order hxj_order (m i - 1)).mp hxi_agemo
      obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hxj_agemo
      have hyB : t j = (ε y) ^ (2 ^ (m i - 1)) := by
        apply ε.symm.injective
        simpa [xj] using hy
      have hyj := congrFun hyB j
      have hpow_one : ((ε y) j) ^ (2 ^ (m i - 1)) = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        refine (orderOf_dvd_natCard ((ε y) j)).trans ?_
        simpa [hn j] using pow_dvd_pow 2 (show m j ≤ m i - 1 by omega)
      have htj_one : t j = 1 := by
        funext k
        by_cases hkj : k = j
        · subst k
          calc
            t j j = ((ε y) ^ (2 ^ (m i - 1))) j := hyj
            _ = ((ε y) j) ^ (2 ^ (m i - 1)) := rfl
            _ = 1 := hpow_one
            _ = (1 : B) j := rfl
        · change ((Pi.mulSingle j (.ofAdd 1) : B) k) ^ (2 ^ (m j - 1)) = 1
          rw [Pi.mulSingle_eq_of_ne hkj, one_pow]
      have hcontra := ht_order j
      rw [htj_one, orderOf_one] at hcontra
      omega
    · by_contra hnot
      have hij : m i < m j := Nat.lt_of_not_ge hnot
      let xi : A := ε.symm (t i)
      let xj : A := ε.symm (t j)
      have hxi_order : orderOf xi = 2 := by simpa [xi] using ht_order i
      have hxj_order : orderOf xj = 2 := by simpa [xj] using ht_order j
      have hxj_agemo : xj ∈ Agemo A 2 (m j - 1) := by
        rw [mem_agemo_iff_of_comm]
        refine ⟨ε.symm (Pi.mulSingle j (.ofAdd 1) : B), ?_⟩
        simp [xj, t]
      have hxi_agemo : xi ∈ Agemo A 2 (m j - 1) :=
        (hheight xj xi hxj_order hxi_order (m j - 1)).mp hxj_agemo
      obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hxi_agemo
      have hyB : t i = (ε y) ^ (2 ^ (m j - 1)) := by
        apply ε.symm.injective
        simpa [xi] using hy
      have hyi := congrFun hyB i
      have hpow_one : ((ε y) i) ^ (2 ^ (m j - 1)) = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        refine (orderOf_dvd_natCard ((ε y) i)).trans ?_
        simpa [hn i] using pow_dvd_pow 2 (show m i ≤ m j - 1 by omega)
      have hti_one : t i = 1 := by
        funext k
        by_cases hki : k = i
        · subst k
          calc
            t i i = ((ε y) ^ (2 ^ (m j - 1))) i := hyi
            _ = ((ε y) i) ^ (2 ^ (m j - 1)) := rfl
            _ = 1 := hpow_one
            _ = (1 : B) i := rfl
        · change ((Pi.mulSingle i (.ofAdd 1) : B) k) ^ (2 ^ (m i - 1)) = 1
          rw [Pi.mulSingle_eq_of_ne hki, one_pow]
      have hcontra := ht_order i
      rw [hti_one, orderOf_one] at hcontra
      omega
  let e : ℕ := max 1 (Finset.univ.sup m)
  have hepos : 0 < e := by simp [e]
  have hne : ∀ i : ι, n i = 2 ^ e := by
    intro i
    rw [hn i]
    congr 1
    have hsup_le : Finset.univ.sup m ≤ m i := by
      apply Finset.sup_le
      intro j _
      exact (hm_eq j i).le
    have hmi_le_sup : m i ≤ Finset.univ.sup m :=
      Finset.le_sup (f := m) (Finset.mem_univ i)
    have hsup : Finset.univ.sup m = m i := le_antisymm hsup_le hmi_le_sup
    have hmone : 1 ≤ m i := hmpos i
    simp [e, hsup, hmone]
  let δ : ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((i : ι) → Multiplicative (ZMod (2 ^ e))) :=
    MulEquiv.piCongrRight fun i =>
      MulEquiv.toAdditive.symm (ZMod.ringEquivCongr (hne i)).toAddEquiv
  exact ⟨ι, hι, e, hepos, ⟨ε.trans δ⟩⟩

/-- **Higman, Suzuki 2-groups, Lemma 1 — homogeneous-factor part**, in its
action-theoretic form: transitivity on the involutions forces a homocyclic
decomposition. -/
theorem exists_homocyclic_decomposition_of_transitive_involutions
    {A X : Type*} [CommGroup A] [Finite A] [Monoid X]
    (hA : IsPGroup 2 A) (phi : X →* MulAut A)
    (htrans : ∀ {x y : A}, orderOf x = 2 → orderOf y = 2 →
      ∃ a : X, phi a x = y) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ℕ), 0 < e ∧
      Nonempty (A ≃* ((i : ι) → Multiplicative (ZMod (2 ^ e)))) := by
  apply exists_homocyclic_decomposition_of_involution_heights hA
  intro x y hx hy s
  exact mem_agemo_iff_of_transitive_orderOf_two phi htrans hx hy

end OddOrder.GroupTheory
