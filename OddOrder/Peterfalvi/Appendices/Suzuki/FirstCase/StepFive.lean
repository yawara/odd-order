/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFour

/-!
# Peterfalvi Part II, Ch. II, step (5): supporting identifications

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (5), pp. 109–110.

Step (5) states: if `F` is not a field — equivalently, `C_Q(P)` is not
abelian — then `F ≅ F_{9,2}` and `Q₁ = 1`.  This leaf builds the two
identifications on which its proof (and the later steps) rest:

* `centralizer_inf_mulEquiv_units`: the book's standing identification
  `C_Q(P) ≅ F^*` — the near-field model of step (2)(b) identifies the `Q`
  of the faithful quotient `C_G(P)/N` with `F^*` (`qEquiv`), and
  `Q ⊓ C_G(P)` maps isomorphically onto that quotient `Q` because the
  kernel `N` lies in `D` and `Q ⊓ D = 1`;
* `Q1_eq_bot_of_card_two_pow`: if `|Q|` is a power of `2` then `Q₁ = 1`
  (the odd factor of the nilpotent group `Q` is trivial) — the final
  inference of step (5) from `|Q| = |C_Q(P)|^p = 8^p` (step (4)).

Everything consuming the near-field model inherits the step (2)(b)
`sorry` (issue 9318) through `exists_affineNearFieldModel`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open Pointwise

/-! ## Group-theoretic helpers for step (5)

Three self-contained inputs: the exponent of a Suzuki `2`-group (Higman —
sorried-cite until the Higman campaign lands it), the center of a
nonabelian group of order `8`, and the cyclicity of odd `p`-subgroups of
near-field unit groups (they act fixed-point-freely on `(F, +)`). -/

section StepFiveHelpers

/-- **Peterfalvi p. 110 (inside step (5)) / Appendix III (Higman)**: a
Suzuki `2`-group has exponent `4` ("`S` is then a Suzuki 2-group and so of
exponent 4").

**Sorried-cite**: the statement is Higman's theorem (a) (Appendix III,
p. 141, `S/Z(S)` and `Z(S) = Ω₁(S)` elementary abelian); the Higman
campaign (`OddOrder/Higman/Suzuki2Groups/**`) is building the proof.
Tracked in issue 2053. -/
theorem pow_four_eq_one_of_isSuzuki2Group {P : Type*} [Group P] [Finite P]
    (hP : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group P) (x : P) :
    x ^ 4 = 1 := by
  sorry

/-- A nonabelian group of order `8` has center of order `2`: the center is
nontrivial (`2`-group), proper (nonabelian), and of index `≠ 2` (a cyclic
central quotient would force commutativity). -/
theorem card_center_eq_two_of_card_eq_eight {T : Type*} [Group T] [Finite T]
    (hcard : Nat.card T = 8) (hnc : ¬ ∀ x y : T, x * y = y * x) :
    Nat.card ↥(Subgroup.center T) = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥(Subgroup.center T) ∣ 8 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card _
  have h2 : IsPGroup 2 T :=
    IsPGroup.of_card (hcard.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
  haveI : Nontrivial T := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcard]; norm_num
  haveI hZnt : Nontrivial ↥(Subgroup.center T) := h2.center_nontrivial
  have hZge : 2 ≤ Nat.card ↥(Subgroup.center T) :=
    Finite.one_lt_card_iff_nontrivial.mpr hZnt
  have hne8 : Nat.card ↥(Subgroup.center T) ≠ 8 := by
    intro h8
    apply hnc
    have htop : Subgroup.center T = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (h8.trans hcard.symm)
    intro x y
    exact Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top y) x
  have hne4 : Nat.card ↥(Subgroup.center T) ≠ 4 := by
    intro h4
    apply hnc
    have hquot : Nat.card (T ⧸ Subgroup.center T) = 2 := by
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center T)
      rw [hcard, h4] at hmul
      omega
    haveI : IsCyclic (T ⧸ Subgroup.center T) := isCyclic_of_prime_card hquot
    have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center T)) (by
        rw [QuotientGroup.ker_mk'])
    exact fun x y => hcomm.is_comm.comm x y
  have hdvd' : Nat.card ↥(Subgroup.center T) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hdvd
  obtain ⟨k, hk3, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  interval_cases k
  · rw [pow_zero] at hkeq
    omega
  · rw [pow_one] at hkeq
    exact hkeq
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hkeq
    exact absurd hkeq hne4
  · rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at hkeq
    exact absurd hkeq hne8

/-- Odd `q`-subgroups of the unit group of a finite near-field are cyclic:
`R` acts fixed-point-freely on `(F, +)` by right multiplication (by the
inverse, to make it a left action), and an odd `p`-group with a
fixed-point-free action on an elementary abelian group is cyclic
([H] Kapitel V, Satz 8.15-adjacent; here
`Huppert.isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian`). -/
theorem isCyclic_odd_pSubgroup_of_nearField_units {F : Type*}
    [NearFields.NearField F] [Finite F] {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    (R : Subgroup Fˣ) (hR : IsPGroup q ↥R) : IsCyclic ↥R := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Nontrivial (Multiplicative F) := inferInstanceAs (Nontrivial F)
  -- the right-multiplication-by-inverse action of `R` on `(F, +)`
  set φ : ↥R →* MulAut (Multiplicative F) :=
    { toFun := fun u => (NearFields.rightMul ((((u : Fˣ))⁻¹ : Fˣ) : F)
        (Units.ne_zero _)).toMultiplicative
      map_one' := by
        ext x
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd x * ((((1 : ↥R) : Fˣ))⁻¹ : Fˣ) =
          Multiplicative.toAdd x
        rw [OneMemClass.coe_one, inv_one, Units.val_one, mul_one]
      map_mul' := fun u v => by
        ext x
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd x * ((((u * v : ↥R) : Fˣ))⁻¹ : Fˣ) =
          (Multiplicative.toAdd x * (((v : Fˣ))⁻¹ : Fˣ)) *
            ((((u : Fˣ))⁻¹ : Fˣ) : F)
        rw [MulMemClass.coe_mul, mul_inv_rev, Units.val_mul, ← mul_assoc] }
    with hφdef
  have hφval : ∀ (u : ↥R) (x : Multiplicative F),
      Multiplicative.toAdd (φ u x) =
        Multiplicative.toAdd x * ((((u : Fˣ))⁻¹ : Fˣ) : F) := fun _ _ => rfl
  -- fixed-point-freeness
  have hfpf : ∀ u : ↥R, u ≠ 1 →
      OddOrder.Isaacs.Ch06.actionFixedBy φ u = ⊥ := by
    intro u hu
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hfix := (OddOrder.Isaacs.Ch06.mem_actionFixedBy).mp hx
    have hfixval : Multiplicative.toAdd x * ((((u : Fˣ))⁻¹ : Fˣ) : F) =
        Multiplicative.toAdd x := by
      rw [← hφval u x, hfix]
    by_contra hxne
    have hx0 : Multiplicative.toAdd x ≠ 0 := fun h0 =>
      hxne (Multiplicative.toAdd.injective h0)
    have hinv1 : ((((u : Fˣ))⁻¹ : Fˣ) : F) = 1 :=
      mul_left_cancel₀ hx0 (hfixval.trans (mul_one _).symm)
    have huinv : ((u : Fˣ))⁻¹ = 1 := Units.ext hinv1
    exact hu (Subtype.ext (inv_eq_one.mp huinv))
  obtain ⟨f, hf, hEA⟩ := NearFields.isElementaryAbelian_multiplicative (F := F)
  exact Huppert.isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian
    hf hR hqodd hEA φ hfpf

/-- **The abstract core of step (5)** (p. 109–110): a finite near-field `F`
whose unit group is nilpotent, of `2`-rank one, with `2`-elements of order
dividing `4`, and noncommutative, has `|F| = 9` (and `|F^*| = 8`).

The unit group decomposes as `F^* = T × O` (normal `2`-complement of the
nilpotent group); the odd part `O` is cyclic (odd `p`-subgroups of `F^*`
act fixed-point-freely on `(F, +)`, `isCyclic_odd_pSubgroup_of_nearField_units`);
noncommutativity pushes into `T`, which is generalized quaternion
([Is] Thm 6.11, 2-rank one) of exponent `4`, hence `Q₈` of order `8`.
Then `Z(F^*) = Z(T) × O` has order `2|O|`, and `T` contains a cyclic
subgroup of order `4`, so `C₄ × O` is cyclic of index `2` in `F^*`;
Appendix C, Proposition 2 (`cyclic_index_two_nearField_classification`)
gives `|F| = r²` with `|Z(F^*)| = r − 1`, and the arithmetic
`8|O| = r² − 1`, `2|O| = r − 1` forces `|O| = 1`, `r = 3`. -/
theorem nearField_card_eq_nine_of_nilpotent_units {F : Type*}
    [NearFields.NearField F] [Finite F]
    (hnil : Group.IsNilpotent Fˣ)
    (h2rank : ∀ E : Subgroup Fˣ, (∀ x ∈ E, x ^ 2 = 1) → Nat.card ↥E ≤ 2)
    (hexp4 : ∀ u : Fˣ, (∃ k : ℕ, orderOf u = 2 ^ k) → u ^ 4 = 1)
    (hnc : ¬ ∀ x y : F, x * y = y * x) :
    Nat.card F = 9 ∧ Nat.card Fˣ = 8 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hnil
  -- the normal `2`-complement `O` and the normal Sylow `2`-subgroup `T`
  obtain ⟨O, hOnorm, hOcompl⟩ :=
    OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent (p := 2) (H := Fˣ)
  obtain ⟨T⟩ : Nonempty (Sylow 2 Fˣ) := inferInstance
  have hcompl : Subgroup.IsComplement' O (T : Subgroup Fˣ) := hOcompl T
  haveI hTnorm : (T : Subgroup Fˣ).Normal := inferInstance
  have hOodd : ¬ 2 ∣ Nat.card ↥O :=
    OddOrder.Isaacs.Ch05.not_dvd_card_of_isComplement'_sylow T hcompl
  have hOpos : 0 < Nat.card ↥O := Nat.card_pos
  -- `O` is cyclic: odd Sylows of `F^*` are cyclic
  haveI hOzg : IsZGroup ↥O := by
    rw [isZGroup_iff]
    intro q hq P'
    haveI : Fact q.Prime := ⟨hq⟩
    rcases eq_or_ne q 2 with rfl | hq2
    · -- the Sylow `2`-subgroup of the odd-order group `O` is trivial
      obtain ⟨k, hk⟩ := P'.isPGroup'.exists_card_eq
      have hdvd : Nat.card ↥(P' : Subgroup ↥O) ∣ Nat.card ↥O :=
        Subgroup.card_subgroup_dvd_card _
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · have h1 : Nat.card ↥(P' : Subgroup ↥O) = 1 := by
          rw [hk, pow_zero]
        rw [Subgroup.eq_bot_of_card_eq _ h1]
        exact isCyclic_of_subsingleton
      · exfalso
        apply hOodd
        refine dvd_trans ?_ hdvd
        rw [hk]
        exact dvd_pow_self 2 hkpos.ne'
    · have hqodd : Odd q := hq.odd_of_ne_two hq2
      have hmap : IsCyclic ↥((P' : Subgroup ↥O).map O.subtype) :=
        isCyclic_odd_pSubgroup_of_nearField_units hq hqodd _
          (P'.isPGroup'.map O.subtype)
      exact isCyclic_of_surjective _
        (Subgroup.equivMapOfInjective (P' : Subgroup ↥O) O.subtype
          O.subtype_injective).symm.surjective
  haveI hOcyc : IsCyclic ↥O := inferInstance
  letI : CommGroup ↥O := hOcyc.commGroup
  -- units are noncommutative
  have hncU : ¬ ∀ u v : Fˣ, u * v = v * u := by
    intro hUcomm
    apply hnc
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · rw [zero_mul, mul_zero]
    rcases eq_or_ne y 0 with rfl | hy
    · rw [mul_zero, zero_mul]
    have h := congrArg Units.val (hUcomm (Units.mk0 x hx) (Units.mk0 y hy))
    simpa using h
  -- elementwise commutation between `O` and `T`
  have hOTcomm : ∀ o t : Fˣ, o ∈ O → t ∈ (T : Subgroup Fˣ) → Commute o t :=
    fun o t ho ht => Subgroup.commute_of_normal_of_disjoint O _ hOnorm hTnorm
      hcompl.disjoint o t ho ht
  -- `T` is noncommutative
  have hTnc : ¬ ∀ a b : ↥(T : Subgroup Fˣ), a * b = b * a := by
    intro hTcomm
    apply hncU
    intro u v
    obtain ⟨⟨ou, tu⟩, hu, -⟩ := hcompl.existsUnique u
    obtain ⟨⟨ov, tv⟩, hv, -⟩ := hcompl.existsUnique v
    have hcomm_oo : Commute (ou : Fˣ) (ov : Fˣ) := by
      have h := mul_comm (⟨(ou : Fˣ), ou.2⟩ : ↥O) ⟨(ov : Fˣ), ov.2⟩
      exact congrArg Subtype.val h
    have hcomm_tt : Commute (tu : Fˣ) (tv : Fˣ) := by
      have h := hTcomm ⟨(tu : Fˣ), tu.2⟩ ⟨(tv : Fˣ), tv.2⟩
      exact congrArg Subtype.val h
    have h1 : Commute (ou : Fˣ) (tv : Fˣ) := hOTcomm _ _ ou.2 tv.2
    have h2 : Commute (tu : Fˣ) (ov : Fˣ) := (hOTcomm _ _ ov.2 tu.2).symm
    have hkey : Commute ((ou : Fˣ) * tu) ((ov : Fˣ) * tv) :=
      Commute.mul_left (hcomm_oo.mul_right h1) (h2.mul_right hcomm_tt)
    calc u * v = ((ou : Fˣ) * tu) * ((ov : Fˣ) * tv) := by rw [hu, hv]
      _ = ((ov : Fˣ) * tv) * ((ou : Fˣ) * tu) := hkey.eq
      _ = v * u := by rw [hu, hv]
  -- `T` is generalized quaternion (2-rank one, [Is] Thm 6.11)
  have hUnique : ∀ K L : Subgroup ↥(T : Subgroup Fˣ),
      Nat.card K = 2 → Nat.card L = 2 → K = L := by
    intro K L hK hL
    by_contra hne
    obtain ⟨E, hEelab, hEcard⟩ :=
      T.isPGroup'.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne
        hK hL hne
    have hle := h2rank (E.map (T : Subgroup Fˣ).subtype) ?_
    · rw [Nat.card_congr (Subgroup.equivMapOfInjective E _
        (Subgroup.subtype_injective _)).toEquiv.symm, hEcard] at hle
      norm_num at hle
    · rintro x ⟨y, hy, rfl⟩
      have h2 := hEelab.pow_eq_one ⟨y, hy⟩
      have hval := congrArg Subtype.val (congrArg Subtype.val h2)
      simpa using hval
  rcases OddOrder.Isaacs.Ch06.isCyclic_or_two_quaternion_of_subgroups_card_prime_unique
      T.isPGroup' hUnique with hTcyc | ⟨-, n, ⟨eqT⟩⟩
  · exfalso
    apply hTnc
    letI := hTcyc.commGroup
    exact fun a b => mul_comm a b
  -- pin `n = 2` via exponent `4`
  have horder_dvd : 2 * n ∣ 4 := by
    have ht4 : (eqT.symm (QuaternionGroup.a 1)) ^ 4 = 1 := by
      set t := eqT.symm (QuaternionGroup.a 1) with htdef
      have h2elt : ∃ k : ℕ, orderOf ((t : Fˣ)) = 2 ^ k := by
        obtain ⟨k, hk⟩ := (T.isPGroup' t)
        have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        exact ⟨j, by rw [Subgroup.orderOf_coe]; exact hj⟩
      have h4 := hexp4 (t : Fˣ) h2elt
      exact Subtype.ext (by simpa using h4)
    have ha4 : (QuaternionGroup.a 1 : QuaternionGroup n) ^ 4 = 1 := by
      have := congrArg eqT ht4
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
    have := orderOf_dvd_of_pow_eq_one ha4
    rwa [QuaternionGroup.orderOf_a_one] at this
  have hn2 : n = 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · norm_num at horder_dvd
    · have hn_le : n ≤ 2 := by
        have h2n := Nat.le_of_dvd (by norm_num) horder_dvd
        omega
      interval_cases n
      · -- `n = 1`: `|T| = 4 = 2²` is commutative, contradiction
        exfalso
        apply hTnc
        have hcard4 : Nat.card ↥(T : Subgroup Fˣ) = 4 := by
          rw [Nat.card_congr eqT.toEquiv, Nat.card_eq_fintype_card,
            QuaternionGroup.card]
        exact fun a b =>
          (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
            (by rw [hcard4]; norm_num)).is_comm.comm a b
      · rfl
  subst hn2
  have hTcard : Nat.card ↥(T : Subgroup Fˣ) = 8 := by
    rw [Nat.card_congr eqT.toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  -- generic: the order of an internal product of disjoint subgroups, the
  -- second normal
  have hprodcard : ∀ A B : Subgroup Fˣ, B.Normal → Disjoint A B →
      Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
    intro A B hBnorm hdisj
    haveI := hBnorm
    rw [← Nat.card_prod]
    apply Nat.card_congr
    refine (Equiv.ofBijective (fun x : ↥A × ↥B =>
      (⟨(x.1 : Fˣ) * (x.2 : Fˣ),
        mul_mem (Subgroup.mem_sup_left x.1.2)
          (Subgroup.mem_sup_right x.2.2)⟩ : ↥(A ⊔ B))) ⟨?_, ?_⟩).symm
    · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab
      have h1 : (a₁ : Fˣ) * b₁ = (a₂ : Fˣ) * b₂ := congrArg Subtype.val hab
      have h2 : (a₂ : Fˣ)⁻¹ * a₁ = (b₂ : Fˣ) * (b₁ : Fˣ)⁻¹ := by
        have h3 := congrArg (fun z => (a₂ : Fˣ)⁻¹ * z * (b₁ : Fˣ)⁻¹) h1
        simpa [mul_assoc] using h3
      have hmemA : (a₂ : Fˣ)⁻¹ * a₁ ∈ A := mul_mem (inv_mem a₂.2) a₁.2
      have hmemB : (a₂ : Fˣ)⁻¹ * a₁ ∈ B := by
        rw [h2]; exact mul_mem b₂.2 (inv_mem b₁.2)
      have hone : (a₂ : Fˣ)⁻¹ * a₁ = 1 := by
        have := hdisj.le_bot ⟨hmemA, hmemB⟩
        rwa [Subgroup.mem_bot] at this
      have ha : a₁ = a₂ := by
        apply Subtype.ext
        rw [← one_mul (a₁ : Fˣ), ← mul_inv_cancel (a₂ : Fˣ), mul_assoc, hone,
          mul_one]
      have hb : b₁ = b₂ := by
        apply Subtype.ext
        have h3 : (b₂ : Fˣ) * (b₁ : Fˣ)⁻¹ = 1 := by rw [← h2, hone]
        rw [← one_mul (b₁ : Fˣ), ← h3, mul_assoc, inv_mul_cancel, mul_one]
      rw [ha, hb]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set Fˣ) * (B : Set Fˣ) := by
        rw [← Subgroup.mul_normal A B]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨⟨a, ha⟩, ⟨b, hb⟩⟩ : ↥A × ↥B), rfl⟩
  -- `O ≤ Z(F^*)`
  have hOle : O ≤ Subgroup.center Fˣ := by
    intro o ho
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨⟨og, tg⟩, hg, -⟩ := hcompl.existsUnique g
    have h1 : Commute (og : Fˣ) o := by
      have h := mul_comm (⟨(og : Fˣ), og.2⟩ : ↥O) ⟨o, ho⟩
      exact congrArg Subtype.val h
    have h2 : Commute o (tg : Fˣ) := hOTcomm _ _ ho tg.2
    calc g * o = ((og : Fˣ) * (tg : Fˣ)) * o := by rw [← hg]
      _ = (og : Fˣ) * ((tg : Fˣ) * o) := mul_assoc _ _ _
      _ = (og : Fˣ) * (o * (tg : Fˣ)) := by rw [← h2.eq]
      _ = ((og : Fˣ) * o) * (tg : Fˣ) := (mul_assoc _ _ _).symm
      _ = (o * (og : Fˣ)) * (tg : Fˣ) := by rw [h1.eq]
      _ = o * ((og : Fˣ) * (tg : Fˣ)) := mul_assoc _ _ _
      _ = o * g := by rw [hg]
  -- `Z(F^*) = (Z(F^*) ⊓ T) ⊔ O`
  have hZeq : Subgroup.center Fˣ =
      (Subgroup.center Fˣ ⊓ (T : Subgroup Fˣ)) ⊔ O := by
    apply le_antisymm
    · intro z hz
      obtain ⟨⟨oz, tz⟩, hzdec, -⟩ := hcompl.existsUnique z
      have hozZ : (oz : Fˣ) ∈ Subgroup.center Fˣ := hOle oz.2
      have htzZ : (tz : Fˣ) ∈ Subgroup.center Fˣ := by
        have h1 : (tz : Fˣ) = (oz : Fˣ)⁻¹ * z := by
          rw [← hzdec, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [h1]
        exact mul_mem (inv_mem hozZ) hz
      have : z = (oz : Fˣ) * tz := hzdec.symm
      rw [this]
      exact mul_mem (Subgroup.mem_sup_right oz.2)
        (Subgroup.mem_sup_left ⟨htzZ, tz.2⟩)
    · exact sup_le inf_le_left hOle
  -- `Z(F^*) ⊓ T` is the center of `T`
  have hZTcard : Nat.card ↥(Subgroup.center Fˣ ⊓ (T : Subgroup Fˣ)) =
      Nat.card ↥(Subgroup.center ↥(T : Subgroup Fˣ)) := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨⟨(x : Fˣ), x.2.2⟩, ?_⟩) ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro t
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp x.2.1 (t : Fˣ)
    · intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : ↥(Subgroup.center ↥(T : Subgroup Fˣ)) =>
        ((z : ↥(T : Subgroup Fˣ)) : Fˣ)) hab
    · rintro ⟨t, ht⟩
      have htZ : (t : Fˣ) ∈ Subgroup.center Fˣ := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨⟨og, tg⟩, hg, -⟩ := hcompl.existsUnique g
        have h1 : Commute (og : Fˣ) (t : Fˣ) := hOTcomm _ _ og.2 t.2
        have h2 : Commute (t : Fˣ) (tg : Fˣ) := by
          have h := Subgroup.mem_center_iff.mp ht ⟨(tg : Fˣ), tg.2⟩
          exact (congrArg Subtype.val h).symm
        calc g * (t : Fˣ) = ((og : Fˣ) * (tg : Fˣ)) * t := by rw [← hg]
          _ = (og : Fˣ) * ((tg : Fˣ) * t) := mul_assoc _ _ _
          _ = (og : Fˣ) * ((t : Fˣ) * tg) := by rw [← h2.eq]
          _ = ((og : Fˣ) * t) * (tg : Fˣ) := (mul_assoc _ _ _).symm
          _ = ((t : Fˣ) * og) * (tg : Fˣ) := by rw [h1.eq]
          _ = (t : Fˣ) * ((og : Fˣ) * (tg : Fˣ)) := mul_assoc _ _ _
          _ = (t : Fˣ) * g := by rw [hg]
      exact ⟨⟨(t : Fˣ), ⟨htZ, t.2⟩⟩, Subtype.ext (Subtype.ext rfl)⟩
  -- `|Z(F^*)| = 2|O|`
  have hZcard : Nat.card ↥(Subgroup.center Fˣ) = 2 * Nat.card ↥O := by
    have hdisjZT_O : Disjoint (Subgroup.center Fˣ ⊓ (T : Subgroup Fˣ)) O :=
      Disjoint.mono_left inf_le_right hcompl.disjoint.symm
    rw [hZeq, hprodcard _ _ hOnorm hdisjZT_O, hZTcard,
      card_center_eq_two_of_card_eq_eight hTcard hTnc]
  -- the cyclic index-`2` subgroup `C = C₄ × O`
  set tgen : ↥(T : Subgroup Fˣ) := eqT.symm (QuaternionGroup.a 1) with htgendef
  have htgen_ord : orderOf ((tgen : Fˣ)) = 4 := by
    rw [Subgroup.orderOf_coe, htgendef, MulEquiv.orderOf_eq,
      QuaternionGroup.orderOf_a_one]
  set Tc : Subgroup Fˣ := Subgroup.zpowers ((tgen : Fˣ)) with hTcdef
  have hTcle : Tc ≤ (T : Subgroup Fˣ) := by
    rw [hTcdef]
    exact Subgroup.zpowers_le.mpr tgen.2
  have hTccard : Nat.card ↥Tc = 4 := by
    rw [hTcdef, Nat.card_zpowers, htgen_ord]
  have hcop4O : Nat.Coprime (Nat.card ↥Tc) (Nat.card ↥O) := by
    rw [hTccard, show (4 : ℕ) = 2 ^ 2 by norm_num]
    refine Nat.Coprime.pow_left 2 ?_
    rw [Nat.coprime_two_left]
    rcases Nat.even_or_odd (Nat.card ↥O) with he | ho
    · exact absurd he.two_dvd hOodd
    · exact ho
  have hTcOdisj : Disjoint Tc O := Subgroup.disjoint_of_coprime_natCard hcop4O
  set C : Subgroup Fˣ := Tc ⊔ O with hCdef
  have hCcard : Nat.card ↥C = 4 * Nat.card ↥O := by
    rw [hCdef, hprodcard _ _ hOnorm hTcOdisj, hTccard]
  -- `C` is cyclic: its Sylow subgroups are cyclic and it is nilpotent
  haveI hCzg : IsZGroup ↥C := by
    rw [isZGroup_iff]
    intro q hq P'
    haveI : Fact q.Prime := ⟨hq⟩
    rcases eq_or_ne q 2 with rfl | hq2
    · -- a Sylow `2`-subgroup of `C` has order dividing `4`; Klein four is
      -- excluded by the `2`-rank hypothesis, so it is cyclic
      by_contra hnotcyc
      obtain ⟨k, hk⟩ := P'.isPGroup'.exists_card_eq
      have hdvd : Nat.card ↥(P' : Subgroup ↥C) ∣ 4 * Nat.card ↥O := by
        rw [← hCcard]
        exact Subgroup.card_subgroup_dvd_card _
      have hk2 : k ≤ 2 := by
        by_contra hk3
        push_neg at hk3
        have h8dvd : (2 : ℕ) ^ 3 ∣ 4 * Nat.card ↥O := by
          refine dvd_trans (pow_dvd_pow 2 hk3) ?_
          rw [← hk]
          exact hdvd
        obtain ⟨c, hc⟩ := h8dvd
        apply hOodd
        refine ⟨c, ?_⟩
        omega
      interval_cases k
      · apply hnotcyc
        have h1 : Nat.card ↥(P' : Subgroup ↥C) = 1 := by
          rw [hk, pow_zero]
        rw [Subgroup.eq_bot_of_card_eq _ h1]
        exact isCyclic_of_subsingleton
      · apply hnotcyc
        exact isCyclic_of_prime_card (p := 2) (by rw [hk, pow_one])
      · -- order `4` and noncyclic: an elementary abelian four-subgroup of
        -- `F^*`, contradicting the `2`-rank
        have hcard4 : Nat.card ↥(P' : Subgroup ↥C) = 4 := by
          rw [hk]; norm_num
        have hexp2 : ∀ x : ↥(P' : Subgroup ↥C), x ^ 2 = 1 := by
          intro x
          have hdvd4 : orderOf x ∣ 2 ^ 2 := by
            rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hcard4]
            exact orderOf_dvd_natCard x
          have hne4 : orderOf x ≠ 4 := by
            intro h4
            exact hnotcyc (isCyclic_of_orderOf_eq_card x
              (by rw [h4, hcard4]))
          have hord2 : orderOf x ∣ 2 := by
            obtain ⟨j, hj2, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd4
            interval_cases j
            · rw [hjeq]; norm_num
            · rw [hjeq]; norm_num
            · norm_num at hjeq
              exact absurd hjeq hne4
          exact orderOf_dvd_iff_pow_eq_one.mp hord2
        have hle := h2rank ((P' : Subgroup ↥C).map C.subtype) ?_
        · rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
            (Subgroup.subtype_injective _)).toEquiv.symm, hcard4] at hle
          norm_num at hle
        · rintro x ⟨y, hy, rfl⟩
          have h2 := hexp2 ⟨y, hy⟩
          have hval := congrArg Subtype.val (congrArg Subtype.val h2)
          simpa using hval
    · have hqodd : Odd q := hq.odd_of_ne_two hq2
      have hmap : IsCyclic ↥((P' : Subgroup ↥C).map C.subtype) :=
        isCyclic_odd_pSubgroup_of_nearField_units hq hqodd _
          (P'.isPGroup'.map C.subtype)
      exact isCyclic_of_surjective _
        (Subgroup.equivMapOfInjective (P' : Subgroup ↥C) C.subtype
          C.subtype_injective).symm.surjective
  haveI hCcyc : IsCyclic ↥C := inferInstance
  have hCidx : C.index = 2 := by
    have hmul := Subgroup.card_mul_index C
    have hUcard : Nat.card Fˣ = 8 * Nat.card ↥O := by
      have h := hcompl.card_mul_card
      simp only [SetLike.coe_sort_coe] at h
      rw [hTcard] at h
      rw [← h]
      ring
    rw [hCcard, hUcard] at hmul
    have hOne : Nat.card ↥O ≠ 0 := hOpos.ne'
    -- `4m * index = 8m` forces `index = 2`
    have h4 : 4 * Nat.card ↥O * C.index = 4 * Nat.card ↥O * 2 := by
      rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h4
  -- Appendix C, Proposition 2
  rcases NearFields.cyclic_index_two_nearField_classification C hCcyc hCidx
    with hfield | ⟨r, K, instK, instKfin, d, ⟨p', n', hp', hp'odd, hn'pos, hreq⟩,
      hcardK, ⟨e, -⟩, hZr⟩
  · exact absurd hfield hnc
  have hcardF9 : Nat.card F = r ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact hcardK
  have hcardU : Nat.card Fˣ = r ^ 2 - 1 := by
    rw [Nat.card_units, hcardF9]
  have hcardU8 : Nat.card Fˣ = 8 * Nat.card ↥O := by
    have h := hcompl.card_mul_card
    simp only [SetLike.coe_sort_coe] at h
    rw [hTcard] at h
    rw [← h]
    ring
  have hZ2m : r - 1 = 2 * Nat.card ↥O := by
    rw [← hZr]
    exact hZcard
  have hrge3 : 3 ≤ r := by
    rw [hreq]
    have hp3 : 3 ≤ p' := by
      have h2 := hp'.two_le
      rcases Nat.lt_or_ge p' 3 with h | h
      · interval_cases p'
        · exact absurd hp'odd (by norm_num)
      · exact h
    calc (3 : ℕ) ≤ p' := hp3
      _ ≤ p' ^ n' := Nat.le_self_pow hn'pos.ne' p'
  set m := Nat.card ↥O with hmdef
  have hr_eq : r = 2 * m + 1 := by omega
  have h8m : 8 * m = r ^ 2 - 1 := by rw [← hcardU8, hcardU]
  have hexp : r ^ 2 = 4 * (m * m) + 4 * m + 1 := by rw [hr_eq]; ring
  have h2' : 8 * m = 4 * (m * m) + 4 * m := by
    rw [h8m, hexp, Nat.add_sub_cancel]
  have h3' : 4 * (m * m) = 4 * m := by
    have h4 : 4 * (m * m) + 4 * m = 4 * m + 4 * m := by
      rw [← h2']; ring
    exact Nat.add_right_cancel h4
  have hmm : m * m = m := Nat.eq_of_mul_eq_mul_left (by norm_num) h3'
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · omega
    · have hle : 2 * m ≤ m * m := Nat.mul_le_mul_right m h
      rw [hmm] at hle
      omega
  refine ⟨?_, ?_⟩
  · rw [hcardF9, hr_eq, hm1]
    norm_num
  · rw [hcardU8, hm1]

end StepFiveHelpers

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **The identification `C_Q(P) ≅ F^*`** (p. 109, used from step (4) on):
for any near-field model of step (2)(b), the subgroup `Q ⊓ C_G(P)` of `G`
is isomorphic to the unit group `F^*`.

`qEquiv` identifies the quotient group `Q̄ = (Q ⊓ C_G(P)) N/N` with `F^*`;
the projection `Q ⊓ C_G(P) → Q̄` is injective because the kernel `N` lies
in `D_L` (`normalCore_cH_eq_centralizer_cQ`) and `Q ⊓ D = 1`, and it is
surjective because `Q̄` is by definition the image of `Q ⊓ C_G(P)`. -/
theorem centralizer_inf_mulEquiv_units :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∀ {F : Type uG} [NearFields.NearField F]
      (model : NearFields.AffineNearFieldModel fc.rankOneQuotient F),
      Nonempty
        (↥(fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G)) ≃* Fˣ) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro F instF model
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore
    with hNdef
  set M₀ : Subgroup G := fc.toHypothesis.Q ⊓ L with hM₀def
  have hM₀L : M₀ ≤ L := inf_le_right
  have hQbar : fc.rankOneQuotient.Q =
      (fc.toHypothesis.Q.subgroupOf L).map (QuotientGroup.mk' N) := rfl
  have hmemQ : ∀ m : ↥M₀,
      ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)) m ∈
        fc.rankOneQuotient.Q := by
    intro m
    rw [hQbar]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr m.2.1)
  set ι : ↥M₀ →* Fˣ :=
    model.qEquiv.toMonoidHom.comp
      (((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)).codRestrict
        fc.rankOneQuotient.Q hmemQ) with hιdef
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : ι (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L))
        (a * b⁻¹) = 1 := by
      have h2' := model.qEquiv.injective (h1.trans (map_one _).symm)
      exact congrArg Subtype.val h2'
    have h4 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact h2
    have h5 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈
        fc.toHypothesis.D.subgroupOf L := by
      have hND : N ≤ fc.toHypothesis.D.subgroupOf L := by
        rw [hNdef, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
        exact inf_le_left
      exact hND h4
    have h6 : ((a * b⁻¹ : ↥M₀) : G) ∈
        fc.toHypothesis.Q ⊓ fc.toHypothesis.D :=
      ⟨(a * b⁻¹).2.1, Subgroup.mem_subgroupOf.mp h5⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at h6
    exact mul_inv_eq_one.mp (Subtype.ext h6)
  have hιsurj : Function.Surjective ι := by
    intro u
    have hmem : ((model.qEquiv.symm u : ↥fc.rankOneQuotient.Q) :
        ↥L ⧸ N) ∈ (fc.toHypothesis.Q.subgroupOf L).map
          (QuotientGroup.mk' N) := by
      rw [← hQbar]
      exact (model.qEquiv.symm u).2
    obtain ⟨x, hxQL, hx⟩ := hmem
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hxQL, x.2⟩, ?_⟩
    have hval : ι ⟨(x : G), Subgroup.mem_subgroupOf.mp hxQL, x.2⟩
        = model.qEquiv ⟨QuotientGroup.mk' N x, by
            rw [hQbar]; exact Subgroup.mem_map_of_mem _ hxQL⟩ := rfl
    rw [hval]
    have harg : (⟨QuotientGroup.mk' N x, by
          rw [hQbar]; exact Subgroup.mem_map_of_mem _ hxQL⟩ :
        ↥fc.rankOneQuotient.Q) = model.qEquiv.symm u :=
      Subtype.ext hx
    rw [harg, MulEquiv.apply_symm_apply]
  exact ⟨MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩⟩

/-- **The closing inference of step (5)** (p. 110): if `|Q|` is a power of
`2` then the odd factor `Q₁` of the nilpotent group `Q` is trivial
(`Q = S × Q₁` with `2 ∤ |Q₁|`). -/
theorem Q1_eq_bot_of_card_two_pow {n : ℕ}
    (h : Nat.card ↥fc.toHypothesis.Q = 2 ^ n) :
    fc.toHypothesis.Q1 = ⊥ := by
  have hdvd : Nat.card ↥fc.toHypothesis.Q1Subgroup ∣ 2 ^ n :=
    h ▸ Subgroup.card_subgroup_dvd_card fc.toHypothesis.Q1Subgroup
  have hodd : ¬ 2 ∣ Nat.card ↥fc.toHypothesis.Q1Subgroup :=
    fc.toHypothesis.two_not_dvd_card_Q1Subgroup
  have hcop : Nat.Coprime (Nat.card ↥fc.toHypothesis.Q1Subgroup) (2 ^ n) :=
    Nat.Coprime.pow_right n
      (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by
        rcases Nat.even_or_odd (Nat.card ↥fc.toHypothesis.Q1Subgroup) with
          he | ho
        · exact absurd he.two_dvd hodd
        · exact Nat.odd_iff.mp ho)))
  have hone : Nat.card ↥fc.toHypothesis.Q1Subgroup = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hbot : fc.toHypothesis.Q1Subgroup = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hone
  rw [Hypothesis.Q1, hbot, Subgroup.map_bot]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
