/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Pointwise.Set.Card
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Isaacs §10A — structure of class-generated index-`p` elementary abelian setups (pp. 295-301)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10 "More Transfer
Theory", §10A 前半: `C_p ≀ C_p` 認識に向けた p-群構造補題群。

* **Lemma 10.3**: `P` p-群, `A ⊴ P` elementary abelian, `|P:A| = p`, `|A| = p^t`
  (`t ≥ 2`), `A` が `P` の一つの共役類で生成されるとき
  (a) `|Z(P)| = p`, (b) `P'` は elementary abelian で `|P'| = p^{t-1}`,
  (c) `P` の nilpotence class は `t`。

「`A` が共役類で生成される」は Lean では `A = Subgroup.normalClosure {a}`
(単元集合の正規閉包 = `a` の共役類が生成する部分群) で表す。

後続 (Thm 10.4 `C_p ≀ C_p` 認識・Cor 10.5) も本 leaf に追加予定。

## 主要依存

* Isaacs Lem 4.6 (cardinality form) =
  `Ch04.card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient`
* Isaacs Thm 4.7 =
  `Ch04.nilpotencyClass_eq_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p_pow`
-/

namespace OddOrder.Isaacs.Ch10

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch04
open scoped commutatorElement
open scoped Pointwise

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

section /- 10A: Lemma 10.3 (pp. 297-298) -/

/-- Pointwise commutativity of an elementary abelian subgroup, coerced to the
ambient group. -/
private lemma elemAb_comm {A : Subgroup P} (hEA : A.IsElementaryAbelian p) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  Subtype.ext_iff.mp (hEA.1 ⟨x, hx⟩ ⟨y, hy⟩)

/-- **Isaacs Lemma 10.3, core computation** (private): under the Lemma 10.3
hypotheses, `Z(P) ≤ A`, `|Z(P)| = p` and `|P'| = p^(t-1)`.

**証明** (Isaacs p.298): まず `Z(P) ≤ A` — さもなくば `z ∈ Z(P) \ A` が
`P ⧸ A` (位数 `p`) を生成し、任意の `x ∈ P` が `x = w · zⁿ` (`w ∈ A`) と書けて
`A ≤ Z(P)` になる。すると `a` の共役類は `{a}` で `A = ⟨a⟩` は位数 ≤ `p`、
`|A| = p^t ≥ p²` に矛盾。次に `⟨a⟩ ⊔ P' ⊴ P` が `a` を含むので正規閉包 `A` を
含み、`A = ⟨a⟩ ⊔ P'`、ゆえに `|A| ≤ p · |P'|`。Lem 4.6 (cardinality) の
`|P'| · |A ⊓ Z(P)| = |A|` と `Z(P) ≤ A`、`|Z(P)| ≥ p` (自明でない p-群の中心)
から `|Z(P)| = p`, `|P'| = p^{t-1}`。 -/
private theorem lemma103_core
    (hP : IsPGroup p P) {A : Subgroup P}
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {t : ℕ} (ht : 2 ≤ t) (hcard : Nat.card A = p ^ t)
    {a : P} (hgen : A = Subgroup.normalClosure {a}) :
    Subgroup.center P ≤ A ∧ Nat.card (Subgroup.center P) = p ∧
      Nat.card (_root_.commutator P) = p ^ (t - 1) := by
  have hp_prime : p.Prime := hp.out
  haveI hA_normal : A.Normal := by rw [hgen]; infer_instance
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := elemAb_comm hEA
  -- a ∈ A and a has order p
  have ha_mem : a ∈ A := hgen.symm ▸ Subgroup.subset_normalClosure (Set.mem_singleton a)
  have ha_ne : a ≠ 1 := by
    rintro rfl
    have hbot : A = ⊥ := by
      rw [hgen]
      refine le_antisymm (Subgroup.normalClosure_le_normal ?_) bot_le
      simp
    rw [hbot, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by omega : t ≠ 0) hp_prime.one_lt
    omega
  have hpow_a : a ^ p = 1 := Subtype.ext_iff.mp (hEA.2 ⟨a, ha_mem⟩)
  have horder : orderOf a = p := by
    rcases hp_prime.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow_a) with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) ha_ne
    · exact h
  haveI : Nontrivial P := ⟨⟨a, 1, ha_ne⟩⟩
  -- the quotient P ⧸ A has order p, hence is cyclic
  have hQcard : Nat.card (P ⧸ A) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  have hCyc : IsCyclic (P ⧸ A) := isCyclic_of_prime_card hQcard
  -- Step 1: Z(P) ≤ A
  have hZle : Subgroup.center P ≤ A := by
    by_contra hnot
    obtain ⟨z, hz_mem, hz_notA⟩ := SetLike.not_le_iff_exists.mp hnot
    -- the image z̄ generates P ⧸ A
    have hz_bar_ne : ((z : P) : P ⧸ A) ≠ 1 := by
      simpa [QuotientGroup.eq_one_iff] using hz_notA
    have hzp_top : Subgroup.zpowers ((z : P) : P ⧸ A) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hQcard]
      have hdvd : orderOf ((z : P) : P ⧸ A) ∣ p := by
        rw [← hQcard]; exact orderOf_dvd_natCard _
      rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | h
      · exact absurd (orderOf_eq_one_iff.mp h1) hz_bar_ne
      · exact h
    -- hence A is central: every x ∈ P is w · zⁿ with w ∈ A, and both commute with A
    have hAcent : A ≤ Subgroup.center P := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro x
      have hx_bar : ((x : P) : P ⧸ A) ∈ Subgroup.zpowers ((z : P) : P ⧸ A) :=
        hzp_top ▸ Subgroup.mem_top _
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx_bar
      have hw_mem : x * (z ^ n)⁻¹ ∈ A := by
        have hone : ((x * (z ^ n)⁻¹ : P) : P ⧸ A) = 1 := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, hn,
            mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp hone
      have hzn : ∀ g : P, g * z ^ n = z ^ n * g := fun g =>
        Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hz_mem n) g
      calc x * y = (x * (z ^ n)⁻¹) * (z ^ n * y) := by group
        _ = (x * (z ^ n)⁻¹) * (y * z ^ n) := by rw [← hzn y]
        _ = ((x * (z ^ n)⁻¹) * y) * z ^ n := by group
        _ = (y * (x * (z ^ n)⁻¹)) * z ^ n := by rw [hAb _ hw_mem _ hy]
        _ = y * x := by group
    -- but then the conjugacy class of a is {a}, so A = ⟨a⟩ is too small
    haveI hz_norm : (Subgroup.zpowers a).Normal := by
      constructor
      intro g hg x
      have hg_center : g ∈ Subgroup.center P :=
        hAcent ((Subgroup.zpowers_le.mpr ha_mem) hg)
      have : x * g * x⁻¹ = g := by
        rw [Subgroup.mem_center_iff.mp hg_center x]; group
      rwa [this]
    have hA_le : A ≤ Subgroup.zpowers a := by
      rw [hgen]
      exact Subgroup.normalClosure_le_normal
        (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a))
    have hle : Nat.card A ≤ p := by
      have h := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hA_le)
      rwa [Nat.card_zpowers, horder] at h
    rw [hcard] at hle
    have : p ^ 1 < p ^ t := Nat.pow_lt_pow_right hp_prime.one_lt (by omega)
    simp only [pow_one] at this
    omega
  -- Step 2: P' ≤ A
  have hG'le : _root_.commutator P ≤ A := by
    letI : CommGroup (P ⧸ A) := IsCyclic.commGroup
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨mul_comm⟩⟩
  -- Step 3: A = ⟨a⟩ ⊔ P' (the sup is normal and contains a, hence the normal closure)
  haveI hH_normal : (Subgroup.zpowers a ⊔ _root_.commutator P).Normal := by
    constructor
    intro h hh g
    have h1 : ⁅g, h⁆ ∈ _root_.commutator P := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
    have heq : g * h * g⁻¹ = ⁅g, h⁆ * h := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) hh
  have hA_eq : A = Subgroup.zpowers a ⊔ _root_.commutator P := by
    refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr ha_mem) hG'le)
    rw [hgen]
    exact Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)))
  -- Step 4: |A| ≤ p · |P'| via the product-set decomposition
  have hcard_le : p ^ t ≤ p * Nat.card (_root_.commutator P) := by
    have hset : ((Subgroup.zpowers a ⊔ _root_.commutator P : Subgroup P) : Set P)
        = (Subgroup.zpowers a : Set P) * (_root_.commutator P : Set P) :=
      Subgroup.mul_normal _ _
    have hmul := Set.natCard_mul_le (s := (Subgroup.zpowers a : Set P))
      (t := (_root_.commutator P : Set P))
    rw [← hset] at hmul
    have hcards : Nat.card ((Subgroup.zpowers a ⊔ _root_.commutator P : Subgroup P) : Set P)
        = p ^ t := by
      rw [SetLike.coe_sort_coe, ← hA_eq, hcard]
    rw [hcards, SetLike.coe_sort_coe, SetLike.coe_sort_coe, Nat.card_zpowers, horder] at hmul
    exact hmul
  -- Step 5: Lemma 4.6 cardinality: |P'| · |Z(P)| = p^t
  have hkey := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
    hAb hCyc
  rw [inf_eq_right.mpr hZle, hcard] at hkey
  -- Step 6: |Z(P)| ≥ p (nontrivial center of a p-group)
  haveI : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  obtain ⟨n, hn_pos, hn⟩ :=
    ((hP.to_subgroup (Subgroup.center P)).nontrivial_iff_card).mp ‹_›
  have hZ_ge : p ≤ Nat.card (Subgroup.center P) := by
    rw [hn]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp_prime.pos (by omega)
  -- Step 7: arithmetic: from x·y = p^t, p^t ≤ p·x, y ≥ p conclude y = p, x = p^(t-1)
  set x := Nat.card (_root_.commutator P) with hx_def
  set y := Nat.card (Subgroup.center P) with hy_def
  have hx_pos : 0 < x := Nat.card_pos
  have hy_le : y ≤ p := by
    have h1 : x * y ≤ x * p := by
      calc x * y = p ^ t := hkey
        _ ≤ p * x := hcard_le
        _ = x * p := mul_comm p x
    exact Nat.le_of_mul_le_mul_left h1 hx_pos
  have hy_eq : y = p := le_antisymm hy_le hZ_ge
  have hx_eq : x = p ^ (t - 1) := by
    have hsucc : p ^ (t - 1) * p = p ^ t := by
      rw [← pow_succ]
      congr 1
      omega
    have : x * p = p ^ (t - 1) * p := by rw [← hsucc] at hkey; rw [← hkey, hy_eq]
    exact Nat.eq_of_mul_eq_mul_right hp_prime.pos this
  exact ⟨hZle, hy_eq, hx_eq⟩

/-- **Isaacs Lemma 10.3(a)**: Let `P` be a `p`-group with a normal elementary
abelian subgroup `A` of index `p` and order `p^t`, `t ≥ 2`, generated by (the
conjugacy class of) a single element, i.e. `A = normalClosure {a}`. Then
`|Z(P)| = p`. -/
theorem card_center_eq_prime_of_elementaryAbelian_normalClosure_index_prime
    (hP : IsPGroup p P) {A : Subgroup P}
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {t : ℕ} (ht : 2 ≤ t) (hcard : Nat.card A = p ^ t)
    {a : P} (hgen : A = Subgroup.normalClosure {a}) :
    Nat.card (Subgroup.center P) = p :=
  (lemma103_core hP hidx hEA ht hcard hgen).2.1

/-- **Isaacs Lemma 10.3 (auxiliary)**: under the Lemma 10.3 hypotheses the
center of `P` is contained in `A`. (Isaacs derives this en route to (a); it is
needed again for Theorem 10.4.) -/
theorem center_le_of_elementaryAbelian_normalClosure_index_prime
    (hP : IsPGroup p P) {A : Subgroup P}
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {t : ℕ} (ht : 2 ≤ t) (hcard : Nat.card A = p ^ t)
    {a : P} (hgen : A = Subgroup.normalClosure {a}) :
    Subgroup.center P ≤ A :=
  (lemma103_core hP hidx hEA ht hcard hgen).1

/-- **Isaacs Lemma 10.3(b), cardinality**: under the Lemma 10.3 hypotheses,
`|P'| = p^(t-1)`. -/
theorem card_commutator_eq_of_elementaryAbelian_normalClosure_index_prime
    (hP : IsPGroup p P) {A : Subgroup P}
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {t : ℕ} (ht : 2 ≤ t) (hcard : Nat.card A = p ^ t)
    {a : P} (hgen : A = Subgroup.normalClosure {a}) :
    Nat.card (_root_.commutator P) = p ^ (t - 1) :=
  (lemma103_core hP hidx hEA ht hcard hgen).2.2

/-- **Isaacs Lemma 10.3(b), elementary abelian**: under the Lemma 10.3
hypotheses, `P'` is elementary abelian (being a subgroup of `A`). -/
theorem isElementaryAbelian_commutator_of_elementaryAbelian_normalClosure_index_prime
    {A : Subgroup P} (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {a : P} (hgen : A = Subgroup.normalClosure {a}) :
    (_root_.commutator P).IsElementaryAbelian p := by
  haveI hA_normal : A.Normal := by rw [hgen]; infer_instance
  have hQcard : Nat.card (P ⧸ A) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  have hCyc : IsCyclic (P ⧸ A) := isCyclic_of_prime_card hQcard
  have hG'le : _root_.commutator P ≤ A := by
    letI : CommGroup (P ⧸ A) := IsCyclic.commGroup
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨mul_comm⟩⟩
  refine ⟨fun x y => Subtype.ext (elemAb_comm hEA _ (hG'le x.2) _ (hG'le y.2)),
    fun x => ?_⟩
  have h : ((x : P)) ^ p = 1 := by
    simpa using congrArg Subtype.val (hEA.2 ⟨(x : P), hG'le x.2⟩)
  exact Subtype.ext (by simpa using h)

/-- **Isaacs Lemma 10.3(c)**: under the Lemma 10.3 hypotheses, the nilpotence
class of `P` is exactly `t`. -/
theorem nilpotencyClass_eq_of_elementaryAbelian_normalClosure_index_prime
    (hP : IsPGroup p P) {A : Subgroup P}
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {t : ℕ} (ht : 2 ≤ t) (hcard : Nat.card A = p ^ t)
    {a : P} (hgen : A = Subgroup.normalClosure {a}) :
    Group.nilpotencyClass P = t := by
  haveI hA_normal : A.Normal := by rw [hgen]; infer_instance
  have hQcard : Nat.card (P ⧸ A) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  have hCyc : IsCyclic (P ⧸ A) := isCyclic_of_prime_card hQcard
  obtain ⟨hZle, hZcard, -⟩ := lemma103_core hP hidx hEA ht hcard hgen
  refine nilpotencyClass_eq_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p_pow
    t hP (elemAb_comm hEA) hCyc hcard ?_
  rw [inf_eq_right.mpr hZle]
  exact hZcard

end

end OddOrder.Isaacs.Ch10
