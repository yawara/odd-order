/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.GroupTheory.RegularWreathProduct
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.GroupTheory.IsMetacyclic
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.CriticalSubgroup

/-!
# Isaacs §10A — structure of class-generated index-`p` elementary abelian setups (pp. 295-301)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10 "More Transfer
Theory", §10A 前半: `C_p ≀ C_p` 認識に向けた p-群構造補題群。

* **Lemma 10.3**: `P` p-群, `A ⊴ P` elementary abelian, `|P:A| = p`, `|A| = p^t`
  (`t ≥ 2`), `A` が `P` の一つの共役類で生成されるとき
  (a) `|Z(P)| = p`, (b) `P'` は elementary abelian で `|P'| = p^{t-1}`,
  (c) `P` の nilpotence class は `t`。
* **Theorem 10.4** (`nonempty_mulEquiv_wreath_of_noncommProd_conjClass_ne_one`):
  さらに `|Z(P)| = p` で、`A` 内の非中心共役類の積 (`Finset.noncommProd`) が
  非自明なら `P ≅ C_p ≀ C_p` (= `Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)`)。
  証明は (i) 共役類 = `{a^{uⁱ} | i < p}` の列挙、(ii) `T := conj u` の
  `(T-1)`-冪零性と幾何和 `∑ Tⁱ` (Cayley–Hamilton) で `dim A ≥ p`、
  (iii) `Z(P)` の補部分群 `B` (`PRank` の `exists_isComplement'`) で
  `P ↪ Sym(p²)`、(iv) `v_p((p²)!) = p+1` で像が Sylow →
  mathlib `Sylow.mulEquivIteratedWreathProduct`。

「`A` が共役類で生成される」は Lean では `A = Subgroup.normalClosure {a}`
(単元集合の正規閉包 = `a` の共役類が生成する部分群) で表す。

後続 (Cor 10.5 = `exists_surjective_wreath_of_noncommProd_conjClass_ne_one`,
Lem 10.14 = `not_isMetacyclic_wreath`) も本 leaf に実装済み。

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

omit [Finite P] hp in
/-- Pointwise commutativity of an elementary abelian subgroup, coerced to the
ambient group. -/
private lemma elemAb_comm {A : Subgroup P} (hEA : A.IsElementaryAbelian p) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  Subtype.ext_iff.mp (hEA.1 ⟨x, hx⟩ ⟨y, hy⟩)

/-- If `A` is an abelian normal subgroup of prime index in the `p`-group `P` and the
center of `P` is *not* contained in `A`, then `A` is central (so `P` is abelian):
a central element `z ∉ A` generates the quotient `P ⧸ A`, so every `x ∈ P` is
`w · zⁿ` with `w ∈ A`, and both factors commute with `A`. (Shared step of
Lemma 10.3 and Theorem 10.4.) -/
private lemma le_center_of_center_not_le {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hnot : ¬ Subgroup.center P ≤ A) : A ≤ Subgroup.center P := by
  have hp_prime : p.Prime := hp.out
  have hQcard : Nat.card (P ⧸ A) = p := by rw [← Subgroup.index_eq_card]; exact hidx
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
    have hAcent : A ≤ Subgroup.center P := le_center_of_center_not_le hidx hAb hnot
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

section /- 10A: Theorem 10.4 support — the (T−1)-nilpotency argument (pp. 298-299) -/

open Polynomial

variable (p) in
/-- Over `ZMod p` (`p` prime), `(X - 1)^(p-1) = ∑_{i<p} X^i`: both sides times
`X - 1` give `X^p - 1` (freshman's dream / geometric sum), and `(ZMod p)[X]` is
a domain. Used in the proof of Isaacs Thm 10.4. -/
private lemma X_sub_one_pow_pred_eq_geom_sum :
    ((X : (ZMod p)[X]) - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i := by
  have hp1 : 1 ≤ p := hp.out.one_le
  have hpow : ((X : (ZMod p)[X]) - 1) ^ p = X ^ p - 1 := by
    rw [sub_pow_char]; simp
  have hcancel : (((X : (ZMod p)[X]) - 1) ^ (p - 1)) * (X - 1)
      = (∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) * (X - 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hp1, hpow, geom_sum_mul]
  have hX1 : ((X : (ZMod p)[X]) - 1) ≠ 0 := by
    simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
  exact mul_right_cancel₀ hX1 hcancel

/-- **Isaacs Thm 10.4, linear-algebra core**: if `T` is an endomorphism of a
finite-dimensional `ZMod p`-vector space `M` with `T^p = 1` and
`dim M < p`, then `∑_{i<p} T^i = 0`.

**証明** (Isaacs p.299): `N := T - 1` は `N^p = T^p - 1 = 0` (char `p`) で冪零。
Cayley–Hamilton (`IsNilpotent.charpoly_eq_X_pow_finrank`) から `N^{dim M} = 0`、
`dim M ≤ p - 1` ゆえ `N^{p-1} = 0`。一方 `(X-1)^{p-1} = ∑ X^i` を `T` で評価して
`0 = N^{p-1} = ∑ T^i`。 -/
theorem geom_sum_end_eq_zero_of_pow_prime_eq_one_of_finrank_lt
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [Module.Finite (ZMod p) M]
    {T : Module.End (ZMod p) M} (hT : T ^ p = 1)
    (hrank : Module.finrank (ZMod p) M < p) :
    ∑ i ∈ Finset.range p, T ^ i = 0 := by
  have hpoly : ((X : (ZMod p)[X]) - 1) ^ p = X ^ p - 1 := by
    rw [sub_pow_char]; simp
  have hNp : (T - 1) ^ p = 0 := by
    have h := congrArg (aeval T) hpoly
    simp only [map_pow, map_sub, aeval_X, map_one] at h
    rw [h, hT, sub_self]
  have hCH : (T - 1) ^ Module.finrank (ZMod p) M = 0 := by
    have hchar := IsNilpotent.charpoly_eq_X_pow_finrank (φ := T - 1) ⟨p, hNp⟩
    calc (T - 1) ^ Module.finrank (ZMod p) M
        = aeval (T - 1) ((X : (ZMod p)[X]) ^ Module.finrank (ZMod p) M) := by
          rw [map_pow, aeval_X]
      _ = aeval (T - 1) (LinearMap.charpoly (T - 1)) := by rw [hchar]
      _ = 0 := LinearMap.aeval_self_charpoly _
  have hNp1 : (T - 1) ^ (p - 1) = 0 := by
    have hsplit : (T - 1) ^ (p - 1)
        = (T - 1) ^ Module.finrank (ZMod p) M
          * (T - 1) ^ (p - 1 - Module.finrank (ZMod p) M) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [hsplit, hCH, zero_mul]
  have hgeom := congrArg (aeval T) (X_sub_one_pow_pred_eq_geom_sum p)
  simp only [map_pow, map_sub, aeval_X, map_one, map_sum] at hgeom
  rw [← hgeom, hNp1]

/-- **Isaacs Thm 10.4, dimension bound**: if `T^p = 1` on a finite-dimensional
`ZMod p`-vector space `M` and `∑_{i<p} T^i a ≠ 0` for some `a : M`, then
`dim M ≥ p`. (Contrapositive packaging of
`geom_sum_end_eq_zero_of_pow_prime_eq_one_of_finrank_lt` used in Thm 10.4:
the class product of `a` being nontrivial forces `dim A ≥ p`.) -/
theorem finrank_ge_of_geom_sum_apply_ne_zero
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [Module.Finite (ZMod p) M]
    {T : Module.End (ZMod p) M} (hT : T ^ p = 1) {a : M}
    (ha : ∑ i ∈ Finset.range p, (T ^ i) a ≠ 0) :
    p ≤ Module.finrank (ZMod p) M := by
  refine le_of_not_gt fun hlt => ha ?_
  have h0 := geom_sum_end_eq_zero_of_pow_prime_eq_one_of_finrank_lt hT hlt
  calc ∑ i ∈ Finset.range p, (T ^ i) a
      = (∑ i ∈ Finset.range p, T ^ i) a := (LinearMap.sum_apply _ _ _).symm
    _ = 0 := by rw [h0]; rfl

/-- Iterate form of `finrank_ge_of_geom_sum_apply_ne_zero`: for an *additive
endomorphism* `f` of a finite-dimensional `ZMod p`-vector space with `f^[p] = id`
and `∑_{i<p} f^[i] a ≠ 0`, the dimension is at least `p`. (An additive map is
automatically `ZMod p`-linear; stated with `Function.iterate` so that group-side
callers need no `Module.End` coercions under `letI`-bound instances.) -/
theorem finrank_ge_of_iterate_sum_ne_zero
    {M : Type*} [AddCommGroup M] [Finite M] [Module (ZMod p) M]
    (f : M →+ M) (hfp : ∀ x, f^[p] x = x) {a : M}
    (ha : ∑ i ∈ Finset.range p, f^[i] a ≠ 0) :
    p ≤ Module.finrank (ZMod p) M := by
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  set T : Module.End (ZMod p) M := AddMonoidHom.toZModLinearMap p f with hT_def
  have hiter : ∀ (i : ℕ) (x : M), (T ^ i) x = f^[i] x := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [Function.iterate_succ_apply', ← ih, pow_succ', Module.End.mul_apply]
      rfl
  have hTp : T ^ p = 1 := LinearMap.ext fun x => by rw [hiter, hfp]; rfl
  refine finrank_ge_of_geom_sum_apply_ne_zero (a := a) hTp ?_
  simpa only [hiter] using ha

end

section /- Regular wreath product auxiliaries: `C_p ≀ C_p` as `≀ᵣ` (p. 299) -/

/-- `PUnit ≀ᵣ Q ≃* Q`: the regular wreath product with trivial base group is
the acting group. (Auxiliary for identifying `IteratedWreathProduct G 2` with
`G ≀ᵣ G`; mathlib's `Sylow.mulEquivIteratedWreathProduct` produces the
iterated form.) -/
def punitRegularWreathProductMulEquiv (Q : Type*) [Group Q] :
    (PUnit ≀ᵣ Q) ≃* Q where
  toFun := RegularWreathProduct.rightHom
  invFun := RegularWreathProduct.inl
  left_inv w := by ext x; rfl
  right_inv q := rfl
  map_mul' := map_mul _

/-- `IteratedWreathProduct G 2 ≃* G ≀ᵣ G`: the twice-iterated wreath product is
the regular wreath product `G ≀ᵣ G`. -/
def iteratedWreathProductTwoMulEquiv (G : Type*) [Group G] :
    IteratedWreathProduct G 2 ≃* (G ≀ᵣ G) :=
  RegularWreathProduct.congr (punitRegularWreathProductMulEquiv G) (MulEquiv.refl G)

end

section /- 10A: Theorem 10.4 — recognition of `C_p ≀ C_p` (pp. 298-299) -/

open scoped IsMulCommutative

omit [Finite P] in
/-- Conjugates of an element of a normal subgroup remain in the subgroup. -/
private lemma mem_of_isConj_of_mem_normal {A : Subgroup P} [A.Normal] {a b : P}
    (haA : a ∈ A) (hab : IsConj a b) : b ∈ A := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  exact hc ▸ ‹A.Normal›.conj_mem a haA c

/-- Pairwise commutation (in the form required by `Finset.noncommProd`) of the
conjugacy class of an element of an elementary abelian normal subgroup: all
conjugates lie in the subgroup, which is abelian. This discharges the `comm`
argument of the class-product hypothesis in Isaacs Thm 10.4 / Cor 10.5. -/
theorem conjClass_pairwise_commute {A : Subgroup P} [A.Normal]
    (hEA : A.IsElementaryAbelian p) {a : P} (haA : a ∈ A) :
    (((Set.toFinite {b | IsConj a b}).toFinset : Set P)).Pairwise
      (Function.onFun Commute id) := by
  intro x hx y hy _
  rw [Set.Finite.coe_toFinset] at hx hy
  exact elemAb_comm hEA x (mem_of_isConj_of_mem_normal haA hx) y
    (mem_of_isConj_of_mem_normal haA hy)

omit [Finite P] in
/-- If `A` is an abelian subgroup of prime index and `a ∈ A` is noncentral, then
`C_P(a) = A`: the centralizer contains the abelian `A`, is proper (else `a` would be
central), and `A` is maximal (prime index). -/
private lemma centralizer_singleton_eq_of_not_mem_center {A : Subgroup P}
    (hidx : A.index = p) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a : P} (haA : a ∈ A) (haZ : a ∉ Subgroup.center P) :
    Subgroup.centralizer {a} = A := by
  have hp_prime : p.Prime := hp.out
  have hA_le : A ≤ Subgroup.centralizer {a} := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAb x hx a haA
  have hC_ne_top : Subgroup.centralizer {a} ≠ ⊤ := by
    intro htop
    apply haZ
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer {a} := htop ▸ Subgroup.mem_top g
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hg
  have hmul : A.relIndex (Subgroup.centralizer {a}) * (Subgroup.centralizer {a}).index
      = p := by
    rw [Subgroup.relIndex_mul_index hA_le, hidx]
  have hdvd : (Subgroup.centralizer {a}).index ∣ p := Dvd.intro_left _ hmul
  rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | hself
  · exact absurd (Subgroup.index_eq_one.mp h1) hC_ne_top
  · have hrel : A.relIndex (Subgroup.centralizer {a}) = 1 := by
      rw [hself] at hmul
      exact Nat.eq_of_mul_eq_mul_right hp_prime.pos (hmul.trans (one_mul p).symm)
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hA_le

omit [Finite P] in
/-- For `u ∉ A` with `A` normal of prime index `p`, the image of `u` in `P ⧸ A`
has order exactly `p`. -/
private lemma orderOf_mk_eq_of_notMem {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) {u : P} (hu : u ∉ A) :
    orderOf ((u : P) : P ⧸ A) = p := by
  have hp_prime : p.Prime := hp.out
  have hQcard : Nat.card (P ⧸ A) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  have hne : ((u : P) : P ⧸ A) ≠ 1 := by simpa [QuotientGroup.eq_one_iff] using hu
  have hdvd : orderOf ((u : P) : P ⧸ A) ∣ p := by
    rw [← hQcard]; exact orderOf_dvd_natCard _
  rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | h
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h

/-- For `u ∉ A` with `A` normal of prime index `p`: `u ^ k ∈ A ↔ p ∣ k`. -/
private lemma pow_mem_iff_dvd {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) {u : P} (hu : u ∉ A) (k : ℕ) :
    u ^ k ∈ A ↔ p ∣ k := by
  rw [← QuotientGroup.eq_one_iff (u ^ k), QuotientGroup.mk_pow,
    ← orderOf_dvd_iff_pow_eq_one, orderOf_mk_eq_of_notMem hidx hu]

/-- **Isaacs Thm 10.4, class enumeration**: the conjugacy class of `a ∈ A` (`A`
abelian normal of prime index) is `{u^i · a · u^(-i) | i < p}` for any `u ∉ A`:
conjugation by `w · u^i` (`w ∈ A`) agrees with conjugation by `u^i` on `A`. -/
private lemma conjClass_toFinset_eq_image [DecidableEq P] {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a : P} (haA : a ∈ A) {u : P} (hu : u ∉ A) :
    (Set.toFinite {b | IsConj a b}).toFinset
      = Finset.image (fun i => u ^ i * a * (u ^ i)⁻¹) (Finset.range p) := by
  have hp_prime : p.Prime := hp.out
  have horder := orderOf_mk_eq_of_notMem hidx hu
  ext b
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_image]
  constructor
  · intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    -- write c̄ = ū^n in the cyclic quotient
    have htop : Subgroup.zpowers ((u : P) : P ⧸ A) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, horder, ← Subgroup.index_eq_card, hidx]
    have hmem : ((c : P) : P ⧸ A) ∈ Submonoid.powers ((u : P) : P ⧸ A) := by
      rw [mem_powers_iff_mem_zpowers]
      exact htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn⟩ := hmem
    refine ⟨n % p, Finset.mem_range.mpr (Nat.mod_lt _ hp_prime.pos), ?_⟩
    -- w := c · (u^(n % p))⁻¹ lies in A
    have hw_mem : c * (u ^ (n % p))⁻¹ ∈ A := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      rw [← horder, pow_mod_orderOf]
      rw [show ((u : P) : P ⧸ A) ^ n = ((c : P) : P ⧸ A) from hn, mul_inv_cancel]
    -- conjugation by c = w · u^(n%p) agrees with conjugation by u^(n%p) on a
    have hconj_mem : u ^ (n % p) * a * (u ^ (n % p))⁻¹ ∈ A :=
      ‹A.Normal›.conj_mem a haA _
    have hcw : c = (c * (u ^ (n % p))⁻¹) * u ^ (n % p) := by group
    rw [← hc, hcw]
    have hcomm := hAb _ hw_mem _ hconj_mem
    -- (w · u^i) a (w · u^i)⁻¹ = w (u^i a u^(-i)) w⁻¹ = u^i a u^(-i)
    calc u ^ (n % p) * a * (u ^ (n % p))⁻¹
        = (c * (u ^ (n % p))⁻¹) * (u ^ (n % p) * a * (u ^ (n % p))⁻¹)
            * (c * (u ^ (n % p))⁻¹)⁻¹ := by
          rw [hcomm]; group
      _ = ((c * (u ^ (n % p))⁻¹) * u ^ (n % p)) * a
            * (((c * (u ^ (n % p))⁻¹) * u ^ (n % p)))⁻¹ := by group
  · rintro ⟨i, -, rfl⟩
    exact isConj_iff.mpr ⟨u ^ i, rfl⟩

/-- **Isaacs Thm 10.4, class-size step**: the enumeration `i ↦ u^i · a · u^(-i)`
(`i < p`) of the conjugacy class of a *noncentral* `a ∈ A` is injective:
`u^(j-i)` would otherwise centralize `a`, but `C_P(a) = A` and `u^k ∈ A` forces
`p ∣ k`. -/
private lemma conj_pow_injOn {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a : P} (haA : a ∈ A) (haZ : a ∉ Subgroup.center P) {u : P} (hu : u ∉ A) :
    Set.InjOn (fun i => u ^ i * a * (u ^ i)⁻¹) (Finset.range p) := by
  have key : ∀ i j, i ≤ j → j < p →
      u ^ i * a * (u ^ i)⁻¹ = u ^ j * a * (u ^ j)⁻¹ → i = j := by
    intro i j hle hjp heq
    have hk : (u ^ i)⁻¹ * u ^ j = u ^ (j - i) := by
      rw [show u ^ j = u ^ (j - i) * u ^ i by rw [← pow_add, Nat.sub_add_cancel hle]]
      group
    have hcomm : a * u ^ (j - i) = u ^ (j - i) * a := by
      have h2 := congrArg (fun x => (u ^ i)⁻¹ * x * u ^ j) heq
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h2
      calc a * u ^ (j - i) = a * ((u ^ i)⁻¹ * u ^ j) := by rw [hk]
        _ = (u ^ i)⁻¹ * u ^ j * a := by
            have := h2
            group at this ⊢
            simpa [mul_assoc] using this
        _ = u ^ (j - i) * a := by rw [hk]
    have hcent : u ^ (j - i) ∈ Subgroup.centralizer {a} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.symm
    rw [centralizer_singleton_eq_of_not_mem_center hidx hAb haA haZ] at hcent
    have hdvd := (pow_mem_iff_dvd hidx hu _).mp hcent
    have hlt : j - i < p := lt_of_le_of_lt (Nat.sub_le _ _) hjp
    have h0 : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  intro i hi j hj hij
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases le_total i j with hle | hle
  · exact key i j hle hj hij
  · exact (key j i hle hi hij.symm).symm

omit [Finite P] in
/-- A subgroup of prime index is proper: there is an element outside it. -/
lemma exists_notMem_of_index_prime {A : Subgroup P} (hidx : A.index = p) :
    ∃ u : P, u ∉ A := by
  have hA_ne_top : A ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hidx
    exact hp.out.one_lt.ne' hidx.symm
  obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hA_ne_top)
  exact ⟨u, hu⟩

/-- The `Finset.noncommProd` of the conjugacy class of a noncentral `a ∈ A` equals
the list product `∏_{i<p} a^{uⁱ}` for any `u ∉ A` (class enumeration
`conjClass_toFinset_eq_image` + injectivity `conj_pow_injOn`). Shared bridge for
Thm 10.4 and Cor 10.5. -/
private lemma noncommProd_conjClass_eq_list_prod {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {a : P} (haA : a ∈ A) (haZ : a ∉ Subgroup.center P) {u : P} (hu : u ∉ A) :
    (Set.toFinite {b | IsConj a b}).toFinset.noncommProd id
        (conjClass_pairwise_commute hEA haA)
      = ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod := by
  classical
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := elemAb_comm hEA
  have hset : (Set.toFinite {b | IsConj a b}).toFinset
      = ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).toFinset := by
    rw [conjClass_toFinset_eq_image hidx hAb haA hu]
    ext b
    simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset, List.mem_map,
      List.mem_range]
  have hnodup : ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).Nodup := by
    refine List.Nodup.map_on ?_ (List.nodup_range)
    intro i hi j hj hij
    exact conj_pow_injOn hidx hAb haA haZ hu
      (by rw [Finset.coe_range]; exact List.mem_range.mp hi)
      (by rw [Finset.coe_range]; exact List.mem_range.mp hj) hij
  rw [Finset.noncommProd_congr hset (fun _ _ => rfl)]
  rw [Finset.noncommProd_toFinset _ _ _ hnodup, List.map_id]

/-- **Isaacs Thm 10.4, order bound**: if the product `∏_{i<p} a^{u^i}` of the
conjugates of `a ∈ A` by powers of `u ∉ A` is nontrivial, then `|A| = p^m` with
`m ≥ p`: conjugation by `u` is a linear operator `T` on the `F_p`-vector space `A`
with `T^p = 1`, and the nontrivial geometric sum forces `dim A ≥ p`
(`finrank_ge_of_geom_sum_apply_ne_zero`). -/
private lemma exists_card_eq_pow_ge_of_conj_list_prod_ne_one {A : Subgroup P} [A.Normal]
    (hEA : A.IsElementaryAbelian p) {a : P} (haA : a ∈ A) {u : P} (hupA : u ^ p ∈ A)
    (hprodne : ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod ≠ 1) :
    ∃ m : ℕ, p ≤ m ∧ Nat.card A = p ^ m := by
  have hEA' : OddOrder.GroupTheory.IsElementaryAbelian p ↥A := hEA
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := elemAb_comm hEA
  -- the enumeration of conjugates inside ↥A
  have he_mem : ∀ i : ℕ, u ^ i * a * (u ^ i)⁻¹ ∈ A := fun i => ‹A.Normal›.conj_mem a haA _
  set ê : ℕ → ↥A := fun i => ⟨u ^ i * a * (u ^ i)⁻¹, he_mem i⟩ with hê_def
  -- conjugation by u on ↥A, multiplicatively; its iterates are conjugation by u^i
  set g : ↥A →* ↥A := (MulAut.conjNormal u).toMonoidHom with hg_def
  have hg_iter : ∀ (i : ℕ) (x : ↥A),
      g^[i] x = (MulAut.conjNormal (u ^ i) : MulAut ↥A) x := by
    intro i
    induction i with
    | zero =>
      intro x
      rw [Function.iterate_zero_apply, pow_zero, map_one, MulAut.one_apply]
    | succ i ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, pow_succ', map_mul]
      rfl
  have hg_pow : ∀ x : ↥A, g^[p] x = x := by
    intro x
    rw [hg_iter p]
    ext
    rw [MulAut.conjNormal_apply]
    have hc := hAb (u ^ p) hupA ((x : ↥A) : P) x.2
    rw [hc]; group
  -- pass to the additive F_p-vector space
  letI : IsMulCommutative ↥A := IsMulCommutative.of_comm hEA'.comm
  letI : CommGroup ↥A := inferInstance
  letI := hEA'.zmodModule
  haveI : Finite (Additive ↥A) := inferInstanceAs (Finite ↥A)
  -- the product of the conjugates, computed in the abelian ↥A, is nontrivial
  have hprodA : (∏ i ∈ Finset.range p, ê i) ≠ 1 := by
    intro h1
    apply hprodne
    have hlist : ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod
        = A.subtype ((List.range p).map ê).prod := by
      rw [map_list_prod, List.map_map]
      rfl
    have hfin : ((List.range p).map ê).prod = ∏ i ∈ Finset.range p, ê i := by
      rw [Finset.prod_eq_multiset_prod]
      rfl
    rw [hlist, hfin, h1, map_one]
  set f : Additive ↥A →+ Additive ↥A := MonoidHom.toAdditive g with hf_def
  have hf_iter : ∀ (i : ℕ) (x : ↥A),
      f^[i] (Additive.ofMul x) = Additive.ofMul (g^[i] x) := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  have hfp : ∀ y : Additive ↥A, f^[p] y = y := by
    intro y
    have := hf_iter p (Additive.toMul y)
    rw [ofMul_toMul, hg_pow, ofMul_toMul] at this
    exact this
  have hkey : ∑ i ∈ Finset.range p, f^[i] (Additive.ofMul (⟨a, haA⟩ : ↥A)) ≠ 0 := by
    have hsum : ∑ i ∈ Finset.range p, f^[i] (Additive.ofMul (⟨a, haA⟩ : ↥A))
        = Additive.ofMul (∏ i ∈ Finset.range p, ê i) := by
      rw [ofMul_prod]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf_iter i, hg_iter i]
      congr 1
    rw [hsum]
    intro h0
    exact hprodA (Additive.ofMul.injective h0)
  have hrank := finrank_ge_of_iterate_sum_ne_zero f hfp hkey
  refine ⟨Module.finrank (ZMod p) (Additive ↥A), hrank, ?_⟩
  have hpf := FiniteField.pow_finrank_eq_natCard p (Additive ↥A)
  rw [Nat.card_congr Additive.toMul] at hpf
  exact hpf.symm

/-- **Isaacs Thm 10.4, Sylow-embedding half**: let `P` be a `p`-group with
`|Z(P)| = p` and a normal elementary abelian subgroup `A ⊇ Z(P)` of index `p`. If
`|A| = p^m` with `m ≥ p`, then `P ≅ C_p ≀ C_p`.

**証明** (Isaacs p.298): elementary abelian `A` の中で `Z(P)` の補部分群 `B` を取る
(`|P : B| = p²`, `B ∩ Z(P) = 1`)。`P` の非自明正規部分群は中心と交わるので
`core_P(B) = 1`、よって `P ⧸ B` (p² 点) 上の作用は忠実で `P ↪ Sym(p²)`。
`(p²)!` の `p` 進付値は `p + 1` なので `|P| = p^{m+1} ≥ p^{p+1}` から `m = p` かつ
`P` の像は `Sym(p²)` の Sylow `p`-部分群。mathlib の
`Sylow.mulEquivIteratedWreathProduct` で `C_p ≀ C_p` と同型。 -/
private lemma nonempty_mulEquiv_wreath_of_card_pow
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    (hZ : Nat.card (Subgroup.center P) = p) (hZle : Subgroup.center P ≤ A)
    {m : ℕ} (hm : p ≤ m) (hcardA : Nat.card A = p ^ m) :
    Nonempty (P ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))) := by
  have hp_prime : p.Prime := hp.out
  have hEA' : OddOrder.GroupTheory.IsElementaryAbelian p ↥A := hEA
  -- |P| = p^(m+1)
  have hcardP : Nat.card P = p ^ (m + 1) := by
    have h1 := Subgroup.card_mul_index A
    rw [hcardA, hidx] at h1
    rw [← h1, pow_succ]
  -- complement B of Z(P) inside A
  obtain ⟨K, hK⟩ := hEA'.exists_isComplement' ((Subgroup.center P).subgroupOf A)
  set B : Subgroup P := K.map A.subtype with hB_def
  have hcardZA : Nat.card ((Subgroup.center P).subgroupOf A) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv, hZ]
  have hcardK : p * Nat.card K = p ^ m := by
    have h1 := hK.card_mul
    rw [hcardZA, hcardA] at h1
    exact h1
  have hm1 : 1 ≤ m := le_trans hp_prime.one_lt.le hm
  have hcardB : Nat.card B = p ^ (m - 1) := by
    have hBK : Nat.card B = Nat.card K :=
      (Nat.card_congr (Subgroup.equivMapOfInjective K A.subtype
        A.subtype_injective).toEquiv).symm
    have h2 : p * Nat.card K = p * p ^ (m - 1) := by
      rw [hcardK, ← pow_succ']
      congr 1
      omega
    rw [hBK]
    exact Nat.eq_of_mul_eq_mul_left hp_prime.pos h2
  -- |P : B| = p²
  have hBidx : B.index = p ^ 2 := by
    have h1 := Subgroup.card_mul_index B
    rw [hcardB, hcardP] at h1
    have h2 : p ^ (m - 1) * B.index = p ^ (m - 1) * p ^ 2 := by
      rw [h1, ← pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp_prime.pos) h2
  -- B ⊓ Z(P) = ⊥, hence core_P(B) = ⊥
  have hBZ : B ⊓ Subgroup.center P = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxZ⟩
    obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hxB
    have hyZA : y ∈ (Subgroup.center P).subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      show (y : P) ∈ Subgroup.center P
      rw [show ((y : P)) = x from hyx]
      exact hxZ
    have hy_bot : y ∈ ((Subgroup.center P).subgroupOf A) ⊓ K := ⟨hyZA, hyK⟩
    rw [disjoint_iff.mp hK.disjoint] at hy_bot
    have hy1 : y = 1 := Subgroup.mem_bot.mp hy_bot
    rw [Subgroup.mem_bot, ← hyx, hy1]
    rfl
  have hcore : B.normalCore = ⊥ := by
    by_contra hne
    obtain ⟨x, hxN, hxZ, hxne⟩ := exists_mem_center_of_normal_ne_bot hP hne
    have hx_bot : x ∈ B ⊓ Subgroup.center P := ⟨B.normalCore_le hxN, hxZ⟩
    rw [hBZ] at hx_bot
    exact hxne (Subgroup.mem_bot.mp hx_bot)
  -- the (faithful) action of P on the p² cosets of B
  set f : P →* Equiv.Perm (P ⧸ B) := MulAction.toPermHom P (P ⧸ B) with hf_def
  have hf_inj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [← Subgroup.normalCore_eq_ker]
    exact hcore
  have hquot : Nat.card (P ⧸ B) = p ^ 2 := by
    rw [← Subgroup.index_eq_card, hBidx]
  -- the p-part of (p²)! is p^(p+1)
  have hval : (Nat.card (Equiv.Perm (P ⧸ B))).factorization p = p + 1 := by
    rw [Nat.card_perm, hquot,
      ← Nat.multiplicity_eq_factorization hp_prime (Nat.factorial_ne_zero _),
      Nat.Prime.multiplicity_factorial_pow hp_prime]
    simp [Finset.sum_range_succ, Nat.add_comm]
  -- |P| divides (p²)!, forcing m = p
  have hcard_range : Nat.card f.range = p ^ (m + 1) := by
    rw [← hcardP]
    exact (Nat.card_congr (MonoidHom.ofInjective hf_inj).toEquiv).symm
  have hm_eq : m = p := by
    have hdvd : p ^ (m + 1) ∣ Nat.card (Equiv.Perm (P ⧸ B)) := by
      rw [← hcard_range]
      exact Subgroup.card_subgroup_dvd_card _
    have hne : Nat.card (Equiv.Perm (P ⧸ B)) ≠ 0 := by
      rw [Nat.card_perm]
      exact (Nat.factorial_pos _).ne'
    have h1 : m + 1 ≤ p + 1 := by
      rw [← hval]
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp_prime hne).mp hdvd
    omega
  -- the image of P is a Sylow p-subgroup of Sym(p²) ≅ C_p ≀ C_p
  have hcard_syl : Nat.card f.range
      = p ^ (Nat.card (Equiv.Perm (P ⧸ B))).factorization p := by
    rw [hcard_range, hval, hm_eq]
  have e2 := Sylow.mulEquivIteratedWreathProduct p 2 (P ⧸ B) hquot
    (Multiplicative (ZMod p))
    (by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])
    (Sylow.ofCard f.range hcard_syl)
  exact ⟨((MonoidHom.ofInjective hf_inj).trans e2).trans
    (iteratedWreathProductTwoMulEquiv _)⟩

/-- **Isaacs Theorem 10.4** (`C_p ≀ C_p` recognition): let `P` be a `p`-group with a
normal elementary abelian subgroup `A` of index `p` and `|Z(P)| = p`, and suppose
the product of the elements of some noncentral conjugacy class of `P` contained in
`A` is not the identity. Then `P ≅ C_p ≀ C_p`.

The class product is expressed as the `Finset.noncommProd` over the conjugacy class
`{b | IsConj a b}` (whose elements commute pairwise: `conjClass_pairwise_commute`),
and `C_p ≀ C_p` is rendered as `Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)`
(mathlib's regular wreath product). -/
theorem nonempty_mulEquiv_wreath_of_noncommProd_conjClass_ne_one
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    (hZ : Nat.card (Subgroup.center P) = p)
    {a : P} (haA : a ∈ A) (haZ : a ∉ Subgroup.center P)
    (hprod : (Set.toFinite {b | IsConj a b}).toFinset.noncommProd id
      (conjClass_pairwise_commute hEA haA) ≠ 1) :
    Nonempty (P ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))) := by
  classical
  have hp_prime : p.Prime := hp.out
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := elemAb_comm hEA
  -- Z(P) ≤ A (else A would be central and a ∈ Z(P))
  have hZle : Subgroup.center P ≤ A := by
    by_contra hnot
    exact haZ (le_center_of_center_not_le hidx hAb hnot haA)
  -- fix u ∉ A
  obtain ⟨u, hu⟩ := exists_notMem_of_index_prime hidx
  have hupA : u ^ p ∈ A := (pow_mem_iff_dvd hidx hu p).mpr dvd_rfl
  -- the class product in list form ∏_{i<p} a^{u^i}
  have hlistne : ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod ≠ 1 := by
    rw [← noncommProd_conjClass_eq_list_prod hidx hEA haA haZ hu]
    exact hprod
  -- |A| = p^m with m ≥ p, and conclude via the Sylow embedding
  obtain ⟨m, hm, hcardA⟩ :=
    exists_card_eq_pow_ge_of_conj_list_prod_ne_one hEA haA hupA hlistne
  exact nonempty_mulEquiv_wreath_of_card_pow hP hidx hEA hZ hZle hm hcardA

end

section /- 10A: Corollary 10.5 (p. 299) -/

/-- Induction engine for Isaacs Cor 10.5, recursing on an upper bound for
`Nat.card Q`: either `|Z(Q)| = p` and Theorem 10.4 applies directly, or
`|Z(Q)| ≥ p²` and one divides out a central subgroup `⟨z⟩` of order `p` avoiding
the class product `b`, preserving all hypotheses (Isaacs p. 299). -/
private theorem cor105_aux (n : ℕ) :
    ∀ {Q : Type*} [Group Q] [Finite Q],
    ∀ (_ : IsPGroup p Q) {A : Subgroup Q} [A.Normal]
      (_ : A.index = p) (_ : A.IsElementaryAbelian p)
      {a : Q} (_ : a ∈ A) (_ : a ∉ Subgroup.center Q)
      {u : Q} (_ : u ∉ A)
      (_ : ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod ≠ 1),
      Nat.card Q ≤ n →
      ∃ φ : Q →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)),
        Function.Surjective φ := by
  induction n with
  | zero =>
    intro Q _ _ _ A _ _ _ a _ _ u _ _ hle
    have : 0 < Nat.card Q := Nat.card_pos
    omega
  | succ n ih =>
    intro Q _ _ hQ A _ hidx hEA a haA haZ u hu hlist hle
    classical
    have hp_prime : p.Prime := hp.out
    have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := elemAb_comm hEA
    have hZle : Subgroup.center Q ≤ A := by
      by_contra hnot
      exact haZ (le_center_of_center_not_le hidx hAb hnot haA)
    by_cases hZp : Nat.card (Subgroup.center Q) = p
    · -- |Z(Q)| = p: Theorem 10.4 pipeline applies directly
      have hupA : u ^ p ∈ A := (pow_mem_iff_dvd hidx hu p).mpr dvd_rfl
      obtain ⟨m, hm, hcardA⟩ :=
        exists_card_eq_pow_ge_of_conj_list_prod_ne_one hEA haA hupA hlist
      obtain ⟨e⟩ := nonempty_mulEquiv_wreath_of_card_pow hQ hidx hEA hZp hZle hm hcardA
      exact ⟨e.toMonoidHom, e.surjective⟩
    · -- |Z(Q)| ≥ p²: divide out a central ⟨z⟩ of order p avoiding the class product
      set b := ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod with hb_def
      have hbA : b ∈ A := by
        apply Subgroup.list_prod_mem
        intro x hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact ‹A.Normal›.conj_mem a haA _
      have hb_ne : b ≠ 1 := hlist
      have hb_pow : b ^ p = 1 := Subtype.ext_iff.mp (hEA.2 ⟨b, hbA⟩)
      have hb_ord : orderOf b = p := by
        rcases hp_prime.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hb_pow)
          with h1 | h
        · exact absurd (orderOf_eq_one_iff.mp h1) hb_ne
        · exact h
      -- the center has order ≥ p²
      have ha_ne : a ≠ 1 := fun h => haZ (h ▸ Subgroup.one_mem _)
      haveI : Nontrivial Q := ⟨⟨a, 1, ha_ne⟩⟩
      haveI := hQ.center_nontrivial
      obtain ⟨k, hk_pos, hkcard⟩ :=
        ((hQ.to_subgroup (Subgroup.center Q)).nontrivial_iff_card).mp ‹_›
      have hk2 : 2 ≤ k := by
        by_contra h
        have hk1 : k = 1 := by omega
        exact hZp (by rw [hkcard, hk1, pow_one])
      have hcardZ_ge : p ^ 2 ≤ Nat.card (Subgroup.center Q) := by
        rw [hkcard]
        exact Nat.pow_le_pow_right hp_prime.pos hk2
      -- choose z ∈ Z(Q) outside ⟨b⟩; it has order p and b ∉ ⟨z⟩
      have hnotle : ¬ Subgroup.center Q ≤ Subgroup.zpowers b := by
        intro hle'
        have h1 := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle')
        rw [Nat.card_zpowers, hb_ord] at h1
        have hp2 : p < p ^ 2 := by
          calc p = p ^ 1 := (pow_one p).symm
            _ < p ^ 2 := Nat.pow_lt_pow_right hp_prime.one_lt (by omega)
        omega
      obtain ⟨z, hz_cent, hz_nb⟩ := SetLike.not_le_iff_exists.mp hnotle
      have hz_ne : z ≠ 1 := fun h => hz_nb (h ▸ Subgroup.one_mem _)
      have hzA : z ∈ A := hZle hz_cent
      have hz_pow : z ^ p = 1 := Subtype.ext_iff.mp (hEA.2 ⟨z, hzA⟩)
      have hz_ord : orderOf z = p := by
        rcases hp_prime.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hz_pow)
          with h1 | h
        · exact absurd (orderOf_eq_one_iff.mp h1) hz_ne
        · exact h
      set Z := Subgroup.zpowers z with hZ_def
      have hZ_le_cent : Z ≤ Subgroup.center Q := Subgroup.zpowers_le.mpr hz_cent
      haveI hZnormal : Z.Normal := by
        constructor
        intro g hg x
        have h1 : x * g * x⁻¹ = g := by
          rw [Subgroup.mem_center_iff.mp (hZ_le_cent hg) x]; group
        rwa [h1]
      have hcardZeq : Nat.card Z = p := by rw [hZ_def, Nat.card_zpowers, hz_ord]
      have hbZ : b ∉ Z := by
        intro hbz
        have hle1 : Subgroup.zpowers b ≤ Z := Subgroup.zpowers_le.mpr hbz
        have heq : Subgroup.zpowers b = Z := by
          apply Subgroup.eq_of_le_of_card_ge hle1
          rw [hcardZeq, Nat.card_zpowers, hb_ord]
        exact hz_nb (heq ▸ Subgroup.mem_zpowers z)
      -- pass to the quotient Q ⧸ Z
      set π : Q →* Q ⧸ Z := QuotientGroup.mk' Z with hπ_def
      have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
      have hkerπ : π.ker = Z := QuotientGroup.ker_mk' Z
      have hZ_le_A : Z ≤ A := Subgroup.zpowers_le.mpr hzA
      haveI : (A.map π).Normal := Subgroup.Normal.map ‹A.Normal› π hπsurj
      have hidx' : (A.map π).index = p := by
        rw [A.index_map_eq hπsurj (by rw [hkerπ]; exact hZ_le_A), hidx]
      have hEA' : (A.map π).IsElementaryAbelian p :=
        Subgroup.IsElementaryAbelian.map_hom π hEA
      have haA' : π a ∈ A.map π := Subgroup.mem_map_of_mem π haA
      have hu' : π u ∉ A.map π := by
        intro hmem
        obtain ⟨w, hwA, hw⟩ := Subgroup.mem_map.mp hmem
        have hker : w⁻¹ * u ∈ Z := by
          rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hw, inv_mul_cancel]
        exact hu (by simpa using A.mul_mem hwA (hZ_le_A hker))
      -- the image of the conjugate list is the conjugate list of the images
      have hmap_list : ((List.range p).map
          (fun i => (π u) ^ i * (π a) * ((π u) ^ i)⁻¹)).prod = π b := by
        rw [hb_def, map_list_prod, List.map_map]
        congr 1
      have hπb_ne : π b ≠ 1 := by
        intro h1
        exact hbZ (by rw [← hkerπ]; exact π.mem_ker.mpr h1)
      have hlist' : ((List.range p).map
          (fun i => (π u) ^ i * (π a) * ((π u) ^ i)⁻¹)).prod ≠ 1 := by
        rw [hmap_list]; exact hπb_ne
      -- π a is noncentral: otherwise π b = (π a)^p = π (a^p) = 1
      have haZ' : π a ∉ Subgroup.center (Q ⧸ Z) := by
        intro hcent
        apply hπb_ne
        rw [← hmap_list]
        have hconst : ((List.range p).map
            (fun i => (π u) ^ i * (π a) * ((π u) ^ i)⁻¹))
            = List.replicate p (π a) := by
          rw [show List.replicate p (π a) = (List.range p).map (fun _ => π a) by
            rw [List.map_const', List.length_range]]
          refine List.map_congr_left fun i _ => ?_
          rw [Subgroup.mem_center_iff.mp hcent ((π u) ^ i)]
          group
        rw [hconst, List.prod_replicate]
        have hpa : a ^ p = 1 := Subtype.ext_iff.mp (hEA.2 ⟨a, haA⟩)
        rw [← map_pow, hpa, map_one]
      -- the quotient is strictly smaller: |Q ⧸ Z| = |Q| / p ≤ n
      have hcard_le : Nat.card (Q ⧸ Z) ≤ n := by
        have h1 : Nat.card Z * Z.index = Nat.card Q := Subgroup.card_mul_index Z
        rw [hcardZeq, Subgroup.index_eq_card] at h1
        have hq_pos : 0 < Nat.card (Q ⧸ Z) := Nat.card_pos
        have hp2 : 2 ≤ p := hp_prime.two_le
        have h2 : 2 * Nat.card (Q ⧸ Z) ≤ p * Nat.card (Q ⧸ Z) :=
          Nat.mul_le_mul_right _ hp2
        omega
      obtain ⟨φ, hφ⟩ := ih (hQ.to_quotient Z) hidx' hEA' haA' haZ' hu' hlist' hcard_le
      exact ⟨φ.comp π, hφ.comp hπsurj⟩

/-- **Isaacs Corollary 10.5**: let `P` be a `p`-group with a normal elementary
abelian subgroup `A` of index `p`, and let `a ∈ A` be noncentral such that the
product of the `p` elements of its conjugacy class is not the identity. Then
`C_p ≀ C_p` is a homomorphic image of `P`.

(Induction on `|P|`: if `|Z(P)| = p` this is Theorem 10.4; otherwise divide out a
central subgroup of order `p` avoiding the class product and recurse.) -/
theorem exists_surjective_wreath_of_noncommProd_conjClass_ne_one
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {a : P} (haA : a ∈ A) (haZ : a ∉ Subgroup.center P)
    (hprod : (Set.toFinite {b | IsConj a b}).toFinset.noncommProd id
      (conjClass_pairwise_commute hEA haA) ≠ 1) :
    ∃ φ : P →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)),
      Function.Surjective φ := by
  obtain ⟨u, hu⟩ := exists_notMem_of_index_prime hidx
  have hlist : ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod ≠ 1 := by
    rw [← noncommProd_conjClass_eq_list_prod hidx hEA haA haZ hu]
    exact hprod
  exact cor105_aux (Nat.card P) hP hidx hEA haA haZ hu hlist le_rfl

/-- **Isaacs Corollary 10.5, enumerated form**: as
`exists_surjective_wreath_of_noncommProd_conjClass_ne_one`, but with the class
product given as the ordered product `∏_{i<p} a^{uⁱ}` for a chosen `u ∉ A`.
(This is the form produced by the transfer computation of Lemma 10.6 and
consumed by Lemma 10.7.) -/
theorem exists_surjective_wreath_of_conj_list_prod_ne_one
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hidx : A.index = p) (hEA : A.IsElementaryAbelian p)
    {a : P} (haA : a ∈ A) (haZ : a ∉ Subgroup.center P)
    {u : P} (hu : u ∉ A)
    (hlist : ((List.range p).map (fun i => u ^ i * a * (u ^ i)⁻¹)).prod ≠ 1) :
    ∃ φ : P →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)),
      Function.Surjective φ :=
  cor105_aux (Nat.card P) hP hidx hEA haA haZ hu hlist le_rfl

end


section /- 10A: the nilpotence class of `C_p ≀ C_p` is `p` (p. 296) -/

open RegularWreathProduct

variable (p : ℕ) [hp : Fact p.Prime]

/-- The base subgroup of `C_p ≀ C_p`: the kernel of the projection `rightHom`
onto the acting factor. -/
private def wreathBase : Subgroup
    (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) :=
  (RegularWreathProduct.rightHom
    (D := Multiplicative (ZMod p)) (Q := Multiplicative (ZMod p))).ker

/-- The distinguished single-coordinate generator of the base subgroup. -/
private def wreathGen : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p) :=
  ⟨Pi.mulSingle 1 (Multiplicative.ofAdd 1), 1⟩

/-- Multiplication of base elements is componentwise on the left factor. -/
private lemma wreathBase_mul (f g : Multiplicative (ZMod p) → Multiplicative (ZMod p)) :
    (⟨f, 1⟩ * ⟨g, 1⟩ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))
      = ⟨f * g, 1⟩ := by
  rw [RegularWreathProduct.mul_def]
  congr 1
  · funext x
    simp
  · simp

private lemma wreathBase_pow (f : Multiplicative (ZMod p) → Multiplicative (ZMod p))
    (m : ℕ) :
    ((⟨f, 1⟩ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) ^ m)
      = ⟨f ^ m, 1⟩ := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    ext <;> rfl
  | succ m ih =>
    rw [pow_succ, ih, wreathBase_mul, ← pow_succ]

/-- Conjugation by `inl q₀` shifts the left component. -/
private lemma inl_conj_base (q₀ : Multiplicative (ZMod p))
    (f : Multiplicative (ZMod p) → Multiplicative (ZMod p)) :
    (RegularWreathProduct.inl q₀ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))
        * ⟨f, 1⟩ * (RegularWreathProduct.inl q₀)⁻¹
      = ⟨fun x => f (q₀⁻¹ * x), 1⟩ := by
  have h1 : (RegularWreathProduct.inl q₀ :
      Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) = ⟨1, q₀⟩ := rfl
  have h2 : ((⟨1, q₀⟩ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))⁻¹
      = ⟨1, q₀⁻¹⟩ := by
    ext <;> simp [RegularWreathProduct.inv_left, RegularWreathProduct.inv_right]
  rw [h1, h2, RegularWreathProduct.mul_def, RegularWreathProduct.mul_def]
  congr 1
  · funext x
    simp
  · simp

private lemma wreathBase_index : (wreathBase p).index = p := by
  have hsurj : Function.Surjective (RegularWreathProduct.rightHom
      (D := Multiplicative (ZMod p)) (Q := Multiplicative (ZMod p))) := by
    intro q
    exact ⟨RegularWreathProduct.inl q, RegularWreathProduct.fun_id q⟩
  rw [wreathBase, Subgroup.index_ker]
  rw [MonoidHom.range_eq_top_of_surjective _ hsurj]
  have h2 : Nat.card (↥(⊤ : Subgroup (Multiplicative (ZMod p))))
      = Nat.card (Multiplicative (ZMod p)) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [h2, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private lemma wreathBase_isElementaryAbelian :
    (wreathBase p).IsElementaryAbelian p := by
  constructor
  · rintro ⟨⟨f, qf⟩, hf⟩ ⟨⟨g, qg⟩, hg⟩
    have hqf : qf = 1 := hf
    have hqg : qg = 1 := hg
    subst hqf
    subst hqg
    refine Subtype.ext ?_
    change (⟨f, 1⟩ * ⟨g, 1⟩ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))
      = ⟨g, 1⟩ * ⟨f, 1⟩
    rw [wreathBase_mul, wreathBase_mul, mul_comm]
  · rintro ⟨⟨f, qf⟩, hf⟩
    have hqf : qf = 1 := hf
    subst hqf
    refine Subtype.ext ?_
    change ((⟨f, 1⟩ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) ^ p) = 1
    rw [wreathBase_pow]
    have hfp : f ^ p = 1 := by
      funext x
      change (f x) ^ p = 1
      have h1 := ZModModule.char_nsmul_eq_zero (n := p) (Multiplicative.toAdd (f x))
      apply Multiplicative.toAdd.injective
      have h2 : Multiplicative.toAdd ((f x) ^ p)
          = p • Multiplicative.toAdd (f x) := rfl
      rw [h2, h1]
      rfl
    rw [hfp]
    rfl

private lemma wreathBase_card : Nat.card (wreathBase p) = p ^ p := by
  have hp_prime : p.Prime := hp.out
  have hcardW : Nat.card (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))
      = p ^ (p + 1) := by
    rw [RegularWreathProduct.card]
    have h1 : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h1, pow_succ]
  have h1 := Subgroup.card_mul_index (wreathBase p)
  rw [wreathBase_index, hcardW, pow_succ] at h1
  exact Nat.eq_of_mul_eq_mul_right hp_prime.pos h1

set_option maxHeartbeats 1000000 in
-- comparing wreath-product components up to defeq (`congr 1` + `funext`) forces
-- repeated whnf of the `RegularWreathProduct` mul/action instances
/-- Every single-coordinate base element is a conjugated power of the
generator `wreathGen`. -/
private lemma mulSingle_mem_normalClosure (q : Multiplicative (ZMod p))
    (d : Multiplicative (ZMod p)) :
    (⟨Pi.mulSingle q d, 1⟩ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))
      ∈ Subgroup.normalClosure {wreathGen p} := by
  -- d is a power of the additive generator
  have hval : ∃ m : ℕ, (Multiplicative.ofAdd (1 : ZMod p)) ^ m = d := by
    refine ⟨(Multiplicative.toAdd d).val, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
    exact ZMod.natCast_rightInverse _
  obtain ⟨m, hm⟩ := hval
  have hconj : (RegularWreathProduct.inl q :
        Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) * (wreathGen p ^ m)
        * (RegularWreathProduct.inl q)⁻¹
      = ⟨Pi.mulSingle q d, 1⟩ := by
    rw [wreathGen, wreathBase_pow, inl_conj_base]
    congr 1
    funext x
    rw [← Pi.mulSingle_pow]
    by_cases hx : x = q
    · rw [hx, show (q⁻¹ * q : Multiplicative (ZMod p)) = 1 from inv_mul_cancel q,
        Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, hm]
    · have hx' : q⁻¹ * x ≠ 1 := by
        intro h4
        apply hx
        have h5 : q * (q⁻¹ * x) = q * 1 := by rw [h4]
        rwa [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h5
      rw [Pi.mulSingle_eq_of_ne hx', Pi.mulSingle_eq_of_ne hx]
  have hgen_mem : wreathGen p ∈ Subgroup.normalClosure {wreathGen p} :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hpow_mem : wreathGen p ^ m ∈ Subgroup.normalClosure {wreathGen p} :=
    Subgroup.pow_mem _ hgen_mem m
  have hconj_mem := Subgroup.normalClosure_normal.conj_mem _ hpow_mem
    (RegularWreathProduct.inl q)
  exact hconj ▸ hconj_mem

/-- The base subgroup is the normal closure of the single generator. -/
private lemma wreathBase_eq_normalClosure :
    wreathBase p = Subgroup.normalClosure {wreathGen p} := by
  classical
  haveI : (wreathBase p).Normal := by
    rw [wreathBase]
    infer_instance
  have hsub : Subgroup.normalClosure {wreathGen p} ≤ wreathBase p := by
    apply Subgroup.normalClosure_le_normal
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    change (wreathGen p).right = 1
    rfl
  refine le_antisymm ?_ hsub
  rintro ⟨f, qf⟩ hmem
  have hqf : qf = 1 := hmem
  subst hqf
  -- embed the commutative function group along g ↦ ⟨g, 1⟩ and decompose f
  set β : (Multiplicative (ZMod p) → Multiplicative (ZMod p))
      →* Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p) :=
    { toFun := fun g => ⟨g, 1⟩
      map_one' := rfl
      map_mul' := fun g₁ g₂ => (wreathBase_mul p g₁ g₂).symm } with hβ_def
  have hdecomp : (⟨f, 1⟩ : Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))
      = β (∏ q, Pi.mulSingle q (f q)) := by
    rw [Finset.univ_prod_mulSingle]
    rfl
  rw [hdecomp]
  exact Subgroup.mem_comap.mp (Subgroup.prod_mem _ fun q _ =>
    Subgroup.mem_comap.mpr (mulSingle_mem_normalClosure p q (f q)))

/-- **The nilpotence class of `C_p ≀ C_p` is exactly `p`** (Isaacs p. 296): the
base subgroup is elementary abelian of order `p^p` and index `p`, and it is
generated by the conjugacy class of a single coordinate function, so
Lemma 10.3(c) applies with `t = p`. -/
theorem nilpotencyClass_wreath :
    Group.nilpotencyClass (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) = p := by
  have hp_prime : p.Prime := hp.out
  have hcardW : Nat.card (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p))
      = p ^ (p + 1) := by
    rw [RegularWreathProduct.card]
    have h1 : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h1, pow_succ]
  have hW_pgroup : IsPGroup p (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) :=
    IsPGroup.of_card hcardW
  exact nilpotencyClass_eq_of_elementaryAbelian_normalClosure_index_prime
    hW_pgroup (wreathBase_index p) (wreathBase_isElementaryAbelian p)
    hp_prime.two_le (wreathBase_card p) (wreathBase_eq_normalClosure p)

/- 10B: `C_p ≀ C_p` is not an image of a metacyclic group (Lemma 10.14, p. 305) -/

/-- **Isaacs Lemma 10.14** (core): for `p > 2` the wreath product `C_p ≀ C_p` is
not metacyclic. Its derived subgroup is elementary abelian of order `p^(p-1) > p`
by Lemma 10.3(b), hence not cyclic — but metacyclic groups have cyclic derived
subgroups. -/
theorem not_isMetacyclic_wreath (hp2 : 2 < p) :
    ¬ IsMetacyclic (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) := by
  intro hmeta
  have hp_prime : p.Prime := hp.out
  have hW_pgroup : IsPGroup p (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) := by
    refine IsPGroup.of_card (n := p + 1) ?_
    rw [RegularWreathProduct.card, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      pow_succ]
  -- `|W'| = p^(p-1)` and `W'` is elementary abelian (Lemma 10.3(b))
  have hcard := card_commutator_eq_of_elementaryAbelian_normalClosure_index_prime
    hW_pgroup (wreathBase_index p) (wreathBase_isElementaryAbelian p)
    hp_prime.two_le (wreathBase_card p) (wreathBase_eq_normalClosure p)
  have hEA := isElementaryAbelian_commutator_of_elementaryAbelian_normalClosure_index_prime
    (wreathBase_index p) (wreathBase_isElementaryAbelian p) (wreathBase_eq_normalClosure p)
  -- metacyclic ⇒ `W'` cyclic, so `|W'| = orderOf g ∣ p` for a generator `g`
  obtain ⟨g, hg⟩ := hmeta.isCyclic_commutator.exists_generator
  have htop : Subgroup.zpowers g = ⊤ := top_unique fun x _ => hg x
  have hcard_eq : Nat.card
      (_root_.commutator (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))
      = orderOf g := by
    rw [← Nat.card_zpowers g, htop]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  have hdvd : p ^ (p - 1) ∣ p := by
    rw [← hcard, hcard_eq]
    exact orderOf_dvd_of_pow_eq_one (hEA.2 g)
  -- but `p - 1 ≥ 2` forces `p^2 ≤ p^(p-1) ≤ p`, absurd
  have hle : p ^ (p - 1) ≤ p := Nat.le_of_dvd hp_prime.pos hdvd
  have hsq : p ^ 2 ≤ p ^ (p - 1) :=
    Nat.pow_le_pow_right hp_prime.one_lt.le (by omega)
  have : p * p ≤ p * 1 := by
    calc p * p = p ^ 2 := (sq p).symm
      _ ≤ p := le_trans hsq hle
      _ = p * 1 := (mul_one p).symm
  have := Nat.le_of_mul_le_mul_left this hp_prime.pos
  omega

/-- **Isaacs Lemma 10.14**: for `p > 2` the wreath product `C_p ≀ C_p` is not a
homomorphic image of a metacyclic group (combine the core with Lemma 10.13(a),
`IsMetacyclic.of_surjective`). -/
theorem not_surjective_wreath_of_isMetacyclic {M : Type*} [Group M]
    (hmeta : IsMetacyclic M) (hp2 : 2 < p)
    (φ : M →* Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)) :
    ¬ Function.Surjective φ := fun hφ =>
  not_isMetacyclic_wreath p hp2 (hmeta.of_surjective hφ)

end

end OddOrder.Isaacs.Ch10
