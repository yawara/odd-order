/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch10_MoreTransfer.WreathRecognition
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.GroupTheory.PrimeOrderSubgroups
import OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke

/-!
# Isaacs §10B — Huppert's metacyclic Sylow theorem (pp. 304-307)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10 "More Transfer
Theory", §10B: Huppert の定理に向けた main lemma。

* **Theorem 10.15** (`dvd_index_commutator_of_normal_metacyclic_sylow`):
  `P ⊴ N` が nonabelian metacyclic な正規 Sylow `p`-部分群で `p > 2` なら
  `p ∣ |N : N'|`。`|P|` に関する帰納。
* **Theorem 10.12** (Huppert) は 10.15 + Yoshida 10.1 + Lemma 10.14 から。
  (本 leaf 後半に追加予定。)

## 教科書対応 (証明の要点, mmd L5613-5645)

1. 位数 `p` の任意の `Y ⊴ N` で `P/Y` が nonabelian なら帰納。
2. さもなくば `P' ≤ Y` が常に成立 → `|P'| = p` で `P'` は `N` の唯一の位数 `p`
   正規部分群 (`P'` cyclic の位数 `p` 部分群の一意性 =
   `subgroup_eq_of_card_eq_prime_of_isCyclic`)。
3. `P' ≤ Z(P)` (`normal_le_center_of_card_eq_prime`)、`P` は class 2。
4. `V := Ω₁(P)` は elementary abelian, `|V| = p²` (BG Lem 4.10 =
   `isElementaryAbelian_omega1_of_isMetacyclic`)。
5. `V ≤ Z(P)` なら `N/P` の coprime 作用に Maschke
   (`exists_aInvariant_complement_of_isElementaryAbelian`) を適用して `P'` と別の
   位数 `p` 正規部分群が出て (2) の一意性と矛盾 ⇒ `V ⊄ Z(P)`。
6. `P/Z(P)` は elementary abelian (`[y^p, x] = [y, x]^p = 1`)。
7. Maschke を `P/Z` に適用: `P/Z = (VZ/Z) × (H/Z)`, `H ⊴ N`。
8. `|V ∩ H| ≤ p` ⇒ `H` の位数 `p` 部分群は一意 ⇒ `H` cyclic (Isaacs Thm 6.11 =
   `isCyclic_of_subgroups_card_prime_unique_of_odd`)。
9. `VZ` abelian `≠ P` ⇒ `H ⊄ Z(P)` 側、`P ⊄ C_N(H)`。
10. `N/C_N(H) ↪ Aut(H)` abelian (`IsCyclic.mulAutMulEquiv`) ⇒ `N' ≤ C_N(H)`、
    `p ∣ |N : C_N(H)|` ⇒ `p ∣ |N : N'|`。

issue 3007 参照。
-/

namespace OddOrder.Isaacs.Ch10

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03 (IsAInvariant)
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom quotientMulAutHom_apply_mk')
open OddOrder.Isaacs.Ch04
open OddOrder.BG.Ch1
open OddOrder.BG.Ch1_Preliminary
open scoped commutatorElement
open scoped Pointwise

variable {p : ℕ} [hp : Fact p.Prime]

section /- 10B: Theorem 10.15 (pp. 305-306) -/

/-- Abelianization cardinality is monotone under surjections: if `f : G →* H` is
surjective then `|H : H'|` divides `|G : G'|` (the abelianization of `H` is a
quotient of that of `G`). Used for the inductive step of Theorem 10.15. -/
theorem index_commutator_dvd_of_surjective {G H : Type*} [Group G] [Group H]
    {f : G →* H} (hf : Function.Surjective f) :
    (commutator H).index ∣ (commutator G).index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  -- the composite `G → H → H ⧸ H'` kills `G'`, hence factors through `G ⧸ G'`
  have hker : commutator G ≤ ((QuotientGroup.mk' (commutator H)).comp f).ker := by
    have hmap : (commutator G).map f ≤ commutator H := by
      rw [commutator_def, Subgroup.map_commutator, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    intro x hx
    have hfx : f x ∈ commutator H := hmap (Subgroup.mem_map_of_mem f hx)
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hfx
  refine Subgroup.card_dvd_of_surjective
    (QuotientGroup.lift (commutator G) _ hker) ?_
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (commutator H) y
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- **Isaacs Theorem 10.15, base case** (Isaacs pp. 305-306, second and later
paragraphs): under the 10.15 hypotheses, if moreover the quotient `P/Y` is
abelian — equivalently `⁅P, P⁆ ≤ Y` — for **every** normal subgroup `Y ⊴ N` of
order `p` inside `P`, then `p ∣ |N : N'|`. This is the heart of the proof
(steps 2-10 of the module docstring); the inductive wrapper `thm1015_aux`
reduces to it. -/
private theorem thm1015_base {N : Type*} [Group N] [Finite N] {P : Subgroup N}
    (hPn : P.Normal) (hPp : IsPGroup p ↥P) (hPidx : ¬(p ∣ P.index))
    (hmeta : IsMetacyclic ↥P) (hnonab : ¬ ∀ x y : ↥P, x * y = y * x)
    (hp2 : 2 < p)
    (habel : ∀ Y : Subgroup N, Y.Normal → Y ≤ P → Nat.card ↥Y = p → ⁅P, P⁆ ≤ Y) :
    p ∣ (commutator N).index := by
  classical
  have hp_prime : p.Prime := hp.out
  haveI := hPn
  -- ### Step 2 setup: `P' := ⁅P, P⁆ ⊴ N` is a nontrivial cyclic `p`-group
  set P' : Subgroup N := ⁅P, P⁆ with hP'_def
  haveI hP'n : P'.Normal := by rw [hP'_def]; infer_instance
  have hP'le : P' ≤ P := Subgroup.commutator_le_left P P
  have hP'_map : (_root_.commutator ↥P).map P.subtype = P' := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hP'cyc : IsCyclic ↥P' := by
    haveI := hmeta.isCyclic_commutator
    have e := Subgroup.equivMapOfInjective (_root_.commutator ↥P) P.subtype
      P.subtype_injective
    rw [hP'_map] at e
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hP'p : IsPGroup p ↥P' := hPp.to_le hP'le
  have hP'ne : P' ≠ ⊥ := by
    intro hbot
    refine hnonab fun x y => ?_
    have hmem : ⁅(x : N), (y : N)⁆ ∈ P' :=
      Subgroup.commutator_mem_commutator x.2 y.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hmem)
  -- `P'` contains an order-`p` element (Cauchy), giving `Y₀ ≤ P'` of order `p`
  have hpdvd : p ∣ Nat.card ↥P' := by
    rcases hP'p.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) hP'ne
    · exact h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  set Y₀ : Subgroup N := (Subgroup.zpowers g).map P'.subtype with hY₀_def
  have hY₀le : Y₀ ≤ P' := Subgroup.map_subtype_le _
  have hY₀card : Nat.card ↥Y₀ = p := by
    rw [hY₀_def,
      ← Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.zpowers g) P'.subtype
        P'.subtype_injective).toEquiv,
      Nat.card_zpowers, hg]
  -- conjugation permutes the order-`p` subgroups of the cyclic `P'`, so `Y₀ ⊴ N`
  have hY₀conj : ∀ n : N, Y₀.map (MulAut.conj n).toMonoidHom = Y₀ := by
    intro n
    set Y₁ : Subgroup N := Y₀.map (MulAut.conj n).toMonoidHom with hY₁_def
    have hY₁le : Y₁ ≤ P' := by
      rw [hY₁_def]
      rintro _ ⟨y, hy, rfl⟩
      exact hP'n.conj_mem y (hY₀le hy) n
    have hY₁card : Nat.card ↥Y₁ = p := by
      rw [hY₁_def,
        ← Nat.card_congr (Subgroup.equivMapOfInjective Y₀ (MulAut.conj n).toMonoidHom
          (MulAut.conj n).injective).toEquiv]
      exact hY₀card
    haveI := hP'cyc
    have hsub : Y₁.subgroupOf P' = Y₀.subgroupOf P' := by
      refine subgroup_eq_of_card_eq_prime_of_isCyclic (p := p) ?_ ?_
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₁le).toEquiv]
        exact hY₁card
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₀le).toEquiv]
        exact hY₀card
    ext x
    constructor
    · intro hx
      have hxP' : x ∈ P' := hY₁le hx
      have : (⟨x, hxP'⟩ : ↥P') ∈ Y₁.subgroupOf P' := hx
      rw [hsub] at this
      exact this
    · intro hx
      have hxP' : x ∈ P' := hY₀le hx
      have : (⟨x, hxP'⟩ : ↥P') ∈ Y₀.subgroupOf P' := hx
      rw [← hsub] at this
      exact this
  haveI hY₀n : Y₀.Normal := by
    constructor
    intro y hy n
    rw [← hY₀conj n]
    exact ⟨y, hy, rfl⟩
  -- ### Step 2 conclusion: `|P'| = p`, and `P'` is the unique order-`p` normal subgroup
  have hP'card : Nat.card ↥P' = p := by
    have hP'Y₀ : P' ≤ Y₀ := habel Y₀ hY₀n (hY₀le.trans hP'le) hY₀card
    rw [le_antisymm hP'Y₀ hY₀le]
    exact hY₀card
  -- any normal `p`-subgroup of `N` sits inside the normal Sylow subgroup `P`
  have hle_P : ∀ Y : Subgroup N, Y.Normal → IsPGroup p ↥Y → Y ≤ P := by
    intro Y hYn hYp
    haveI := hYn
    by_contra hnot
    have hsupp : IsPGroup p ↥(Y ⊔ P) := hYp.to_sup_of_normal_right hPp
    have hlt : P < Y ⊔ P := lt_of_le_of_ne le_sup_right fun h => hnot (h ▸ le_sup_left)
    have hrel_ne : P.relIndex (Y ⊔ P) ≠ 1 := by
      intro h1
      exact hlt.not_ge (Subgroup.relIndex_eq_one.mp h1)
    have hdvd_card : P.relIndex (Y ⊔ P) ∣ Nat.card ↥(Y ⊔ P) :=
      Subgroup.index_dvd_card _
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hsupp
    rw [hm] at hdvd_card
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp_prime).mp hdvd_card
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h1
      · exact absurd (by rw [hk, h0, pow_zero]) hrel_ne
      · exact h1
    refine hPidx ?_
    have hmul := Subgroup.relIndex_mul_index (le_sup_right : P ≤ Y ⊔ P)
    calc p ∣ p ^ k := dvd_pow_self p (by omega)
      _ = P.relIndex (Y ⊔ P) := hk.symm
      _ ∣ P.index := ⟨(Y ⊔ P).index, hmul.symm⟩
  have huniq : ∀ Y : Subgroup N, Y.Normal → Nat.card ↥Y = p → Y = P' := by
    intro Y hYn hYcard
    have hYP : Y ≤ P := hle_P Y hYn (IsPGroup.of_card (by rw [hYcard, pow_one]))
    have hP'Y : P' ≤ Y := habel Y hYn hYP hYcard
    exact (Subgroup.eq_of_le_of_card_ge hP'Y (by rw [hP'card, hYcard])).symm
  -- ### Step 3: `P' ≤ Z(P)` — `P` has class 2
  have hcomm_card : Nat.card ↥(_root_.commutator ↥P) = p := by
    have h := Nat.card_congr (Subgroup.equivMapOfInjective (_root_.commutator ↥P)
      P.subtype P.subtype_injective).toEquiv
    rw [hP'_map] at h
    rw [h, hP'card]
  have hcomm_le_center : _root_.commutator ↥P ≤ Subgroup.center ↥P :=
    normal_le_center_of_card_eq_prime hPp hcomm_card
  -- ### Step 4: `V := Ω₁(P)` is elementary abelian of order `p²`
  have hnc : ¬ IsCyclic ↥P := by
    intro hcyc
    letI : CommGroup ↥P := IsCyclic.commGroup
    exact hnonab fun x y => mul_comm x y
  obtain ⟨hVea, hVcard⟩ := OddOrder.BG.Ch1.S04.isElementaryAbelian_omega1_of_isMetacyclic
    hPp (hp_prime.odd_of_ne_two (by omega)) hmeta hnc
  -- ### Step 5: `V = Ω₁(P)` is not contained in `Z(P)`
  -- (`commutator ↥P` is `p`-torsion, so it lies inside `V`)
  have hK'V : _root_.commutator ↥P ≤ Omega ↥P p 1 := by
    intro x hx
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one]
    have h1 : (⟨x, hx⟩ : ↥(_root_.commutator ↥P)) ^ p = 1 := by
      rw [← hcomm_card]; exact pow_card_eq_one'
    simpa using congrArg Subtype.val h1
  -- conjugation action of `N` on `↥P`; `V` and `commutator ↥P` are characteristic
  set φ₀ : N →* MulAut ↥P := MulAut.conjNormal with hφ₀_def
  have hVinv : IsAInvariant φ₀ (Omega ↥P p 1) := IsAInvariant.of_characteristic φ₀
  have hVnotZ : ¬ (Omega ↥P p 1 ≤ Subgroup.center ↥P) := by
    intro hVZ
    -- `P` acts trivially on the central `V`, so the action descends to `N ⧸ P`
    have hker : P ≤ hVinv.restrict.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      rintro ⟨v, hv⟩
      show (hVinv.restrict x) ⟨v, hv⟩ = ⟨v, hv⟩
      apply Subtype.ext
      show (φ₀ x) v = v
      apply Subtype.ext
      have hcomm := (Subgroup.mem_center_iff.mp (hVZ hv)) ⟨x, hx⟩
      have hconj : (⟨x, hx⟩ : ↥P) * v * (⟨x, hx⟩ : ↥P)⁻¹ = v := by
        rw [hcomm]; group
      calc ((φ₀ x) v : N) = x * (v : N) * x⁻¹ := by simp [hφ₀_def]
        _ = ((((⟨x, hx⟩ : ↥P) * v * (⟨x, hx⟩ : ↥P)⁻¹ : ↥P)) : N) := by
            push_cast
            rfl
        _ = (v : N) := by rw [hconj]
    -- the descended coprime action of `N ⧸ P` on `↥V`, and Maschke
    set φQ : N ⧸ P →* MulAut ↥(Omega ↥P p 1) :=
      QuotientGroup.lift P hVinv.restrict hker with hφQ_def
    have hpE : p ∣ Nat.card ↥(Omega ↥P p 1) := by
      rw [hVcard]; exact dvd_pow_self p two_ne_zero
    have hcop : Nat.Coprime (Nat.card (N ⧸ P)) (Nat.card ↥(Omega ↥P p 1)) := by
      rw [hVcard]
      have h1 : Nat.card (N ⧸ P) = P.index := (Subgroup.index_eq_card P).symm
      rw [h1]
      exact Nat.Coprime.pow_right 2 ((hp_prime.coprime_iff_not_dvd.mpr hPidx).symm)
    have hUinvN : IsAInvariant hVinv.restrict
        ((_root_.commutator ↥P).subgroupOf (Omega ↥P p 1)) :=
      isAInvariant_subgroupOf_restrict hVinv (IsAInvariant.of_characteristic φ₀)
    have hUinv : IsAInvariant φQ ((_root_.commutator ↥P).subgroupOf (Omega ↥P p 1)) := by
      intro a
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective P a
      exact hUinvN n
    obtain ⟨W, hWinv, hWinf, hWsup⟩ :=
      exists_aInvariant_complement_of_isElementaryAbelian hpE hcop hVea hUinv
    -- cardinality bookkeeping: `|U| = p` hence `|W| = p`
    have hUcard : Nat.card ↥((_root_.commutator ↥P).subgroupOf (Omega ↥P p 1)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'V).toEquiv, hcomm_card]
    letI : CommGroup ↥(Omega ↥P p 1) :=
      { (inferInstance : Group ↥(Omega ↥P p 1)) with mul_comm := hVea.comm }
    have hcompl : ((_root_.commutator ↥P).subgroupOf (Omega ↥P p 1)).IsComplement' W := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
        (disjoint_iff.mpr hWinf) ?_
      rw [← Subgroup.mul_normal, hWsup, Subgroup.coe_top]
    have hWcard : Nat.card ↥W = p := by
      have hmul := hcompl.card_mul
      rw [hUcard, hVcard, pow_two] at hmul
      exact Nat.eq_of_mul_eq_mul_left hp_prime.pos hmul
    -- transport `W` to a normal order-`p` subgroup of `N`
    have hWres : IsAInvariant hVinv.restrict W := fun n => hWinv (QuotientGroup.mk n)
    have hWPinv : IsAInvariant φ₀ (W.map (Omega ↥P p 1).subtype) :=
      isAInvariant_map_subtype_of_restrict hVinv hWres
    set W2 : Subgroup N := (W.map (Omega ↥P p 1).subtype).map P.subtype with hW2_def
    have hW2card : Nat.card ↥W2 = p := by
      rw [hW2_def,
        ← Nat.card_congr (Subgroup.equivMapOfInjective _ P.subtype
          P.subtype_injective).toEquiv,
        ← Nat.card_congr (Subgroup.equivMapOfInjective _ (Omega ↥P p 1).subtype
          (Omega ↥P p 1).subtype_injective).toEquiv]
      exact hWcard
    have hW2n : W2.Normal := by
      constructor
      intro x hx n
      rw [hW2_def] at hx ⊢
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨(φ₀ n) u, hWPinv.smul_mem n hu, ?_⟩
      simp [hφ₀_def]
    -- `W2 = P'` by uniqueness, yet `W2` meets `U = commutator` trivially: contradiction
    have hW2eq : W2 = P' := huniq W2 hW2n hW2card
    have hbot : P' ≤ ⊥ := by
      intro x hxP'
      have hxW2 : x ∈ W2 := by rw [hW2eq]; exact hxP'
      rw [hW2_def] at hxW2
      obtain ⟨u, hu, rfl⟩ := hxW2
      obtain ⟨w, hw, rfl⟩ := hu
      have hwU : w ∈ (_root_.commutator ↥P).subgroupOf (Omega ↥P p 1) := by
        rw [Subgroup.mem_subgroupOf]
        rw [← hP'_map] at hxP'
        obtain ⟨k, hk, hkeq⟩ := hxP'
        have hkw : k = ((w : ↥(Omega ↥P p 1)) : ↥P) := P.subtype_injective hkeq
        rwa [hkw] at hk
      have hmem : w ∈ (_root_.commutator ↥P).subgroupOf (Omega ↥P p 1) ⊓ W := ⟨hwU, hw⟩
      rw [hWinf, Subgroup.mem_bot] at hmem
      rw [hmem]
      simp
    exact hP'ne (le_bot_iff.mp hbot)
  -- ### Step 6: `P ⧸ Z(P)` is elementary abelian
  -- `⁅·, x⁆` is a homomorphism in the left argument (class ≤ 2) …
  have hcomm_hom : ∀ x a b : ↥P, ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    intro x a b
    have hcb := Subgroup.mem_center_iff.mp
      (hcomm_le_center (commutatorElement_mem_commutator_top b x))
    have hca := Subgroup.mem_center_iff.mp
      (hcomm_le_center (commutatorElement_mem_commutator_top a x))
    have h1 : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by group
    have h2 : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by rw [hcb a]; group
    rw [h1, h2, ← hca ⁅b, x⁆]
  -- … so `⁅y^m, x⁆ = ⁅y, x⁆^m`
  have hcomm_pow : ∀ (x y : ↥P) (m : ℕ), ⁅y ^ m, x⁆ = ⁅y, x⁆ ^ m := by
    intro x y m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, hcomm_hom x (y ^ m) y, ih]
  -- `p`-th powers are central since `|P'| = p`
  have hpow_central : ∀ y : ↥P, y ^ p ∈ Subgroup.center ↥P := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro x
    have hc : ⁅y, x⁆ ^ p = 1 := by
      have hmem := commutatorElement_mem_commutator_top y x
      have h1 : (⟨⁅y, x⁆, hmem⟩ : ↥(_root_.commutator ↥P)) ^ p = 1 := by
        rw [← hcomm_card]; exact pow_card_eq_one'
      simpa using congrArg Subtype.val h1
    have : ⁅y ^ p, x⁆ = 1 := by rw [hcomm_pow x y p, hc]
    have := commutatorElement_eq_one_iff_mul_comm.mp this
    rw [this]
  -- the conjugation action of `N` descends to `E := P ⧸ Z(P)` modulo `P`
  have hZinv : IsAInvariant φ₀ (Subgroup.center ↥P) := IsAInvariant.of_characteristic φ₀
  set φ₁ : N →* MulAut (↥P ⧸ Subgroup.center ↥P) := quotientMulAutHom hZinv with hφ₁_def
  have hker2 : P ≤ φ₁.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥P) v
    rw [hφ₁_def, quotientMulAutHom_apply_mk']
    show _ = (1 : MulAut _) ((QuotientGroup.mk' _) y)
    rw [MulAut.one_apply]
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⁅(⟨x, hx⟩ : ↥P), y⁻¹⁆, hcomm_le_center
      (commutatorElement_mem_commutator_top (⟨x, hx⟩ : ↥P) y⁻¹), ?_⟩
    have hval : (φ₀ x) y = (⟨x, hx⟩ : ↥P) * y * (⟨x, hx⟩ : ↥P)⁻¹ := by
      apply Subtype.ext
      simp [hφ₀_def]
    rw [hval, commutatorElement_def]
    group
  set φQ2 : N ⧸ P →* MulAut (↥P ⧸ Subgroup.center ↥P) :=
    QuotientGroup.lift P φ₁ hker2 with hφQ2_def
  -- elementary abelian: abelian (class 2) + exponent `p` (p-th powers central)
  have hEea : IsElementaryAbelian p (↥P ⧸ Subgroup.center ↥P) := by
    constructor
    · exact fun a b => isMulCommutative_iff.mp
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le
          (N := Subgroup.center ↥P)).mpr hcomm_le_center) a b
    · intro v
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥P) v
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hpow_central y
  -- `p` divides `|E|`: the centre is proper since `P` is nonabelian
  have hZne : Subgroup.center ↥P ≠ ⊤ := by
    intro htop
    refine hnonab fun x y => ?_
    exact Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top y) x
  have hEp : IsPGroup p (↥P ⧸ Subgroup.center ↥P) := hPp.to_quotient _
  have hpE2 : p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) := by
    rcases hEp.card_eq_or_dvd with h1 | h2
    · exfalso
      have : (Subgroup.center ↥P).index = 1 := by
        rw [Subgroup.index_eq_card]; exact h1
      exact hZne (Subgroup.index_eq_one.mp this)
    · exact h2
  have hcop2 : Nat.Coprime (Nat.card (N ⧸ P))
      (Nat.card (↥P ⧸ Subgroup.center ↥P)) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hEp
    rw [hm, ← Subgroup.index_eq_card]
    exact Nat.Coprime.pow_right m ((hp_prime.coprime_iff_not_dvd.mpr hPidx).symm)
  -- `U₂ := VZ/Z`, invariant; Maschke gives an invariant complement `X = H/Z`
  set U2 : Subgroup (↥P ⧸ Subgroup.center ↥P) :=
    (Omega ↥P p 1).map (QuotientGroup.mk' (Subgroup.center ↥P)) with hU2_def
  have hU2invN : IsAInvariant φ₁ U2 := by
    rw [hU2_def, hφ₁_def]
    exact isAInvariant_map_mk' hZinv hVinv
  have hU2inv : IsAInvariant φQ2 U2 := by
    intro a
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective P a
    exact hU2invN n
  obtain ⟨X, hXinv, hXinf, hXsup⟩ :=
    exists_aInvariant_complement_of_isElementaryAbelian hpE2 hcop2 hEea hU2inv
  -- ### Step 8: `H := X.comap mk'` has a unique order-`p` subgroup, hence is cyclic
  set H_P : Subgroup ↥P := X.comap (QuotientGroup.mk' (Subgroup.center ↥P))
    with hH_P_def
  -- `V ⊓ H ≤ Z`: an element of both maps into `U₂ ⊓ X = ⊥`
  have hVH_le_Z : Omega ↥P p 1 ⊓ H_P ≤ Subgroup.center ↥P := by
    rintro v ⟨hvV, hvH⟩
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥P)) v ∈ U2 ⊓ X := by
      refine ⟨?_, hvH⟩
      rw [hU2_def]
      exact Subgroup.mem_map_of_mem _ hvV
    rw [hXinf, Subgroup.mem_bot] at h1
    rwa [← QuotientGroup.eq_one_iff v]
  -- `|V ⊓ H| ≤ p` (otherwise `V ≤ H` and then `V ≤ Z`, contradiction)
  have hD_card : Nat.card ↥(Omega ↥P p 1 ⊓ H_P : Subgroup ↥P) ≤ p := by
    by_contra hgt
    push Not at hgt
    -- card divides p² and exceeds p, so it is p²; then V ⊓ H = V forces V ≤ Z
    have hdvd : Nat.card ↥(Omega ↥P p 1 ⊓ H_P : Subgroup ↥P) ∣ p ^ 2 := by
      rw [← hVcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp_prime).mp hdvd
    interval_cases k
    · rw [pow_zero] at hk; omega
    · rw [pow_one] at hk; omega
    · have heq : (Omega ↥P p 1 ⊓ H_P : Subgroup ↥P) = Omega ↥P p 1 := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hk, hVcard]
      exact hVnotZ (heq ▸ hVH_le_Z)
  -- unique order-`p` subgroups in `↥H_P`
  have hHuniq : ∀ K L : Subgroup ↥H_P, Nat.card ↥K = p → Nat.card ↥L = p → K = L := by
    have hkey : ∀ K : Subgroup ↥H_P, Nat.card ↥K = p →
        K = (Omega ↥P p 1 ⊓ H_P).subgroupOf H_P := by
      intro K hK
      have hle : K ≤ (Omega ↥P p 1 ⊓ H_P).subgroupOf H_P := by
        intro k hk
        rw [Subgroup.mem_subgroupOf]
        refine ⟨?_, (k : ↥H_P).2⟩
        refine Omega.mem_of_pow_eq_one ?_
        rw [pow_one]
        have h1 : (⟨k, hk⟩ : ↥K) ^ p = 1 := by rw [← hK]; exact pow_card_eq_one'
        have h2 := congrArg (fun z : ↥K => ((z : ↥H_P) : ↥P)) h1
        simpa using h2
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hK]
      calc Nat.card ↥((Omega ↥P p 1 ⊓ H_P).subgroupOf H_P)
          = Nat.card ↥(Omega ↥P p 1 ⊓ H_P : Subgroup ↥P) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
        _ ≤ p := hD_card
    intro K L hK hL
    rw [hkey K hK, hkey L hL]
  have hHcyc : IsCyclic ↥H_P :=
    OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd
      (hPp.to_subgroup H_P) (hp_prime.odd_of_ne_two (by omega)) hHuniq
  -- ### Step 9: `H ⊄ Z(P)`, hence some `u ∈ P` fails to centralize some `h₀ ∈ H`
  have hU2ne_top : U2 ≠ ⊤ := by
    intro htop
    refine hnonab fun x y => ?_
    -- `P = V ⊔ Z` would make `P` abelian
    have hPVZ : ∀ w : ↥P, w ∈ Omega ↥P p 1 ⊔ Subgroup.center ↥P := by
      intro w
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥P)) w ∈ U2 := by
        rw [htop]; exact Subgroup.mem_top _
      rw [hU2_def] at h1
      obtain ⟨v, hv, hveq⟩ := h1
      have hz : v⁻¹ * w ∈ Subgroup.center ↥P := QuotientGroup.eq.mp hveq
      have : w = v * (v⁻¹ * w) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hz)
    -- elements of `V ⊔ Z` commute
    have hcommVZ : ∀ a b : ↥P, a ∈ Omega ↥P p 1 ⊔ Subgroup.center ↥P →
        b ∈ Omega ↥P p 1 ⊔ Subgroup.center ↥P → a * b = b * a := by
      have hmul : ∀ c : ↥P, c ∈ Omega ↥P p 1 ⊔ Subgroup.center ↥P →
          ∃ v ∈ Omega ↥P p 1, ∃ z ∈ Subgroup.center ↥P, c = v * z := by
        intro c hc
        have : c ∈ (Omega ↥P p 1 : Set ↥P) * (Subgroup.center ↥P : Set ↥P) := by
          rw [← Subgroup.mul_normal]
          exact hc
        obtain ⟨v, hv, z, hz, hvz⟩ := this
        exact ⟨v, hv, z, hz, hvz.symm⟩
      intro a b ha hb
      obtain ⟨v₁, hv₁, z₁, hz₁, rfl⟩ := hmul a ha
      obtain ⟨v₂, hv₂, z₂, hz₂, rfl⟩ := hmul b hb
      have cz₁ : ∀ g : ↥P, Commute g z₁ := fun g => Subgroup.mem_center_iff.mp hz₁ g
      have cz₂ : ∀ g : ↥P, Commute g z₂ := fun g => Subgroup.mem_center_iff.mp hz₂ g
      have cv : Commute v₁ v₂ := by
        have := hVea.comm ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩
        simpa [Commute, SemiconjBy] using congrArg Subtype.val this
      exact ((cv.mul_right (cz₂ v₁)).mul_left
        (((cz₁ v₂).symm).mul_right (cz₂ z₁)))
    exact hcommVZ x y (hPVZ x) (hPVZ y)
  have hXne_bot : X ≠ ⊥ := by
    intro hbot
    rw [hbot, sup_bot_eq] at hXsup
    exact hU2ne_top hXsup
  obtain ⟨h₀, hh₀H, hh₀Z⟩ : ∃ h₀ : ↥P, h₀ ∈ H_P ∧ h₀ ∉ Subgroup.center ↥P := by
    obtain ⟨⟨ξ, hξX⟩, hξne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne_bot
    obtain ⟨h₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥P) ξ
    refine ⟨h₀, hξX, fun hz => hξne (Subtype.ext ?_)⟩
    show (QuotientGroup.mk' (Subgroup.center ↥P)) h₀ = 1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨u, hu⟩ : ∃ u : ↥P, u * h₀ ≠ h₀ * u := by
    by_contra hall
    push Not at hall
    exact hh₀Z (Subgroup.mem_center_iff.mpr fun g => hall g)
  -- ### Step 10: `N/C_N(H)` embeds in the abelian `Aut(H)`
  have hH_Pinv : IsAInvariant φ₀ H_P := by
    rw [hH_P_def]
    refine isAInvariant_comap_mk' hZinv ?_
    intro n
    exact hXinv (QuotientGroup.mk n)
  set H2 : Subgroup N := H_P.map P.subtype with hH2_def
  haveI hH2n : H2.Normal := by
    constructor
    intro x hx n
    rw [hH2_def] at hx ⊢
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨(φ₀ n) w, hH_Pinv.smul_mem n hw, ?_⟩
    simp [hφ₀_def]
  haveI hH2cyc : IsCyclic ↥H2 := by
    haveI := hHcyc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective H_P P.subtype P.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective H_P P.subtype P.subtype_injective).surjective
  set ψ2 : N →* MulAut ↥H2 := MulAut.conjNormal with hψ2_def
  -- `Aut(H)` is abelian since `H` is cyclic
  let e := IsCyclic.mulAutMulEquiv ↥H2
  letI : CommGroup (MulAut ↥H2) := e.toMonoidHom.commGroupOfInjective e.injective
  have hN'ker : commutator N ≤ ψ2.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  -- `p` divides the index of the kernel: `u` acts nontrivially
  have hp_ker : p ∣ ψ2.ker.index := by
    have hxker : (u : N) ∉ ψ2.ker := by
      intro hker
      rw [MonoidHom.mem_ker] at hker
      have h1 := congrArg (fun ψ : MulAut ↥H2 =>
        ((ψ ⟨(h₀ : N), Subgroup.mem_map_of_mem _ hh₀H⟩ : ↥H2) : N)) hker
      simp only [hψ2_def, MulAut.one_apply] at h1
      have h2 : (u : N) * (h₀ : N) * (u : N)⁻¹ = (h₀ : N) := by
        rw [show (((MulAut.conjNormal (u : N))
              ⟨(h₀ : N), _⟩ : ↥H2) : N)
            = (u : N) * (h₀ : N) * (u : N)⁻¹ from rfl] at h1
        exact h1
      refine hu ?_
      apply Subtype.ext
      have : (u : N) * (h₀ : N) = (h₀ : N) * (u : N) := by
        calc (u : N) * (h₀ : N) = ((u : N) * (h₀ : N) * (u : N)⁻¹) * (u : N) := by group
          _ = (h₀ : N) * (u : N) := by rw [h2]
      exact_mod_cast this
    obtain ⟨k, hk⟩ := hPp u
    have hxpow : ((u : N)) ^ p ^ k = 1 := by
      have := congrArg (Subtype.val) hk
      simpa using this
    set y : N ⧸ ψ2.ker := QuotientGroup.mk (u : N) with hy_def
    have hyne : y ≠ 1 := by
      rw [hy_def, Ne, QuotientGroup.eq_one_iff]
      exact hxker
    have hypow : y ^ p ^ k = 1 := by
      rw [hy_def, ← QuotientGroup.mk_pow, hxpow, QuotientGroup.mk_one]
    have hdvd : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hypow
    obtain ⟨j, hj_le, hj⟩ := (Nat.dvd_prime_pow hp_prime).mp hdvd
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h1
      · exfalso
        rw [h0, pow_zero, orderOf_eq_one_iff] at hj
        exact hyne hj
      · exact h1
    calc p ∣ p ^ j := dvd_pow_self p (by omega)
      _ = orderOf y := hj.symm
      _ ∣ Nat.card (N ⧸ ψ2.ker) := orderOf_dvd_natCard y
      _ = ψ2.ker.index := (Subgroup.index_eq_card ψ2.ker).symm
  exact dvd_trans hp_ker (Subgroup.index_dvd_of_le hN'ker)

/-- **Isaacs Theorem 10.15**, inductive core: if `P ⊴ N` is a nonabelian
metacyclic Sylow `p`-subgroup (`p`-group of full `p`-part: `p ∤ |N : P|`) with
`p > 2`, then `p` divides `|N : N'|`. Induction on `|P| ≤ n`; the inductive
step passes to `N ⧸ Y` for a normal `Y` of order `p` with `P/Y` nonabelian,
and the terminal case is `thm1015_base`. -/
private theorem thm1015_aux (n : ℕ) :
    ∀ {N : Type*} [Group N] [Finite N] {P : Subgroup N},
      P.Normal → IsPGroup p ↥P → ¬(p ∣ P.index) →
      IsMetacyclic ↥P → (¬ ∀ x y : ↥P, x * y = y * x) →
      2 < p →
      Nat.card ↥P ≤ n →
      p ∣ (commutator N).index := by
  induction n with
  | zero =>
    intro N _ _ P _ _ _ _ _ _ hle
    have : 0 < Nat.card ↥P := Nat.card_pos
    omega
  | succ n ih =>
    intro N _ _ P hPn hPp hPidx hmeta hnonab hp2 hle
    classical
    have hp_prime : p.Prime := hp.out
    by_cases hquot : ∃ Y : Subgroup N, Y.Normal ∧ Y ≤ P ∧ Nat.card ↥Y = p ∧
        ¬ ⁅P, P⁆ ≤ Y
    · -- some order-`p` normal `Y` has nonabelian `P/Y`: induct in `N ⧸ Y`
      obtain ⟨Y, hYn, hYP, hYcard, hYcomm⟩ := hquot
      haveI := hYn
      have hfsurj : Function.Surjective (QuotientGroup.mk' Y) :=
        QuotientGroup.mk'_surjective Y
      set Pq : Subgroup (N ⧸ Y) := P.map (QuotientGroup.mk' Y) with hPq_def
      haveI hPqn : Pq.Normal := Subgroup.Normal.map hPn _ hfsurj
      -- the image is again a `p`-group …
      have hPqp : IsPGroup p ↥Pq :=
        IsPGroup.of_surjective (hPp.of_equiv (MulEquiv.refl _)) ((QuotientGroup.mk' Y).subgroupMap P)
          ((QuotientGroup.mk' Y).subgroupMap_surjective P)
      -- … of the same (unchanged) index …
      have hPqidx : Pq.index = P.index := by
        rw [hPq_def, Subgroup.index_map, QuotientGroup.ker_mk', sup_of_le_left hYP,
          MonoidHom.range_eq_top_of_surjective _ hfsurj, Subgroup.index_top, mul_one]
      -- … metacyclic …
      have hmetaq : IsMetacyclic ↥Pq :=
        hmeta.of_surjective ((QuotientGroup.mk' Y).subgroupMap_surjective P)
      -- … and of cardinality `|P| / p`
      have hcard_mul : Nat.card ↥Pq * p = Nat.card ↥P := by
        have h1 := Subgroup.card_mul_index Pq
        have h2 := Subgroup.card_mul_index Y
        have h3 := Subgroup.card_mul_index P
        have h4 : Nat.card (N ⧸ Y) = Y.index := (Subgroup.index_eq_card Y).symm
        have hidx_pos : 0 < P.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
        refine Nat.eq_of_mul_eq_mul_right hidx_pos ?_
        have : Nat.card ↥Pq * Pq.index = Nat.card (N ⧸ Y) := h1
        rw [hPqidx, h4] at this
        -- `card Pq * P.index * p = Y.index * p = card Y * Y.index = card N = card P * P.index`
        calc Nat.card ↥Pq * p * P.index
            = Nat.card ↥Pq * P.index * p := by ring
          _ = Y.index * p := by rw [this]
          _ = p * Y.index := by ring
          _ = Nat.card ↥Y * Y.index := by rw [hYcard]
          _ = Nat.card N := h2
          _ = Nat.card ↥P * P.index := h3.symm
      have hcard_le : Nat.card ↥Pq ≤ n := by
        have hpos : 0 < Nat.card ↥Pq := Nat.card_pos
        nlinarith [hcard_mul, hle, hp2, hpos]
      -- `P/Y` is nonabelian: were it abelian, `⁅P, P⁆` would map to `⊥`, i.e. land in `Y`
      have hQnonab : ¬ ∀ x y : ↥Pq, x * y = y * x := by
        intro hcomm
        refine hYcomm ?_
        have hbot : ⁅Pq, Pq⁆ = ⊥ := by
          rw [eq_bot_iff, Subgroup.commutator_le]
          intro g₁ hg₁ g₂ hg₂
          have := hcomm ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
          have hcoe : g₁ * g₂ = g₂ * g₁ := congrArg Subtype.val this
          simp [commutatorElement_def, hcoe]
        have hmap : (⁅P, P⁆ : Subgroup N).map (QuotientGroup.mk' Y) = ⊥ := by
          rw [Subgroup.map_commutator]
          exact hbot
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
        exact hmap
      have hres := ih hPqn hPqp (by rw [hPqidx]; exact hPidx) hmetaq hQnonab hp2 hcard_le
      exact dvd_trans hres (index_commutator_dvd_of_surjective hfsurj)
    · -- every order-`p` normal subgroup has abelian `P/Y`: the base case applies
      push Not at hquot
      exact thm1015_base hPn hPp hPidx hmeta hnonab hp2 hquot

/-- **Isaacs Theorem 10.15**: let `P ⊴ N` with `P` a nonabelian metacyclic
Sylow `p`-subgroup of the finite group `N`, and `p > 2`. Then `p` divides
`|N : N'|`. -/
theorem dvd_index_commutator_of_normal_metacyclic_sylow
    {N : Type*} [Group N] [Finite N] (hp2 : 2 < p) (P : Sylow p N)
    (hPn : (P : Subgroup N).Normal)
    (hmeta : IsMetacyclic ↥(P : Subgroup N))
    (hnonab : ¬ ∀ x y : ↥(P : Subgroup N), x * y = y * x) :
    p ∣ (commutator N).index :=
  thm1015_aux (Nat.card ↥(P : Subgroup N)) hPn P.isPGroup'
    (P.not_dvd_index) hmeta hnonab hp2 le_rfl

end

end OddOrder.Isaacs.Ch10
