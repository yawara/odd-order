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
open OddOrder.BG.Ch1
open scoped commutatorElement

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
  sorry

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
