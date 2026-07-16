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

/-- **Isaacs Theorem 10.15**, inductive core: if `P ⊴ N` is a nonabelian
metacyclic Sylow `p`-subgroup (`p`-group of full `p`-part: `p ∤ |N : P|`) with
`p > 2`, then `p` divides `|N : N'|`. Induction on `|P| ≤ n`. -/
private theorem thm1015_aux (n : ℕ) :
    ∀ {N : Type*} [Group N] [Finite N] {P : Subgroup N},
      P.Normal → IsPGroup p ↥P → ¬(p ∣ P.index) →
      IsMetacyclic ↥P → (¬ ∀ x y : ↥P, x * y = y * x) →
      2 < p →
      Nat.card ↥P ≤ n →
      p ∣ (commutator N).index := by
  sorry

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
