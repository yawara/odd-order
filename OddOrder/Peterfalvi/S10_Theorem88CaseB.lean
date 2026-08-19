/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.CyclicSubgroupUniqueness
import OddOrder.GroupTheory.TISubset

/-!
# Peterfalvi Section 10, Theorem (8.8) case (b) and result (8.9)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 10 "Structure of a Minimal Simple Group of Odd Order", pp. 44--49
(book pages `references/peterfalvi/pages/peterfalvi-p046.png`,
`peterfalvi-p047.png`).

⚠ The repository module number is the book **result** chapter number **plus two**
(`S10` ↔ results `(8.x)`).

## Main definitions

* `Theorem88CaseBData` -- the full data of case (b) of Theorem (8.8): a cyclic
  `W = W₁ × W₂` with both factors nontrivial satisfying (8.4.e), and two maximal
  subgroups `S`, `T` satisfying (b1)--(b4).

## Main results

* `Theorem88CaseBData.derivedInG_inf_centralizer_W1_eq` -- **Peterfalvi (8.9)** in
  intrinsic form: `C_{S'}(W₁) = W₂`.
* `Theorem88CaseBData.typePData_W2_eq` -- **Peterfalvi (8.9)** as stated in the book:
  the group denoted `W₂` in Theorem (8.8) coincides with the group denoted `W₂` in
  (8.4.d) with `M = S`.

Theorem (8.8) itself is a *reference* in Peterfalvi ("[BG], §16, Theorem I,
Proposition 16.1, Theorem B and Theorem C(3)"); it is discharged on the BG side and
consumed through this datum.  (8.9), by contrast, carries a proof in the book, which
is what this file formalises.
-/

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (8.8), case (b)** (book p. 46): `G` contains a cyclic subgroup
`W = W₁ × W₂` with `W₁ ≠ 1` and `W₂ ≠ 1`, which satisfies (8.4.e), and two maximal
subgroups `S` and `T` such that

* (b1) `S = [S,S] ⋊ W₁`, `T = [T,T] ⋊ W₂` and `S ∩ T = W`;
* (b2) `S` or `T` is of Type II;
* (b3) `S` and `T` are of Type II, III, IV or V (that is, `IsTypeNonI`);
* (b4) every maximal subgroup of `G` is conjugate to `S` or to `T`, or is of Type I.

Every clause of the book statement is a field: the direct-product decomposition
(`W_eq`, `W1_inf_W2_eq_bot`), the nontriviality of both factors, the (8.4.e)
normalizer law, the two semidirect decompositions and the intersection `S ∩ T = W`,
the Type-II member, the type restriction and the covering. -/
structure Theorem88CaseBData (G : Type*) [Group G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  /-- `W = W₁ × W₂`, first half: `W` is the join of the two factors. -/
  W_eq : W = W1 ⊔ W2
  /-- `W = W₁ × W₂`, second half: the two factors intersect trivially. -/
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W_cyclic : IsCyclic ↥W
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  /-- **(8.4.e)** for `W`: every nonempty subset `X` of `V = W − (W₁ ∪ W₂)` has
  `N_G(X) = W`. -/
  normalizer_V : ∀ X : Set G, X.Nonempty →
    X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W
  /-- (b3) for `S`. -/
  S_nonI : IsTypeNonI S
  /-- (b3) for `T`. -/
  T_nonI : IsTypeNonI T
  /-- (b2). -/
  one_typeII : IsTypeII S ∨ IsTypeII T
  /-- (b1): `W₁ ≤ S` and `S = [S,S] ⋊ W₁` (so `W₁` complements `S' = [S,S]` in `S`). -/
  W1_le_S : W1 ≤ S
  W2_le_T : W2 ≤ T
  S_compl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (W1.subgroupOf S)
  T_compl : Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)
  /-- (b1), last clause: `S ∩ T = W`. -/
  S_inf_T_eq_W : S ⊓ T = W
  /-- (b4): every maximal subgroup of `G` is conjugate to `S` or to `T`, or is of Type I. -/
  cover : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
    IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = T)

/-- **(8.4.e) from the BG §14 TI-set** — the route both producers of `Theorem88CaseBData` use.

BG Theorem 14.7 (`typeP_duality`) hands out two facts about the κ-Hall pair `K`, `K*` of a
type-`P` maximal subgroup: the join `K ⊔ K*` is cyclic, and `Ẑ = (K ⊔ K*) − (K ∪ K*)`
(`OddOrder.BG.Ch4.S14.zTilde`, definitionally the set below) is a TI-subset with
normalizer-bound `K ⊔ K*`.  Together these *are* (8.4.e): a cyclic host is commutative, so
`set_normalizer_eq_of_subset_of_commute` applies.

Note that neither conjunct mentions the dual maximal subgroup, so a producer holding only the
pair `(K, K*)` can supply (8.4.e) without identifying the `∃!` partner — and without a
`TypePData` carrier (which would additionally demand type-`P₂`-ness and a `K`-invariant
`(κ∪σ)′`-Hall complement). -/
theorem normalizer_V_of_isTISubset {A B : Subgroup G} (hcyc : IsCyclic ↥(A ⊔ B))
    (hTI : IsTISubset (((A ⊔ B : Subgroup G) : Set G) \ ((A : Set G) ∪ (B : Set G))) (A ⊔ B)) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ ((A ⊔ B : Subgroup G) : Set G) \ ((A : Set G) ∪ (B : Set G)) →
      Subgroup.normalizer X = A ⊔ B := by
  have := hcyc
  let : CommGroup ↥(A ⊔ B) := IsCyclic.commGroup
  refine fun X hX hXV => hTI.set_normalizer_eq_of_subset_of_commute Set.sdiff_subset ?_ hX hXV
  exact fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(A ⊔ B)) ⟨y, hy⟩)

namespace Theorem88CaseBData

variable (cb : Theorem88CaseBData G)

theorem W1_le_W : cb.W1 ≤ cb.W := cb.W_eq ▸ le_sup_left

theorem W2_le_W : cb.W2 ≤ cb.W := cb.W_eq ▸ le_sup_right

theorem W_le_S : cb.W ≤ cb.S := cb.S_inf_T_eq_W ▸ inf_le_left

theorem W_le_T : cb.W ≤ cb.T := cb.S_inf_T_eq_W ▸ inf_le_right

theorem W2_le_S : cb.W2 ≤ cb.S := cb.W2_le_W.trans cb.W_le_S

/-- The exceptional set `V = W − (W₁ ∪ W₂)` of the case-(b) configuration; the set on which
(8.4.e) pins the normalizer. -/
def V : Set G := (cb.W : Set G) \ ((cb.W1 : Set G) ∪ (cb.W2 : Set G))

/-- `V = W − (W₁ ∪ W₂)` is nonempty: a generator of the cyclic `W` lies in no proper subgroup,
and both `W₁` and `W₂` are proper (if `W₁ = W` then `W₂ ≤ W₁`, so `W₂ = W₁ ⊓ W₂ = 1`). -/
theorem V_nonempty : cb.V.Nonempty := by
  have := cb.W_cyclic
  obtain ⟨g0, hg0⟩ := IsCyclic.exists_generator (α := ↥cb.W)
  -- A proper subgroup of `W` misses the generator.
  have hnot : ∀ A : Subgroup G, A ≤ cb.W → (cb.W : Set G) ⊆ (A : Set G) ∨ (g0 : G) ∉ A := by
    intro A hA
    by_cases hg : (g0 : G) ∈ A
    · refine Or.inl ?_
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥cb.W) ∈ A.subgroupOf cb.W := by
        obtain ⟨n, hn⟩ := hg0 ⟨x, hx⟩
        rw [← hn]
        exact zpow_mem (Subgroup.mem_subgroupOf.mpr hg) n
      exact Subgroup.mem_subgroupOf.mp hx'
    · exact Or.inr hg
  have hW1prop : (g0 : G) ∉ cb.W1 := by
    rcases hnot cb.W1 cb.W1_le_W with h | h
    · exact absurd (le_bot_iff.mp (cb.W1_inf_W2_eq_bot ▸
        le_inf (fun x hx => h (cb.W2_le_W hx)) le_rfl)) cb.W2_nontrivial
    · exact h
  have hW2prop : (g0 : G) ∉ cb.W2 := by
    rcases hnot cb.W2 cb.W2_le_W with h | h
    · exact absurd (le_bot_iff.mp (cb.W1_inf_W2_eq_bot ▸
        le_inf (le_rfl : cb.W1 ≤ cb.W1) fun x hx => h (cb.W1_le_W hx))) cb.W1_nontrivial
    · exact h
  exact ⟨(g0 : G), g0.2, by simpa using ⟨hW1prop, hW2prop⟩⟩

/-- Decompose an element of `W = W₁ ⊔ W₂` as a product `a · b` with `a ∈ W₁`, `b ∈ W₂`.
`W` is cyclic, hence abelian, so `Subgroup.mem_sup` applies inside `↥W`. -/
theorem mem_W_decomp {x : G} (hx : x ∈ cb.W) : ∃ a ∈ cb.W1, ∃ b ∈ cb.W2, a * b = x := by
  have := cb.W_cyclic
  let : CommGroup ↥cb.W := IsCyclic.commGroup
  have hsup : cb.W1.subgroupOf cb.W ⊔ cb.W2.subgroupOf cb.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup cb.W1_le_W cb.W2_le_W, ← cb.W_eq, Subgroup.subgroupOf_self]
  have hmem : (⟨x, hx⟩ : ↥cb.W) ∈ cb.W1.subgroupOf cb.W ⊔ cb.W2.subgroupOf cb.W := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  exact ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb,
    by simpa using congrArg Subtype.val hab⟩

/-- The two factors of the cyclic `W` have **coprime orders** — the first step of the proof of
(8.9) ("Since `W` is cyclic, `|W₁|` and `|W₂|` are relatively prime"). -/
theorem coprime_card_W1_W2 [Finite G] :
    Nat.Coprime (Nat.card ↥cb.W1) (Nat.card ↥cb.W2) :=
  haveI := cb.W_cyclic
  coprime_card_of_inf_eq_bot_of_le_cyclic cb.W1_le_W cb.W2_le_W cb.W1_inf_W2_eq_bot

/-- `W₂ ⊆ S'`, the commutator subgroup of `S` (book p. 46).  `W₂ ≤ W ≤ S`, and the index
`[S : S'] = |W₁|` is coprime to `|W₂|` by `coprime_card_W1_W2`, so `W₂` dies in `S/S'`. -/
theorem W2_le_derivedInG_S [Finite G] : cb.W2 ≤ derivedInG cb.S := by
  have hidx : ((derivedInG cb.S).subgroupOf cb.S).index = Nat.card ↥cb.W1 := by
    rw [cb.S_compl.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe cb.W1_le_S).toEquiv]
  have : ((derivedInG cb.S).subgroupOf cb.S).Normal := by
    rw [show (derivedInG cb.S).subgroupOf cb.S = commutator ↥cb.S from
      Subgroup.comap_map_eq_self_of_injective cb.S.subtype_injective _]
    infer_instance
  intro x hx
  set y : ↥cb.S := ⟨x, cb.W2_le_S hx⟩ with hy
  -- `orderOf y = orderOf x` divides `|W₂|`.
  have hord2 : orderOf y ∣ Nat.card ↥cb.W2 := by
    have h1 : orderOf y = orderOf x := Subgroup.orderOf_mk (H := cb.S) x (cb.W2_le_S hx)
    have h2 : orderOf (⟨x, hx⟩ : ↥cb.W2) = orderOf x := Subgroup.orderOf_mk (H := cb.W2) x hx
    rw [h1, ← h2]
    exact orderOf_dvd_natCard _
  -- The image of `y` in `S/S'` has order dividing both `|W₂|` and `[S : S'] = |W₁|`.
  have hord1 : orderOf (QuotientGroup.mk y : ↥cb.S ⧸ (derivedInG cb.S).subgroupOf cb.S) ∣
      Nat.card ↥cb.W1 := by
    rw [← hidx, Subgroup.index]
    exact orderOf_dvd_natCard _
  have hdvd : orderOf (QuotientGroup.mk y : ↥cb.S ⧸ (derivedInG cb.S).subgroupOf cb.S) ∣
      Nat.card ↥cb.W2 :=
    (orderOf_map_dvd (QuotientGroup.mk' ((derivedInG cb.S).subgroupOf cb.S)) y).trans hord2
  have hone : orderOf (QuotientGroup.mk y : ↥cb.S ⧸ (derivedInG cb.S).subgroupOf cb.S) = 1 :=
    Nat.eq_one_of_dvd_coprimes cb.coprime_card_W1_W2 hord1 hdvd
  have : y ∈ (derivedInG cb.S).subgroupOf cb.S :=
    QuotientGroup.eq_one_iff y |>.mp (orderOf_eq_one_iff.mp hone)
  exact Subgroup.mem_subgroupOf.mp this

/-- `W ∩ S' = W₂`, the last step of the proof of (8.9): decompose `x ∈ W` as `a·b` with
`a ∈ W₁`, `b ∈ W₂ ≤ S'`; then `a = x·b⁻¹ ∈ W₁ ∩ S' = 1` by the complement `S = S' ⋊ W₁`. -/
theorem W_inf_derivedInG_S_le_W2 [Finite G] : cb.W ⊓ derivedInG cb.S ≤ cb.W2 := by
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := cb.mem_W_decomp hx.1
  have hbD : b ∈ derivedInG cb.S := cb.W2_le_derivedInG_S hb
  have haD : a ∈ derivedInG cb.S := by
    have hrw : a = x * b⁻¹ := by rw [← hab]; group
    rw [hrw]; exact mul_mem hx.2 (inv_mem hbD)
  have hdisj := cb.S_compl.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have ha1 : a = 1 := congrArg Subtype.val
    (hdisj (x := ⟨a, cb.W1_le_S ha⟩) (Subgroup.mem_subgroupOf.mpr haD)
      (Subgroup.mem_subgroupOf.mpr ha))
  rw [← hab, ha1, one_mul]
  exact hb

/-- The centralizer of `W` is contained in `W`: it fixes `V = W − (W₁ ∪ W₂)` pointwise, hence
normalizes it, and `N_G(V) = W` by (8.4.e). -/
theorem centralizer_W_le_W : Subgroup.centralizer (cb.W : Set G) ≤ cb.W := by
  refine le_trans ?_ (le_of_eq (cb.normalizer_V cb.V cb.V_nonempty Set.Subset.rfl))
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hfix : ∀ w ∈ cb.W, x * w * x⁻¹ = w := by
    intro w hw
    rw [← hx w hw]
    group
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh; rwa [hfix h hh.1]
  · intro hh
    have hW : x * h * x⁻¹ ∈ cb.W := hh.1
    have hcomm : (x * h * x⁻¹) * x = x * (x * h * x⁻¹) := hx _ hW
    have heq : x * h = x * (x * h * x⁻¹) := by rw [← hcomm]; group
    have hfin : h = x * h * x⁻¹ := mul_left_cancel heq
    rwa [hfin]

/-- **Peterfalvi (8.9)** (intrinsic form, book pp. 46--47): in case (b) of Theorem (8.8),
`C_{S'}(W₁) = W₂`.

The proof follows the book verbatim.  `W₂ ⊆ W ⊆ S` and `|W₁|`, `|W₂|` are coprime because `W` is
cyclic, so `W₂ ⊆ S'` (`W2_le_derivedInG_S`) and hence `W₂ ⊆ C_{S'}(W₁)` (the factors commute
inside the abelian `W`).  By (8.4.d) with `M = S`, `C_{S'}(W₁)` is the cyclic group `W₂(S)` of the
type-`P` datum, so `W₁ C_{S'}(W₁)` is abelian and `C_{S'}(W₁) ⊆ C_G(W)`.  As `W` satisfies (8.4.e),
`C_G(W) ⊆ N_G(V) = W` (`centralizer_W_le_W`), whence `C_{S'}(W₁) ⊆ W ∩ S' = W₂`.

The type-`P` datum of `S` enters only through (8.4.d); the hypothesis `data.W1 = cb.W1` is
legitimate by the remark following Definition (8.4) ("properties (8.4.b--e) hold whatever
complement `W₁` is chosen") together with (8.8.b1). -/
theorem derivedInG_inf_centralizer_W1_eq [Finite G] (data : TypePData cb.S)
    (hW1 : data.W1 = cb.W1) :
    derivedInG cb.S ⊓ Subgroup.centralizer (cb.W1 : Set G) = cb.W2 := by
  have := cb.W_cyclic
  let : CommGroup ↥cb.W := IsCyclic.commGroup
  -- (8.4.d) with `M = S`: the intersection is the cyclic `W₂` of the type-`P` datum.
  have hkey : derivedInG cb.S ⊓ Subgroup.centralizer (cb.W1 : Set G) = data.W2 := by
    rw [← hW1]; exact data.derivedInG_inf_centralizer_W1_eq
  have := data.W2_cyclic
  let : CommGroup ↥data.W2 := IsCyclic.commGroup
  -- `W₂ ⊆ C_{S'}(W₁)`: `W₂ ⊆ S'`, and `W₁`, `W₂` commute inside the abelian `W`.
  have hle1 : cb.W2 ≤ data.W2 := by
    rw [← hkey]
    refine le_inf cb.W2_le_derivedInG_S ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val
      (mul_comm (⟨h, cb.W1_le_W hh⟩ : ↥cb.W) ⟨x, cb.W2_le_W hx⟩)
  rw [hkey]
  refine le_antisymm ?_ hle1
  -- `C_{S'}(W₁) ⊆ C_G(W)`: it centralizes `W₁` by definition and `W₂` because it is abelian and
  -- contains `W₂`.
  have hcent : data.W2 ≤ Subgroup.centralizer (cb.W : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨a, ha, b, hb, hab⟩ := cb.mem_W_decomp hh
    have hxa : a * x = x * a := by
      have hxC : x ∈ Subgroup.centralizer (cb.W1 : Set G) := (hkey ▸ hx).2
      exact (Subgroup.mem_centralizer_iff.mp hxC) a ha
    have hxb : b * x = x * b :=
      congrArg Subtype.val (mul_comm (⟨b, hle1 hb⟩ : ↥data.W2) ⟨x, hx⟩)
    rw [← hab, mul_assoc, hxb, ← mul_assoc, hxa, mul_assoc]
  -- `C_G(W) ⊆ W` by (8.4.e), and `W ∩ S' = W₂`.
  refine le_trans (le_inf (hcent.trans cb.centralizer_W_le_W) ?_) cb.W_inf_derivedInG_S_le_W2
  rw [← hkey]
  exact inf_le_left

/-- **Peterfalvi (8.9)** as stated in the book (p. 46): *the group denoted by `W₂` in Theorem
(8.8) coincides with the group denoted by `W₂` in (8.4.d) with `M = S`.*

The (8.4.d) group is `C_{S'}(W₁)` (`TypePData.derivedInG_inf_centralizer_W1_eq`), which
`derivedInG_inf_centralizer_W1_eq` identifies with the (8.8) factor `W₂`. -/
theorem typePData_W2_eq [Finite G] (data : TypePData cb.S) (hW1 : data.W1 = cb.W1) :
    data.W2 = cb.W2 := by
  rw [← data.derivedInG_inf_centralizer_W1_eq, hW1]
  exact cb.derivedInG_inf_centralizer_W1_eq data hW1

end Theorem88CaseBData

end OddOrder.Peterfalvi.S10
