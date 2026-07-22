/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.LengthFourReduction

/-!
# Higman's Lemma 13: the Frattini layers

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The two cases in Higman's proof are distinguished by the exponent of
`Φ(P)`.  If it has exponent two, transitivity on the ambient involutions
makes it a single normal actor-invariant composition factor.  If it has
exponent four, its square subgroup is a nontrivial proper characteristic
subgroup, so

`1 < Φ(P)² < Φ(P) < P`.

This leaf constructs that square subgroup in the ambient group and proves
both assertions.  In particular, the Frattini layers used by the later
Maschke splitting are actual normal actor-invariant subgroups rather than
posited composition data.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP uX

variable {P : Type uP} [Group P]
variable {X : Type uX} [Group X]

/-- The square subgroup of the Frattini subgroup, mapped back into the
ambient group.  This is Higman's `Φ(P)²`. -/
def frattiniSquare (P : Type uP) [Group P] : Subgroup P :=
  (Agemo (frattini P) 2 1).map (frattini P).subtype

/-- The Frattini square is contained in the Frattini subgroup. -/
theorem frattiniSquare_le_frattini :
    frattiniSquare P ≤ frattini P :=
  Subgroup.map_subtype_le (Agemo (frattini P) 2 1)

/-- The Frattini square as a normal actor-invariant subgroup of the ambient
group.  Normality comes from characteristicity inside the characteristic
Frattini subgroup. -/
def frattiniSquareNormalInvariant (act : X →* MulAut P) :
    NormalInvariantSubgroup act :=
  ⟨frattiniSquare P, by
    let hPhiInv : IsAInvariant act (frattini P) :=
      IsAInvariant.of_characteristic act
    obtain ⟨hInv, hNormal, _⟩ :=
      aInvariant_normal_map_of_characteristic
        hPhiInv (Agemo (frattini P) 2 1)
    exact ⟨hNormal, hInv⟩⟩

@[simp] theorem frattiniSquareNormalInvariant_val
    (act : X →* MulAut P) :
    (frattiniSquareNormalInvariant act).1 = frattiniSquare P :=
  rfl

/-- The Frattini subgroup of a noncommutative finite `p`-group is
nontrivial. -/
theorem frattini_ne_bot_of_not_isMulCommutative
    [Finite P] (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P) :
    frattini P ≠ (⊥ : Subgroup P) := by
  intro hPhiBot
  have hcommBot : _root_.commutator P = ⊥ :=
    le_bot_iff.mp
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        (le_of_eq hPhiBot))
  exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)

/-- In a nontrivial finite group the Frattini subgroup is proper. -/
theorem frattini_ne_top_of_nontrivial
    [Finite P] [Nontrivial P] :
    frattini P ≠ (⊤ : Subgroup P) := by
  obtain ⟨M, hM, _⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (⊥ : Subgroup P)).resolve_left bot_lt_top.ne
  exact fun htop => hM.1
    (le_antisymm le_top (htop ▸ frattini_le_coatom hM))

/-- If `Φ(P)` has exponent at most four, every element of its square
subgroup has square one. -/
theorem pow_two_eq_one_of_mem_frattiniSquare
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    {x : P} (hx : x ∈ frattiniSquare P) :
    x ^ 2 = 1 := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hz
  have hzval : (z : P) = (y : P) ^ 2 := by
    simpa using congrArg Subtype.val hy
  have hyfour : (y : P) ^ 4 = 1 := by
    simpa using congrArg Subtype.val (hfour y)
  calc
    x ^ 2 = (z : P) ^ 2 :=
      congrArg (fun a : P => a ^ 2) hzx.symm
    _ = ((y : P) ^ 2) ^ 2 := by rw [hzval]
    _ = (y : P) ^ 4 := by group
    _ = 1 := hyfour

/-- A Frattini element with nontrivial square makes `Φ(P)²` nontrivial. -/
theorem frattiniSquare_ne_bot_of_exists_pow_two_ne_one
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    frattiniSquare P ≠ (⊥ : Subgroup P) := by
  obtain ⟨z, hz⟩ := hexists
  intro hbot
  apply hz
  apply Subtype.ext
  have hzAgemo : z ^ 2 ∈ Agemo (frattini P) 2 1 := by
    simpa using
      (Agemo.mem_of_eq_pow
        (G := frattini P) (p := 2) (n := 1) z)
  have hzSquare : (z : P) ^ 2 ∈ frattiniSquare P := by
    simpa [frattiniSquare] using
      Subgroup.mem_map_of_mem (frattini P).subtype hzAgemo
  rw [hbot, Subgroup.mem_bot] at hzSquare
  exact hzSquare

/-- In the genuine exponent-four case, `Φ(P)²` is a proper subgroup of
`Φ(P)`. -/
theorem frattiniSquare_lt_frattini
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    frattiniSquare P < frattini P := by
  apply lt_of_le_of_ne frattiniSquare_le_frattini
  obtain ⟨z, hz⟩ := hexists
  intro heq
  apply hz
  apply Subtype.ext
  exact pow_two_eq_one_of_mem_frattiniSquare hPhiComm hfour
    (show (z : P) ∈ frattiniSquare P from by
      rw [heq]
      exact z.property)

/-- **Higman Lemma 13 (p. 92), exponent-four Frattini chain.**

When `Φ(P)` has exponent four, its square subgroup supplies two strict
normal actor-invariant steps below `Φ(P)`. -/
theorem frattiniSquare_strict_chain_of_exponent_four
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    normalInvariantBot Y.subtype <
        frattiniSquareNormalInvariant Y.subtype ∧
      frattiniSquareNormalInvariant Y.subtype <
        frattiniNormalInvariant Y.subtype ∧
      frattiniNormalInvariant Y.subtype <
        normalInvariantTop Y.subtype := by
  letI : Nontrivial P := by
    obtain ⟨x, y, _, _, hxy⟩ := hmulti
    exact ⟨⟨x, y, hxy⟩⟩
  constructor
  · change (⊥ : Subgroup P) < frattiniSquare P
    exact bot_lt_iff_ne_bot.mpr
      (frattiniSquare_ne_bot_of_exists_pow_two_ne_one hexists)
  constructor
  · change frattiniSquare P < frattini P
    exact frattiniSquare_lt_frattini hPhiComm hfour hexists
  · change frattini P < (⊤ : Subgroup P)
    exact lt_top_iff_ne_top.mpr frattini_ne_top_of_nontrivial

/-- In the exponent-four branch, the Frattini square covers the bottom
normal invariant term.  Indeed, every element of `Φ(P)²` has square one,
so every nonidentity element is an ambient involution. -/
theorem normalInvariantBot_covBy_frattiniSquare_of_exponent_four
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    normalInvariantBot Y.subtype ⋖
      frattiniSquareNormalInvariant Y.subtype := by
  apply covBy_iff_lt_and_eq_or_eq.mpr
  refine ⟨?_, ?_⟩
  · change (⊥ : Subgroup P) < frattiniSquare P
    exact bot_lt_iff_ne_bot.mpr
      (frattiniSquare_ne_bot_of_exists_pow_two_ne_one hexists)
  intro C hbotC hCSquare
  by_cases hCbot : C = normalInvariantBot Y.subtype
  · exact Or.inl hCbot
  right
  apply Subtype.ext
  apply le_antisymm
  · exact hCSquare
  have hCNeBot : C.1 ≠ (⊥ : Subgroup P) := by
    intro hC
    apply hCbot
    apply Subtype.ext
    exact hC
  have hinvC : involutions P ⊆ C.1 :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive C.2.2 hCNeBot
  intro z hz
  by_cases hz1 : z = 1
  · exact hz1 ▸ C.1.one_mem
  apply hinvC
  exact ⟨pow_two_eq_one_of_mem_frattiniSquare
    hPhiComm hfour hz, hz1⟩

/-- Every actor-invariant subgroup between `Φ(P)²` and `Φ(P)` is one of
the two endpoints.

This is the interval-classification content of Higman Lemma 1.  Normality
in the ambient group is not required. -/
theorem eq_frattiniSquare_or_frattini_of_invariant
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    {C : Subgroup P}
    (hCinv : IsAInvariant Y.subtype C)
    (hSquareC : frattiniSquare P ≤ C)
    (hCPhi : C ≤ frattini P) :
    C = frattiniSquare P ∨ C = frattini P := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  have htransPhi : ∀ x ∈ involutions (frattini P),
      ∀ y ∈ involutions (frattini P),
        ∃ g : Y, hPhiInv.restrict g x = y :=
    restricted_involutions_transitive Y.subtype hPhiInv (by
      intro x hx y hy
      obtain ⟨g, hg⟩ := hxi.transitive x hx y hy
      exact ⟨g, hg⟩)
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  obtain ⟨ι, hι, _e, _he, _hε, classify⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      (hP.to_subgroup (frattini P)) hPhiInv.restrict htransPhi
  letI : Fintype ι := hι
  let U : Subgroup (frattini P) := C.subgroupOf (frattini P)
  have hUInv : IsAInvariant hPhiInv.restrict U := by
    simpa [U] using hPhiInv.subgroupOf hCinv
  obtain ⟨s, _hs, hU⟩ := classify U hUInv
  cases s with
  | zero =>
      right
      have hPhiC : frattini P ≤ C :=
        Subgroup.subgroupOf_eq_top.mp (by
          simpa [U, agemo_zero_eq_top] using hU)
      exact le_antisymm hCPhi hPhiC
  | succ s =>
      left
      have hUle : U ≤ Agemo (frattini P) 2 1 := by
        rw [hU]
        exact Agemo.anti (Nat.succ_le_succ (Nat.zero_le s))
      have hCLeSquare : C ≤ frattiniSquare P := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hCPhi, frattiniSquare]
        exact Subgroup.map_mono hUle
      exact le_antisymm hCLeSquare hSquareC

/-- In the exponent-four branch, `Φ(P)²` is covered by `Φ(P)`.

Higman Lemma 1 classifies every subgroup of the commutative Frattini
subgroup invariant under the restricted actor as an Agemo layer.  A layer
containing `Φ(P)²` is therefore either `Φ(P)²` itself or all of
`Φ(P)`. -/
theorem frattiniSquare_covBy_frattini_of_exponent_four
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    frattiniSquareNormalInvariant Y.subtype ⋖
      frattiniNormalInvariant Y.subtype := by
  apply covBy_iff_lt_and_eq_or_eq.mpr
  refine ⟨?_, ?_⟩
  · change frattiniSquare P < frattini P
    exact frattiniSquare_lt_frattini hPhiComm hfour hexists
  intro C hSquareC hCPhi
  rcases eq_frattiniSquare_or_frattini_of_invariant
      hP hxi hPhiComm C.2.2 hSquareC hCPhi with hC | hC
  · exact Or.inl (Subtype.ext hC)
  · exact Or.inr (Subtype.ext hC)

/-- **Higman Lemma 13 (p. 92), exponent-four lower composition
series.**  The two strict Frattini steps are both covers. -/
theorem frattiniSquare_composition_series_of_exponent_four
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    normalInvariantBot Y.subtype ⋖
        frattiniSquareNormalInvariant Y.subtype ∧
      frattiniSquareNormalInvariant Y.subtype ⋖
        frattiniNormalInvariant Y.subtype :=
  ⟨normalInvariantBot_covBy_frattiniSquare_of_exponent_four
      hP hxi hPhiComm hfour hexists,
    frattiniSquare_covBy_frattini_of_exponent_four
      hP hxi hPhiComm hfour hexists⟩

/-- **Higman Lemma 13 (p. 92), exponent-two Frattini factor.**

If `Φ(P)` has exponent two, every nonidentity element of it is an ambient
involution.  Actor transitivity therefore puts all of `Φ(P)` in every
nontrivial normal invariant subgroup, so `Φ(P)` covers the bottom term. -/
theorem normalInvariantBot_covBy_frattini_of_pow_two_eq_one
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    normalInvariantBot Y.subtype ⋖
      frattiniNormalInvariant Y.subtype := by
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) :=
    frattini_ne_bot_of_not_isMulCommutative hP hncomm
  apply covBy_iff_lt_and_eq_or_eq.mpr
  refine ⟨?_, ?_⟩
  · change (⊥ : Subgroup P) < frattini P
    exact bot_lt_iff_ne_bot.mpr hPhiNeBot
  intro C hbotC hCPhi
  by_cases hCbot : C = normalInvariantBot Y.subtype
  · exact Or.inl hCbot
  right
  apply Subtype.ext
  apply le_antisymm
  · exact hCPhi
  have hCNeBot : C.1 ≠ (⊥ : Subgroup P) := by
    intro hC
    apply hCbot
    apply Subtype.ext
    exact hC
  have hinvC : involutions P ⊆ C.1 :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive C.2.2 hCNeBot
  intro z hz
  by_cases hz1 : z = 1
  · exact hz1 ▸ C.1.one_mem
  apply hinvC
  refine ⟨?_, hz1⟩
  exact congrArg Subtype.val (htwo ⟨z, hz⟩)

end OddOrder.Higman.Suzuki2Groups
