/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven.TraceFormula
import OddOrder.Higman.Suzuki2Groups.HigmanFiniteFieldTrace
import OddOrder.Higman.Suzuki2Groups.HigmanSquareMap
import OddOrder.Higman.Suzuki2Groups.HigmanXiLengthTwo
import OddOrder.Higman.Suzuki2Groups.HigmanTripleBracketContradiction
import OddOrder.GroupTheory.RepresentationTheory.AInvariantSubrep

/-!
# Higman's Lemma 11: excluding a proper field extension

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 11, p. 89.

This leaf formalizes the contradiction after the trace calculation.  The
xi-length-two structure makes the actual first-layer square map nonzero away
from zero, while Lemma 10 supplies a nonzero trace-zero coordinate in every
proper odd-degree field extension.  Therefore the relative degree is one.
-/

set_option autoImplicit false

open scoped IsMulCommutative
open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open Module
open scoped TensorProduct BigOperators

namespace OddOrder.Higman.Suzuki2Groups

universe u uK uL uW

local instance properExtensionLayerIsMulCommutative
    (P : Type u) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance properExtensionLayerCommGroup
    (P : Type u) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance properExtensionLayerZModTwoModule
    (P : Type u) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-! ## The original actor on the lower-central layers

Higman first replaces the cyclic actor, if necessary, so that its prime
divisors are precisely among those of the number of involutions (p. 87).
After that replacement the actor itself, rather than a further subgroup, acts
irreducibly on the first layer.  The results in this section keep that actor
fixed; in particular, no irreducibility claim is made after restriction to a
proper subgroup. -/

private def layerZeroQuotientHom (P : Type u) [Group P] :
    P →* lowerCentralLayer P 0 :=
  (QuotientGroup.mk' (lowerCentralLayerKernel P 0)).comp
    { toFun := fun x => ⟨x, by simp [lowerCentralTerm]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

private theorem layerZeroQuotientHom_surjective
    (P : Type u) [Group P] :
    Function.Surjective (layerZeroQuotientHom P) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 0) q
  exact ⟨x, rfl⟩

private theorem layerZeroQuotientHom_ker_eq_frattini
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup 2 P) :
    (layerZeroQuotientHom P).ker = frattini P := by
  ext x
  rw [MonoidHom.mem_ker]
  let x0 : lowerCentralTerm P 0 := ⟨x, by simp [lowerCentralTerm]⟩
  change QuotientGroup.mk' (lowerCentralLayerKernel P 0) x0 = 1 ↔ _
  constructor
  · intro hx
    have hx0 : x0 ∈ lowerCentralLayerKernel P 0 :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 0] at hx0
    change x ∈ lowerCentralLayerKernelInAmbient P 0 at hx0
    rwa [lowerCentralLayerKernelInAmbient_zero_eq_frattini P hP] at hx0
  · intro hx
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 0]
    change x ∈ lowerCentralLayerKernelInAmbient P 0
    rwa [lowerCentralLayerKernelInAmbient_zero_eq_frattini P hP]

private theorem frattini_ne_top_of_nontrivial
    {P : Type u} [Group P] [Finite P] [Nontrivial P] :
    frattini P ≠ ⊤ := by
  obtain ⟨M, hM, _⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup P)).resolve_left
      bot_lt_top.ne
  exact fun htop => hM.1
    (le_antisymm le_top (htop ▸ frattini_le_coatom hM))

/-- Under Higman's xi-length-two hypotheses, the original cyclic actor acts
irreducibly on the first lower-central layer.  This is the source-facing
irreducibility assertion used in Lemma 11 (pp. 87–88). -/
theorem lowerCentralLayerZeroRepresentation_isIrreducible_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype) :
    Representation.IsIrreducible
      (lowerCentralLayerRepresentation Y.subtype 0) := by
  classical
  have hcomm_ne : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h => hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcomm_ne
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  have hPhi_ne_bot : frattini P ≠ (⊥ : Subgroup P) := by
    rw [← (commutator_eq_frattini_and_frattini_eq_center
      hP hncomm hxi hlen).1]
    exact hcomm_ne
  have hPhi_ne_top : frattini P ≠ (⊤ : Subgroup P) :=
    frattini_ne_top_of_nontrivial
  have hPhi_lt_top : frattini P < (⊤ : Subgroup P) :=
    lt_of_le_of_ne le_top hPhi_ne_top
  obtain ⟨x0, -, hx0Phi⟩ := SetLike.exists_of_lt hPhi_lt_top
  let q0 : P →* lowerCentralLayer P 0 := layerZeroQuotientHom P
  have hqx0 : q0 x0 ≠ 1 := by
    intro hx
    apply hx0Phi
    have hxker : x0 ∈ q0.ker := MonoidHom.mem_ker.mpr hx
    rw [show q0.ker = frattini P from
      layerZeroQuotientHom_ker_eq_frattini hP] at hxker
    exact hxker
  letI : Nontrivial (lowerCentralLayer P 0) := ⟨q0 x0, 1, hqx0⟩
  have hPhi_bot :
      frattiniNormalInvariant Y.subtype ≠ normalInvariantBot Y.subtype := by
    intro h
    exact hPhi_ne_bot (congrArg Subtype.val h)
  have hPhi_top :
      frattiniNormalInvariant Y.subtype ≠ normalInvariantTop Y.subtype := by
    intro h
    exact hPhi_ne_top (congrArg Subtype.val h)
  have hcover := hlen.covBy_top_of_ne_bot_of_ne_top hPhi_bot hPhi_top
  let rho := lowerCentralLayerRepresentation Y.subtype 0
  have hbot_ne_top : (⊥ : Subrepresentation rho) ≠ ⊤ := by
    exact fun hEq => bot_ne_top
      (congrArg Subrepresentation.toSubmodule hEq)
  letI : Nontrivial (Subrepresentation rho) :=
    ⟨⊥, ⊤, hbot_ne_top⟩
  refine IsSimpleOrder.of_forall_eq_top fun S hSne => ?_
  let Phi : Submodule (ZMod 2) (Additive (lowerCentralLayer P 0)) ≃o
      Subgroup (lowerCentralLayer P 0) :=
    elabSubmoduleSubgroupEquiv 2
  let J : Subgroup (lowerCentralLayer P 0) := Phi S.toSubmodule
  let q : P →* lowerCentralLayer P 0 := layerZeroQuotientHom P
  let A : Subgroup P := J.comap q
  have hJinv : IsAInvariant (lowerCentralLayerAction Y.subtype 0) J := by
    rw [isAInvariant_iff_smul_mem]
    intro y z hz
    have hz' : Additive.ofMul z ∈ S.toSubmodule :=
      (mem_elabSubmoduleSubgroupEquiv S.toSubmodule z).mp hz
    have hs := S.apply_mem_toSubmodule y hz'
    apply (mem_elabSubmoduleSubgroupEquiv S.toSubmodule _).mpr
    change rho y (Additive.ofMul z) ∈ S.toSubmodule at hs
    simpa [rho, lowerCentralLayerRepresentation_apply] using hs
  have hAinv : IsAInvariant Y.subtype A := by
    rw [isAInvariant_iff_smul_mem]
    intro y x hx
    change q ((y : MulAut P) x) ∈ J
    have hxJ : q x ∈ J := hx
    have hacted := hJinv.smul_mem y hxJ
    have heq : q ((y : MulAut P) x) =
        lowerCentralLayerAction Y.subtype 0 y (q x) := by
      change QuotientGroup.mk' (lowerCentralLayerKernel P 0)
          (⟨(y : MulAut P) x, _⟩ : lowerCentralTerm P 0) =
        QuotientGroup.mk' (lowerCentralLayerKernel P 0)
          (lowerCentralTermAction Y.subtype 0 y
            (⟨x, _⟩ : lowerCentralTerm P 0))
      apply congrArg (QuotientGroup.mk' (lowerCentralLayerKernel P 0))
      apply Subtype.ext
      rfl
    rw [heq]
    exact hacted
  haveI : J.Normal := inferInstance
  haveI : A.Normal := Subgroup.Normal.comap inferInstance q
  let Ani : NormalInvariantSubgroup Y.subtype := ⟨A, inferInstance, hAinv⟩
  have hPhi_le_A : frattiniNormalInvariant Y.subtype ≤ Ani := by
    intro x hx
    change q x ∈ J
    have hxker : x ∈ q.ker := by
      rw [show q.ker = frattini P from
        layerZeroQuotientHom_ker_eq_frattini hP]
      exact hx
    rw [MonoidHom.mem_ker.mp hxker]
    exact J.one_mem
  have hA_le_top : Ani ≤ normalInvariantTop Y.subtype := by
    change A ≤ (⊤ : Subgroup P)
    exact le_top
  rcases hcover.eq_or_eq hPhi_le_A hA_le_top with hAeqPhi | hAeqTop
  · exfalso
    apply hSne
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊥
    apply Phi.injective
    change J = Phi ⊥
    rw [Phi.map_bot]
    have hAker : A = q.ker := by
      calc
        A = frattini P := congrArg Subtype.val hAeqPhi
        _ = q.ker := (layerZeroQuotientHom_ker_eq_frattini hP).symm
    apply le_antisymm
    · intro z hz
      obtain ⟨x, rfl⟩ := layerZeroQuotientHom_surjective P z
      have hxA : x ∈ A := hz
      have hxker : x ∈ q.ker := by rwa [← hAker]
      exact MonoidHom.mem_ker.mp hxker
    · exact bot_le
  · apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    apply Phi.injective
    change J = Phi ⊤
    rw [Phi.map_top]
    apply le_antisymm le_top
    intro z _
    obtain ⟨x, rfl⟩ := layerZeroQuotientHom_surjective P z
    have hxA : x ∈ A := by
      rw [show A = ⊤ from congrArg Subtype.val hAeqTop]
      exact Subgroup.mem_top x
    exact hxA

/-- The denominator of the second lower-central layer is trivial under the
xi-length-two hypotheses. -/
theorem lowerCentralLayerKernel_one_eq_bot_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype) :
    lowerCentralLayerKernel P 1 = ⊥ := by
  have hAmbientK1 : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot hP hncomm hxi hlen, sup_bot_eq,
      lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_agemo_one_map_eq_bot hP hncomm hxi hlen]
  rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbientK1]
  simp

/-- The original xi-actor is transitive on the nonzero vectors of the actual
second lower-central layer. -/
theorem lowerCentralLayerOneRepresentation_transitive_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype) :
    ∀ v w : Additive (lowerCentralLayer P 1),
      v ≠ 0 → w ≠ 0 →
        ∃ y : Y, lowerCentralLayerRepresentation Y.subtype 1 y v = w := by
  intro v w hv hw
  obtain ⟨z, hz⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 1) v.toMul
  obtain ⟨t, ht⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 1) w.toMul
  have hzPhi : (z : P) ∈ frattini P := by
    rw [← lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen]
    exact z.2
  have htPhi : (t : P) ∈ frattini P := by
    rw [← lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen]
    exact t.2
  have hzsq : (z : P) ^ 2 = 1 := congrArg Subtype.val
    (frattini_sq_eq_one hP hncomm hxi hlen ⟨z, hzPhi⟩)
  have htsq : (t : P) ^ 2 = 1 := congrArg Subtype.val
    (frattini_sq_eq_one hP hncomm hxi hlen ⟨t, htPhi⟩)
  have hzne : (z : P) ≠ 1 := by
    intro hz1
    apply hv
    apply Additive.toMul.injective
    calc
      v.toMul = QuotientGroup.mk' (lowerCentralLayerKernel P 1) z := hz.symm
      _ = 1 := by
        have : z = 1 := Subtype.ext hz1
        rw [this]
        exact map_one _
  have htne : (t : P) ≠ 1 := by
    intro ht1
    apply hw
    apply Additive.toMul.injective
    calc
      w.toMul = QuotientGroup.mk' (lowerCentralLayerKernel P 1) t := ht.symm
      _ = 1 := by
        have : t = 1 := Subtype.ext ht1
        rw [this]
        exact map_one _
  obtain ⟨y, hyt⟩ := hxi.transitive (z : P) ⟨hzsq, hzne⟩
    (t : P) ⟨htsq, htne⟩
  refine ⟨y, ?_⟩
  apply Additive.toMul.injective
  change lowerCentralLayerAction Y.subtype 1 y v.toMul = w.toMul
  rw [← hz, ← ht, lowerCentralLayerAction_apply_mk]
  apply congrArg (QuotientGroup.mk' (lowerCentralLayerKernel P 1))
  apply Subtype.ext
  exact hyt

/-- Higman's parameter (q-1), the number of involutions, is the number of
nonzero vectors in the second lower-central layer. -/
theorem involutions_ncard_eq_pow_finrank_lowerCentralLayer_one_sub_one
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype) :
    (involutions P).ncard =
      2 ^ Module.finrank (ZMod 2) (Additive (lowerCentralLayer P 1)) - 1 := by
  classical
  have hcomm_ne : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h => hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcomm_ne
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  have heq := commutator_eq_frattini_and_frattini_eq_center
    hP hncomm hxi hlen
  have hset : (frattini P : Set P) = insert 1 (involutions P) := by
    ext x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · exact Set.mem_insert_iff.mpr (Or.inl hx1)
      · exact Set.mem_insert_iff.mpr (Or.inr
          ⟨congrArg Subtype.val
            (frattini_sq_eq_one hP hncomm hxi hlen ⟨x, hx⟩), hx1⟩)
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx1 | hxinv
      · subst x
        exact (frattini P).one_mem
      · rw [heq.2]
        exact involutions_subset_center_of_transitive
          hP Y hxi.transitive hxinv
  have hcardPhi :
      Nat.card ↥(frattini P) = (involutions P).ncard + 1 := by
    calc
      Nat.card ↥(frattini P) = (frattini P : Set P).ncard :=
        Nat.card_coe_set_eq _
      _ = (insert 1 (involutions P)).ncard := by rw [hset]
      _ = (involutions P).ncard + 1 := by
        rw [Set.ncard_insert_of_notMem]
        simp [involutions]
  have hK1 : lowerCentralLayerKernel P 1 = ⊥ :=
    lowerCentralLayerKernel_one_eq_bot_of_xiLengthTwo
      hP hncomm hxi hlen
  have hcardLayer :
      Nat.card (lowerCentralLayer P 1) = Nat.card ↥(frattini P) := by
    change Nat.card
      (↥(lowerCentralTerm P 1) ⧸ lowerCentralLayerKernel P 1) =
        Nat.card ↥(frattini P)
    rw [hK1]
    calc
      Nat.card
          (↥(lowerCentralTerm P 1) ⧸
            (⊥ : Subgroup ↥(lowerCentralTerm P 1))) =
          Nat.card ↥(lowerCentralTerm P 1) :=
        Nat.card_congr QuotientGroup.quotientBot.toEquiv
      _ = Nat.card ↥(frattini P) :=
        Nat.card_congr
          (MulEquiv.subgroupCongr
            (lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen)).toEquiv
  have hpow := lowerCentralLayer_card_eq_pow_finrank P 1
  rw [hcardLayer, hcardPhi] at hpow
  omega

/-- If every prime divisor of the original actor order divides Higman's
(q-1), then that actor has odd order. -/
theorem actor_card_odd_of_primeSupport_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hsupp : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    Odd (Nat.card Y) := by
  letI : Nontrivial (lowerCentralLayer P 1) :=
    lowerCentralLayer_one_nontrivial_of_not_isMulCommutative hP hncomm
  letI : Nontrivial (Additive (lowerCentralLayer P 1)) := inferInstance
  have hnpos : 0 < Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer P 1)) := Module.finrank_pos
  have hcard :=
    involutions_ncard_eq_pow_finrank_lowerCentralLayer_one_sub_one
      hP hncomm hxi hlen
  have hinvpos : 0 < (involutions P).ncard := by
    rw [hcard]
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow hnpos.ne' (by omega))
  have hinv : (involutions P).Nonempty :=
    (Set.ncard_pos (s := involutions P)).mp hinvpos
  have hinvodd := involutions_ncard_odd_of_isPGroup hP hinv
  exact Nat.not_even_iff_odd.mp fun hYeven =>
    hinvodd.not_two_dvd_nat
      (hsupp 2 Nat.prime_two (Even.two_dvd hYeven))

/-- The first lower-central layer of a noncommutative finite 2-group is
nontrivial.  This supplies the nonzero carrier needed by the field model. -/
theorem lowerCentralLayer_zero_nontrivial_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (_hxi : IsXiActor Y)
    (_hlen : HasXiLengthTwo Y.subtype) :
    Nontrivial (lowerCentralLayer P 0) := by
  have hcomm_ne : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h => hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcomm_ne
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  have hPhi_ne_top : frattini P ≠ (⊤ : Subgroup P) :=
    frattini_ne_top_of_nontrivial
  have hPhi_lt_top : frattini P < (⊤ : Subgroup P) :=
    lt_of_le_of_ne le_top hPhi_ne_top
  obtain ⟨x, -, hxPhi⟩ := SetLike.exists_of_lt hPhi_lt_top
  let q : P →* lowerCentralLayer P 0 := layerZeroQuotientHom P
  have hqx : q x ≠ 1 := by
    intro hx
    apply hxPhi
    have hxker : x ∈ q.ker := MonoidHom.mem_ker.mpr hx
    rwa [show q.ker = frattini P from
      layerZeroQuotientHom_ker_eq_frattini hP] at hxker
  exact ⟨q x, 1, hqx⟩

/-- **Higman Lemma 11 (pp. 87–89), field model for a prescribed
original-actor generator.**

Assume, as Higman does after the reduction in Section 6, that every prime
divisor of the original cyclic actor order divides the number of involutions.
Then the caller's chosen generator of that same actor acts on the first
lower-central layer as multiplication by an element which generates the full
field.  If the first and second layer dimensions are `m` and `n`, respectively,
then `n ∣ m` and `m / n` is odd.  Prescribing the generator is what lets the
later simultaneous-coordinate construction keep the common centre coordinate
fixed.

The auxiliary prime-supported subgroup is used only to prove
`2 ^ n - 1 ∣ Nat.card Y`; the irreducible representation is never
restricted from `Y` to that subgroup. -/
theorem exists_originalXiActor_degree_dvd_and_odd_quotient_of_generator
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hsupp : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (c : Y) (hcgen : ∀ g : Y, g ∈ Subgroup.zpowers c) :
    let m := Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer P 0))
    let n := Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer P 1))
    ∃ (e : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2]
        GaloisField 2 m)
      (mu : Y →* (GaloisField 2 m)ˣ),
      Function.Injective mu ∧
      (∀ (g : Y) (v : Additive (lowerCentralLayer P 0)),
        e (lowerCentralLayerRepresentation Y.subtype 0 g v) =
          (mu g : GaloisField 2 m) * e v) ∧
      orderOf (mu c : GaloisField 2 m) = Nat.card Y ∧
      Algebra.adjoin (ZMod 2)
        ({(mu c : GaloisField 2 m)} : Set (GaloisField 2 m)) = ⊤ ∧
      n ∣ m ∧ Odd (m / n) := by
  dsimp only
  let m := Module.finrank (ZMod 2)
    (Additive (lowerCentralLayer P 0))
  let n := Module.finrank (ZMod 2)
    (Additive (lowerCentralLayer P 1))
  letI : IsCyclic Y := hxi.cyclic
  letI : CommGroup Y := IsCyclic.commGroup
  letI : Nontrivial (lowerCentralLayer P 0) :=
    lowerCentralLayer_zero_nontrivial_of_xiLengthTwo
      hP hncomm hxi hlen
  letI : Nontrivial (Additive (lowerCentralLayer P 0)) := inferInstance
  letI : Nontrivial (lowerCentralLayer P 1) :=
    lowerCentralLayer_one_nontrivial_of_not_isMulCommutative hP hncomm
  letI : Nontrivial (Additive (lowerCentralLayer P 1)) := inferInstance
  have hm : 0 < m := Module.finrank_pos
  have hn : 0 < n := Module.finrank_pos
  have hcard : (involutions P).ncard = 2 ^ n - 1 :=
    involutions_ncard_eq_pow_finrank_lowerCentralLayer_one_sub_one
      hP hncomm hxi hlen
  have hinvpos : 0 < (involutions P).ncard := by
    rw [hcard]
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have hinv : (involutions P).Nonempty :=
    (Set.ncard_pos (s := involutions P)).mp hinvpos
  obtain ⟨B, hBY, -, -, hInvDvdB, -⟩ :=
    exists_primeSupported_cyclic_actor
      Y hxi.cyclic hxi.transitive hinv
  have hbase : 2 ^ n - 1 ∣ Nat.card Y := by
    rw [← hcard]
    exact hInvDvdB.trans (Subgroup.card_dvd_of_le hBY)
  have hsupp' : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ 2 ^ n - 1 := by
    intro p hp hpY
    rw [← hcard]
    exact hsupp p hp hpY
  have hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation Y.subtype 0) :=
    lowerCentralLayerZeroRepresentation_isIrreducible_of_xiLengthTwo
      hP hncomm hxi hlen
  have hYodd : Odd (Nat.card Y) :=
    actor_card_odd_of_primeSupport_xiLengthTwo
      hP hncomm hxi hlen hsupp
  have hfaith : Function.Injective
      (lowerCentralLayerRepresentation Y.subtype 0) :=
    lowerCentralLayerZeroRepresentation_injective_of_odd_faithful_action
      hP Y.subtype Y.subtype_injective hYodd
  obtain ⟨e, mu, hmu, hcompat⟩ :=
    OddOrder.RepresentationTheory.exists_galoisFieldLinearModel_of_faithful_irreducible
      (lowerCentralLayerRepresentation Y.subtype 0)
      m hm.ne' rfl hirr hfaith
  have hcorder : orderOf c = Nat.card Y :=
    orderOf_eq_card_of_forall_mem_zpowers hcgen
  have hlambdaOrder :
      orderOf (mu c : GaloisField 2 m) = Nat.card Y :=
    orderOf_units.trans ((orderOf_injective mu hmu c).trans hcorder)
  have hgen : Algebra.adjoin (ZMod 2)
      ({(mu c : GaloisField 2 m)} : Set (GaloisField 2 m)) = ⊤ :=
    OddOrder.RepresentationTheory.adjoin_generator_eq_top_of_irreducible_linearModel
      (lowerCentralLayerRepresentation Y.subtype 0)
      hirr e mu hcompat c hcgen
  have hdegree :=
    OddOrder.RepresentationTheory.galoisField_degree_dvd_and_odd_quotient_of_primeFactors_dvd
      hn hm Nat.card_pos (mu c : GaloisField 2 m)
      hgen hlambdaOrder hbase hsupp'
  exact ⟨e, mu, hmu, hcompat, hlambdaOrder, hgen,
    hdegree.1, hdegree.2⟩

/-- **Higman Lemma 11 (pp. 87–89), field model for the original actor.**

This existential form chooses a generator of the original cyclic actor and
then applies
`exists_originalXiActor_degree_dvd_and_odd_quotient_of_generator`. -/
theorem exists_originalXiActor_degree_dvd_and_odd_quotient
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hsupp : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    let m := Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer P 0))
    let n := Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer P 1))
    ∃ (c : Y)
      (e : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2]
        GaloisField 2 m)
      (mu : Y →* (GaloisField 2 m)ˣ),
      (∀ g : Y, g ∈ Subgroup.zpowers c) ∧
      Function.Injective mu ∧
      (∀ (g : Y) (v : Additive (lowerCentralLayer P 0)),
        e (lowerCentralLayerRepresentation Y.subtype 0 g v) =
          (mu g : GaloisField 2 m) * e v) ∧
      orderOf (mu c : GaloisField 2 m) = Nat.card Y ∧
      Algebra.adjoin (ZMod 2)
        ({(mu c : GaloisField 2 m)} : Set (GaloisField 2 m)) = ⊤ ∧
      n ∣ m ∧ Odd (m / n) := by
  dsimp only
  letI : IsCyclic Y := hxi.cyclic
  letI : CommGroup Y := IsCyclic.commGroup
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := Y)
  obtain ⟨e, mu, hmu, hcompat, hlambdaOrder, hgen, hnm, hodd⟩ :=
    exists_originalXiActor_degree_dvd_and_odd_quotient_of_generator
      hP hncomm hxi hlen hsupp c hcgen
  exact ⟨c, e, mu, hcgen, hmu, hcompat, hlambdaOrder, hgen, hnm, hodd⟩

/-! ## Assembling the actual anchored trace formula -/

/-- Assemble Higman's anchored trace formula for the actual lower-central
square map.

The first-layer square formula and the two cyclic conjugate bases are the
outputs of the Singer-coordinate and bracket-support arguments.  The
second-layer ground coordinate is shifted internally to the selected bracket
anchor; it is not postulated as an additional coordinate system. -/
theorem exists_lowerCentralSquareMap_eq_anchoredTrace_of_actualSingerData
    {P : Type u} [Group P] [Finite P]
    (hAgemo : Agemo P 2 1 = lowerCentralTerm P 1)
    {K : Type uK} {L : Type uL}
    [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [CharP L 2] [Algebra (ZMod 2) L]
    [Algebra K L]
    (iota : K →ₐ[ZMod 2] L)
    (hiota : ∀ z : K, iota z = algebraMap K L z)
    (d : Nat)
    [NeZero (finrank (ZMod 2) K)]
    [NeZero (d * finrank (ZMod 2) K)]
    (hn : 0 < finrank (ZMod 2) K) (hd : 0 < d)
    (hcardK : Nat.card K = 2 ^ finrank (ZMod 2) K)
    (hfinKL : finrank K L = d)
    (hfinL : finrank (ZMod 2) L = d * finrank (ZMod 2) K)
    (eOne : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2] L)
    (bOne : Basis (Fin (d * finrank (ZMod 2) K)) L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer P 0)))
    (hq : ∀ x,
      lowerCentralSquareMapBaseChange L P
          (lowerCentralSquaresLieInSecond_of_agemo_eq P hAgemo) x =
        ∑ i : Fin (d * finrank (ZMod 2) K),
          ∑ j : Fin (d * finrank (ZMod 2) K) with i < j,
            (eOne x) ^ (2 ^ i.val + 2 ^ j.val) •
              lowerCentralCommutatorBilinearBaseChange L P
                (bOne i) (bOne j))
    (hcycleOne : ∀ i,
      frobeniusScalarBaseChange L (bOne i) =
        bOne (higmanCyclicSucc (Nat.mul_pos hd hn) i))
    (eTwo : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] K)
    (bTwo : Basis (Fin (finrank (ZMod 2) K)) L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer P 1)))
    (hbTwo : bTwo =
      conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo)
    (hcycleTwo : ∀ s,
      frobeniusScalarBaseChange L (bTwo s) =
        bTwo (higmanCyclicSucc hn s))
    (a : Fin (d * finrank (ZMod 2) K))
    (s₀ : Fin (finrank (ZMod 2) K))
    (r : Fin (d * finrank (ZMod 2) K))
    (hr0 : r ≠ 0) (hrtwo : r + r ≠ 0)
    (epsilon : L)
    (hseed : lowerCentralCommutatorBilinearBaseChange L P
        (bOne a) (bOne (a + r)) = epsilon • bTwo s₀)
    (hsymm : ∀ i j,
      lowerCentralCommutatorBilinearBaseChange L P
          (bOne i) (bOne j) =
        lowerCentralCommutatorBilinearBaseChange L P
          (bOne j) (bOne i))
    (hsupport : ∀ i j,
      j ≠ i + r → i ≠ j + r →
        lowerCentralCommutatorBilinearBaseChange L P
          (bOne i) (bOne j) = 0) :
    ∃ eTwoShift : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] K,
      ∀ alpha : L,
        lowerCentralSquareMapAdditive P
            (lowerCentralSquaresLieInSecond_of_agemo_eq P hAgemo)
            (eOne.symm alpha) =
          eTwoShift.symm
            (Algebra.trace K L
              (alpha ^ (2 ^ a.val) *
                (alpha ^ (2 ^ a.val)) ^ (2 ^ r.val) * epsilon)) := by
  obtain ⟨eTwoShift, hTwoExpansionShiftCanonical⟩ :=
    exists_shiftedSecondLinearEquiv_expansion iota eTwo s₀
  have hTwoExpansionShiftCanonical' : ∀ z : K,
      (1 : L) ⊗ₜ[ZMod 2] eTwoShift.symm z =
        ∑ s : Fin (finrank (ZMod 2) K),
          (iota z) ^ (2 ^ s.val) •
            (conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo)
              (s₀ + s) := by
    intro z
    simpa only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using hTwoExpansionShiftCanonical z
  have hTwoExpansionShift : ∀ z : K,
      (1 : L) ⊗ₜ[ZMod 2] eTwoShift.symm z =
        ∑ s : Fin (finrank (ZMod 2) K),
          (algebraMap K L z) ^ (2 ^ s.val) • bTwo (s₀ + s) := by
    intro z
    calc
      (1 : L) ⊗ₜ[ZMod 2] eTwoShift.symm z =
          ∑ s : Fin (finrank (ZMod 2) K),
            (iota z) ^ (2 ^ s.val) •
              (conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo)
                (s₀ + s) := hTwoExpansionShiftCanonical' z
      _ = ∑ s : Fin (finrank (ZMod 2) K),
          (algebraMap K L z) ^ (2 ^ s.val) • bTwo (s₀ + s) := by
        simp only [hiota, hbTwo]
  refine ⟨eTwoShift, ?_⟩
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq P hAgemo
  let q : L → Additive (lowerCentralLayer P 1) := fun alpha ↦
    lowerCentralSquareMapAdditive P hSq (eOne.symm alpha)
  let iotaAdd : K →+ Additive (lowerCentralLayer P 1) :=
    eTwoShift.symm.toLinearMap.toAddMonoidHom
  intro alpha
  have hqAlpha :
      (1 : L) ⊗ₜ[ZMod 2] q alpha =
        ∑ i : Fin (d * finrank (ZMod 2) K),
          ∑ j : Fin (d * finrank (ZMod 2) K) with i < j,
            alpha ^ (2 ^ i.val + 2 ^ j.val) •
              lowerCentralCommutatorBilinearBaseChange L P
                (bOne i) (bOne j) := by
    change lowerCentralSquareMapBaseChange L P hSq (eOne.symm alpha) = _
    simpa only [eOne.apply_symm_apply] using hq (eOne.symm alpha)
  have htrace := squareMap_eq_trace_of_anchored_singleGap
    (lowerCentralCommutatorBilinear P)
    (finrank (ZMod 2) K) d hn hd hcardK hfinKL hfinL
    bOne bTwo hcycleOne hcycleTwo
    a s₀ r hr0 hrtwo epsilon
    (by simpa only [lowerCentralCommutatorBilinearBaseChange] using hseed)
    (by simpa only [lowerCentralCommutatorBilinearBaseChange] using hsymm)
    (by simpa only [lowerCentralCommutatorBilinearBaseChange] using hsupport)
    q iotaAdd
    (by
      intro z
      change (1 : L) ⊗ₜ[ZMod 2] eTwoShift.symm z = _
      exact hTwoExpansionShift z)
    alpha
    (by simpa only [lowerCentralCommutatorBilinearBaseChange] using hqAlpha)
  change lowerCentralSquareMapAdditive P hSq (eOne.symm alpha) =
    eTwoShift.symm
      (Algebra.trace K L
        (alpha ^ (2 ^ a.val) *
          (alpha ^ (2 ^ a.val)) ^ (2 ^ r.val) * epsilon)) at htrace
  simpa only [q, hSq] using htrace

/-! ## Nonvanishing of the actual square map -/

/-- If the second lower-central layer has trivial denominator and every
involution lies in the second lower-central term, the first-layer square map
has trivial zero locus. -/
theorem lowerCentralSquareMap_eq_one_imp_eq_one_of_kernel_one_eq_bot
    (H : Type u) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (hK1 : lowerCentralLayerKernel H 1 = ⊥)
    (hInv : ∀ x : H, x ^ 2 = 1 → x ∈ lowerCentralTerm H 1)
    (u : lowerCentralLayer H 0)
    (hu : lowerCentralSquareMap H hSq u = 1) :
    u = 1 := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 0) u
  have hsquareValue : lowerCentralSquareValue H hSq g = 1 := by
    simpa only [lowerCentralSquareMap_mk] using hu
  have hsquareRepMem : lowerCentralSquareRepresentative H hSq g ∈
      lowerCentralLayerKernel H 1 :=
    (QuotientGroup.eq_one_iff _).mp hsquareValue
  have hsquareRep : lowerCentralSquareRepresentative H hSq g = 1 := by
    rw [hK1] at hsquareRepMem
    exact Subgroup.mem_bot.mp hsquareRepMem
  have hgsq : (g : H) ^ 2 = 1 := congrArg Subtype.val hsquareRep
  apply (QuotientGroup.eq_one_iff g).mpr
  rw [lowerCentralLayerKernel_zero_eq_of_squares_le H hSq,
    Subgroup.mem_subgroupOf]
  exact hInv (g : H) hgsq

/-- Additive nonvanishing form of the preceding quotient-kernel criterion. -/
theorem lowerCentralSquareMapAdditive_ne_zero_of_kernel_one_eq_bot
    (H : Type u) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (hK1 : lowerCentralLayerKernel H 1 = ⊥)
    (hInv : ∀ x : H, x ^ 2 = 1 → x ∈ lowerCentralTerm H 1)
    (u : Additive (lowerCentralLayer H 0))
    (hu : u ≠ 0) :
    lowerCentralSquareMapAdditive H hSq u ≠ 0 := by
  intro hzero
  apply hu
  apply Additive.toMul.injective
  change Additive.toMul u = 1
  apply lowerCentralSquareMap_eq_one_imp_eq_one_of_kernel_one_eq_bot
    H hSq hK1 hInv
  apply Additive.ofMul.injective
  exact hzero

/-- Higman's nonabelian xi-length-two hypotheses imply the actual square map
is nonzero on every nonzero first-layer vector. -/
theorem lowerCentralSquareMapAdditive_ne_zero_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (u : Additive (lowerCentralLayer P 0))
    (hu : u ≠ 0) :
    lowerCentralSquareMapAdditive P
        (lowerCentralSquaresLieInSecond_of_agemo_eq P
          (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)) u ≠ 0 := by
  have hcomm_ne : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h ↦ hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcomm_ne
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq P
    (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  have hAmbientK1 : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot hP hncomm hxi hlen, sup_bot_eq,
      lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_agemo_one_map_eq_bot hP hncomm hxi hlen]
  have hK1 : lowerCentralLayerKernel P 1 = ⊥ := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbientK1]
    simp
  have hInv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1 := by
    intro x hx
    rw [lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_eq_involutionSubgroup hP hncomm hxi hlen,
      involutionSubgroup, mem_omega1OfAbelian]
    refine ⟨?_, hx⟩
    by_cases hx1 : x = 1
    · simp [hx1]
    · exact involutions_subset_center_of_transitive hP Y hxi.transitive
        ⟨hx, hx1⟩
  exact lowerCentralSquareMapAdditive_ne_zero_of_kernel_one_eq_bot
    P hSq hK1 hInv u hu

/-! ## The Lemma 10 contradiction -/

/-- Minimal endgame connector for Higman's Lemma 11.

If the square map is given by the relative-trace normal form produced by the
single-gap calculation, and it is nonzero on every nonzero first-layer
coordinate, then the odd finite extension cannot be proper. -/
theorem finrank_eq_one_of_trace_squareMap_ne_zero
    {K : Type uK} {L : Type uL} {W : Type uW}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [AddCommMonoid W]
    (q : L → W) (iotaAdd : K →+ W)
    (hodd : Odd (Module.finrank K L))
    (r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      q alpha = iotaAdd
        (Algebra.trace K L
          (alpha * alpha ^ (2 ^ r) * epsilon)))
    (hq_ne_zero : ∀ alpha : L, alpha ≠ 0 → q alpha ≠ 0) :
    Module.finrank K L = 1 := by
  have hnotProper : ¬ 1 < Module.finrank K L := by
    intro hproper
    obtain ⟨alpha, halpha, htrace⟩ :=
      higmanLemmaTen hproper hodd (r : Int) epsilon
    have hfrobenius :
        alpha ^ (2 ^ r) =
          ((frobeniusEquiv L 2) ^ (r : Int)) alpha := by
      rw [zpow_natCast, ← iterateFrobeniusEquiv_eq_pow]
      exact (iterateFrobeniusEquiv_def L 2 r alpha).symm
    have htraceNat :
        Algebra.trace K L
          (alpha * alpha ^ (2 ^ r) * epsilon) = 0 := by
      rw [hfrobenius]
      exact htrace
    apply hq_ne_zero alpha halpha
    rw [hformula alpha, htraceNat, map_zero]
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  omega

/-- Anchor-general variant.  Frobenius bijectivity pulls the witness from
Lemma 10 back through `alpha ↦ alpha^(2^a)`. -/
theorem finrank_eq_one_of_anchoredTrace_squareMap_ne_zero
    {K : Type uK} {L : Type uL} {W : Type uW}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [AddCommMonoid W]
    (q : L → W) (iotaAdd : K →+ W)
    (hodd : Odd (Module.finrank K L))
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      q alpha = iotaAdd
        (Algebra.trace K L
          (alpha ^ (2 ^ a) *
            (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon)))
    (hq_ne_zero : ∀ alpha : L, alpha ≠ 0 → q alpha ≠ 0) :
    Module.finrank K L = 1 := by
  have hfrobenius (x : L) (t : Nat) :
      x ^ (2 ^ t) = ((frobeniusEquiv L 2) ^ (t : Int)) x := by
    rw [zpow_natCast, ← iterateFrobeniusEquiv_eq_pow]
    exact (iterateFrobeniusEquiv_def L 2 t x).symm
  have hnotProper : ¬ 1 < Module.finrank K L := by
    intro hproper
    obtain ⟨beta, hbeta, htrace⟩ :=
      higmanLemmaTen hproper hodd (r : Int) epsilon
    obtain ⟨alpha, halphaImage⟩ :=
      ((frobeniusEquiv L 2) ^ (a : Int)).surjective beta
    have hanchor : alpha ^ (2 ^ a) = beta :=
      (hfrobenius alpha a).trans halphaImage
    have halpha : alpha ≠ 0 := by
      intro halphaZero
      apply hbeta
      rw [← hanchor, halphaZero, zero_pow (by positivity)]
    have htraceNat :
        Algebra.trace K L
          (beta * beta ^ (2 ^ r) * epsilon) = 0 := by
      rw [hfrobenius beta r]
      exact htrace
    apply hq_ne_zero alpha halpha
    rw [hformula alpha, hanchor, htraceNat, map_zero]
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  omega

/-- **Higman Lemma 11 (p. 89), exclusion of a proper field extension.**

For a nonabelian xi-length-two group, an anchored trace formula for its actual
lower-central square map forces the relative first-layer field degree to be
one.  This is Higman's contradiction: Lemma 10 would otherwise produce a
nonzero first-layer coordinate whose square is zero, hence an involution
outside the Frattini subgroup. -/
theorem finrank_eq_one_of_anchoredTrace_lowerCentralSquareMap_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    (e : Additive (lowerCentralLayer P 0) ≃+ L)
    (iotaAdd : K →+ Additive (lowerCentralLayer P 1))
    (hodd : Odd (Module.finrank K L))
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      lowerCentralSquareMapAdditive P
          (lowerCentralSquaresLieInSecond_of_agemo_eq P
            (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen))
          (e.symm alpha) =
        iotaAdd
          (Algebra.trace K L
            (alpha ^ (2 ^ a) *
              (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))) :
    Module.finrank K L = 1 := by
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq P
    (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  let q : L → Additive (lowerCentralLayer P 1) := fun alpha =>
    lowerCentralSquareMapAdditive P hSq (e.symm alpha)
  apply finrank_eq_one_of_anchoredTrace_squareMap_ne_zero
    q iotaAdd hodd a r epsilon
  · intro alpha
    exact hformula alpha
  · intro alpha halpha
    apply lowerCentralSquareMapAdditive_ne_zero_of_xiLengthTwo
      hP hncomm hxi hlen
    intro hzero
    apply halpha
    apply e.symm.injective
    simpa only [map_zero] using hzero

/-! ## The trace is superfluous in degree one -/

/-- The algebra map is a ring equivalence when the relative degree is one. -/
noncomputable def finrankOneRingEquiv
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Algebra K L]
    (hfin : Module.finrank K L = 1) : K ≃+* L :=
  RingEquiv.ofBijective (algebraMap K L)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin)

@[simp]
theorem finrankOneRingEquiv_apply
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Algebra K L]
    (hfin : Module.finrank K L = 1) (x : K) :
    finrankOneRingEquiv K L hfin x = algebraMap K L x :=
  rfl

/-- Over a degree-one extension of finite fields, embedding the relative trace
back into the top field returns the original element. -/
theorem algebraMap_trace_eq_self_of_finrank_eq_one
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    (hfin : Module.finrank K L = 1) (x : L) :
    algebraMap K L (Algebra.trace K L x) = x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hfin]
  simp

/-- Thus the relative trace itself is the inverse of the algebra-map
equivalence. -/
theorem trace_eq_finrankOneRingEquiv_symm
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    (hfin : Module.finrank K L = 1) (x : L) :
    Algebra.trace K L x = (finrankOneRingEquiv K L hfin).symm x := by
  let e := finrankOneRingEquiv K L hfin
  apply e.injective
  calc
    e (Algebra.trace K L x) =
        algebraMap K L (Algebra.trace K L x) := rfl
    _ = x := algebraMap_trace_eq_self_of_finrank_eq_one K L hfin x
    _ = e (e.symm x) := (e.apply_symm_apply x).symm

/-- Higman's absolute finite-field degrees agree when the relative degree is
one.  This is the equality `m = n` on p. 89. -/
theorem absoluteFinrank_eq_of_relativeFinrank_eq_one
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) L]
    [IsScalarTower (ZMod 2) K L]
    (hfin : Module.finrank K L = 1) :
    Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) K := by
  rw [← Module.finrank_mul_finrank (ZMod 2) K L, hfin, mul_one]

/-- Named-degree form of Higman's conclusion `m = n`. -/
theorem absoluteDegrees_eq_of_relativeFinrank_eq_one
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) L]
    [IsScalarTower (ZMod 2) K L]
    (m n : Nat)
    (hfinK : Module.finrank (ZMod 2) K = n)
    (hfinL : Module.finrank (ZMod 2) L = m)
    (hfin : Module.finrank K L = 1) :
    m = n := by
  calc
    m = Module.finrank (ZMod 2) L := hfinL.symm
    _ = Module.finrank (ZMod 2) K :=
      absoluteFinrank_eq_of_relativeFinrank_eq_one K L hfin
    _ = n := hfinK

/-- The exact right-hand-side rewrite in the anchored Frobenius-sum theorem:
the relative trace disappears after the relative degree has been proved one. -/
theorem anchoredFrobeniusSum_trace_superfluous
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    {M : Type uW} [AddCommMonoid M] [Module L M]
    (hfin : Module.finrank K L = 1)
    (n : Nat) (bTwo : Fin n → M) (s₀ : Fin n) (z : L) :
    (∑ s : Fin n,
        (algebraMap K L (Algebra.trace K L z)) ^ (2 ^ s.val) •
          bTwo (s₀ + s)) =
      ∑ s : Fin n, z ^ (2 ^ s.val) • bTwo (s₀ + s) := by
  rw [algebraMap_trace_eq_self_of_finrank_eq_one K L hfin z]

/-- Higman's p. 89 statement that the trace is superfluous.  A degree-one
anchored trace normal form is the same formula with an additive coordinate
map defined on the common field itself. -/
theorem anchoredTraceFormula_trace_superfluous
    {K : Type uK} {L : Type uL} {W : Type uW}
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    [AddCommMonoid W]
    (hfin : Module.finrank K L = 1)
    (q : L → W) (iotaAdd : K →+ W)
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      q alpha = iotaAdd
        (Algebra.trace K L
          (alpha ^ (2 ^ a) *
            (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))) :
    ∃ iotaL : L →+ W, ∀ alpha : L,
      q alpha = iotaL
        (alpha ^ (2 ^ a) *
          (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon) := by
  refine ⟨iotaAdd.comp
    (finrankOneRingEquiv K L hfin).symm.toAddMonoidHom, ?_⟩
  intro alpha
  change q alpha = iotaAdd
    ((finrankOneRingEquiv K L hfin).symm
      (alpha ^ (2 ^ a) *
        (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))
  rw [hformula alpha,
    trace_eq_finrankOneRingEquiv_symm K L hfin]

end OddOrder.Higman.Suzuki2Groups
