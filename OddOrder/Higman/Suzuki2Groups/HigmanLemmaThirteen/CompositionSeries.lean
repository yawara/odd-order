/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniLayers

/-!
# Higman's Lemma 13: branch-specific composition series

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For exact `ξ`-length four, the lower Frattini layers from
`FrattiniLayers` can be extended to full composition series:

* if `Φ(P)` has exponent four, the series starts
  `1 ⋖ Φ(P)² ⋖ Φ(P)`;
* if `Φ(P)` has exponent two, it starts `1 ⋖ Φ(P)`.

The exponent-four extension uses Higman Lemmas 7 and 8.  If `Φ(P)`
covered `P`, their cover dichotomy would force either `P` to be
commutative or `Φ(P)` to have exponent two.  Thus a further proper term
exists above `Φ(P)`.  In the exponent-two branch, every nontrivial
invariant term contains `Φ(P)`, so the first term of any length-four
composition series is `Φ(P)` itself.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- The ambient image of the Frattini subgroup of the top subgroup is the
Frattini subgroup of the ambient group. -/
theorem ambientFrattini_top_eq_frattini :
    NormalInvariantCover.ambientFrattini (⊤ : Subgroup P) =
      frattini P := by
  let e : (⊤ : Subgroup P) ≃* P := Subgroup.topEquiv
  have hfrattini :
      (frattini (⊤ : Subgroup P)).map e.toMonoidHom = frattini P := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · have hback :=
        frattini_le_comap_frattini_of_surjective
          (φ := e.symm.toMonoidHom) e.symm.surjective
      rwa [Subgroup.map_equiv_eq_comap_symm']
  have he : e.toMonoidHom = (⊤ : Subgroup P).subtype := by
    ext x
    rfl
  change (frattini (⊤ : Subgroup P)).map
      (⊤ : Subgroup P).subtype = frattini P
  rw [← he]
  exact hfrattini

/-- **Higman Lemma 13 (p. 92), exponent-four composition series.**

The lower Frattini covers extend by two further covers to the top term. -/
theorem exists_frattini_composition_series_of_xiLengthFour_exponent_four
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    ∃ B : NormalInvariantSubgroup Y.subtype,
      normalInvariantBot Y.subtype ⋖
          frattiniSquareNormalInvariant Y.subtype ∧
        frattiniSquareNormalInvariant Y.subtype ⋖
          frattiniNormalInvariant Y.subtype ∧
        frattiniNormalInvariant Y.subtype ⋖ B ∧
          B ⋖ normalInvariantTop Y.subtype := by
  letI : Nontrivial P := by
    obtain ⟨x, y, _, _, hxy⟩ := hmulti
    exact ⟨⟨x, y, hxy⟩⟩
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) :=
    frattini_ne_bot_of_not_isMulCommutative hP hncomm
  letI : Nontrivial (frattini P) :=
    (Subgroup.nontrivial_iff_ne_bot (frattini P)).mpr hPhiNeBot
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
  obtain ⟨ι, hι, _e, _he, _hε, classifyFull⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      (hP.to_subgroup (frattini P)) hPhiInv.restrict htransPhi
  letI : Fintype ι := hι
  have classify : ∀ U : Subgroup (frattini P),
      IsAInvariant hPhiInv.restrict U →
        ∃ s : ℕ, U = Agemo (frattini P) 2 s := by
    intro U hU
    obtain ⟨s, _hs, hsU⟩ := classifyFull U hU
    exact ⟨s, hsU⟩
  have hYodd : Odd (Nat.card Y) := by
    have hinv : (involutions P).Nonempty := by
      obtain ⟨x, _, hx, _, _⟩ := hmulti
      exact ⟨x, hx⟩
    exact actor_card_odd_of_primeSupport hP hinv hprime
  have hchain :=
    frattiniSquare_strict_chain_of_exponent_four
      (Y := Y) hmulti hPhiComm hfour hexists
  have hPhiTop :
      frattiniNormalInvariant Y.subtype <
        normalInvariantTop Y.subtype :=
    hchain.2.2
  have hnotCover :
      ¬ frattiniNormalInvariant Y.subtype ⋖
        normalInvariantTop Y.subtype := by
    intro hcov
    let hcover : NormalInvariantCover Y.subtype (frattini P) ⊤ :=
      { left := ⟨inferInstance, hPhiInv⟩
        right := ⟨inferInstance, IsAInvariant.top Y.subtype⟩
        covBy := by
          simpa [frattiniNormalInvariant, normalInvariantTop] using hcov }
    rcases hcover.commutator_map_eq_left_or_le_agemo_one
        hP classify ambientFrattini_top_eq_frattini with
      hderived | hderived
    · obtain ⟨z, hz⟩ := hexists
      apply hz
      exact higmanLemmaEight_pow_two_eq_one_of_transitive
        hP Y hxi.cyclic hxi.transitive hYodd hmulti
          (frattini P) ⊤ hcover hPhiComm hderived z
    · have hTopComm : IsMulCommutative (⊤ : Subgroup P) :=
        higmanLemmaSeven_isMulCommutative_of_transitive
          hP Y hxi.cyclic hxi.transitive hmulti
            (frattini P) ⊤ hcover hPhiComm
              ambientFrattini_top_eq_frattini hderived
      apply hncomm
      refine IsMulCommutative.of_comm fun x y => ?_
      exact congrArg Subtype.val
        (hTopComm.is_comm.comm
          (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup P))
          (⟨y, Subgroup.mem_top y⟩ : (⊤ : Subgroup P)))
  obtain ⟨B, hPhiB, hBtop⟩ :=
    (not_covBy_iff hPhiTop).mp hnotCover
  exact ⟨B, hlen.covers_of_chain
    hchain.1 hchain.2.1 hPhiB hBtop⟩

/-- **Higman Lemma 13 (p. 92), exponent-two composition series.**

The Frattini subgroup is the first term of a length-four composition
series, followed by two proper intermediate terms. -/
theorem exists_frattini_composition_series_of_xiLengthFour_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    ∃ B C : NormalInvariantSubgroup Y.subtype,
      normalInvariantBot Y.subtype ⋖
          frattiniNormalInvariant Y.subtype ∧
        frattiniNormalInvariant Y.subtype ⋖ B ∧
          B ⋖ C ∧ C ⋖ normalInvariantTop Y.subtype := by
  obtain ⟨A, B, C, hbotA, hAB, hBC, hCtop⟩ :=
    hlen.exists_composition_series
  have hPhiCover :=
    normalInvariantBot_covBy_frattini_of_pow_two_eq_one
      hP hncomm hxi htwo
  have hAne : A.1 ≠ (⊥ : Subgroup P) := by
    exact ne_of_gt (show (⊥ : Subgroup P) < A.1 from hbotA.lt)
  have hinvA : involutions P ⊆ A.1 :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive A.2.2 hAne
  have hPhiA : frattini P ≤ A.1 := by
    intro z hz
    by_cases hz1 : z = 1
    · exact hz1 ▸ A.1.one_mem
    · apply hinvA
      exact ⟨congrArg Subtype.val (htwo ⟨z, hz⟩), hz1⟩
  let phi := frattiniNormalInvariant Y.subtype
  have hPhiAle : phi ≤ A := hPhiA
  have hphiA : phi = A :=
    (hbotA.eq_or_eq hPhiCover.le hPhiAle).resolve_left
      hPhiCover.lt.ne'
  subst A
  exact ⟨B, C, by simpa [phi] using hPhiCover,
    by simpa [phi] using hAB, hBC, hCtop⟩

end OddOrder.Higman.Suzuki2Groups
