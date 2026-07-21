/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.TypeBFromW
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuotientPlaneModel
import OddOrder.GroupTheory.RepresentationTheory.ProjectiveFreeTwoDim

/-!
# Peterfalvi Part II, Ch. I §3, Lemma 5: cyclicity of `W` and `|W| ∣ q + 1`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, Lemma 5, p. 107, final paragraph.

If `W ≠ 1`, the plane model identifies `Q ⧸ Q₀` with `F_q × F_q`, and each
`w ∈ W` acts on it as an `F_q`-linear automorphism: it is additive because
conjugation descends to the quotient, and it commutes with every scalar
because `W` centralizes `K` and `K` surjects onto the nonzero scalars.  The
moved-summand engine shows that no nonidentity element of `W` fixes a
projective point — a fixed line would be a `K`-invariant order-`q` subgroup
invariant under `w`, contradicting `C_Q(w) = Q₀`.  The general
two-dimensional theorem then gives cyclicity of `W` and `|W| ∣ q + 1`.  For
`W = 1` both conclusions are trivial, so Lemma 5's first two claims hold
unconditionally.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **Peterfalvi Part II, Ch. I §3, Lemma 5** (first two claims, p. 107).
If `|st| = 3` and `Q` is a Suzuki `2`-group of order `q³` with
`q = |Q₀| = 2^m`, then `W` is cyclic and `|W|` divides `q + 1`. -/
theorem isCyclic_W_and_card_dvd_of_orderThree
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω) :
    IsCyclic ↥hyp.W ∧ Nat.card ↥hyp.W ∣ 2 ^ m + 1 := by
  classical
  rcases eq_or_ne hyp.W ⊥ with hWbot | hWne
  · -- trivial `W`
    have hone : Nat.card ↥hyp.W = 1 := by
      rw [hWbot, Subgroup.card_bot]
    have hsub : Subsingleton ↥hyp.W :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    refine ⟨@isCyclic_of_subsingleton _ _ hsub, ?_⟩
    rw [hone]
    exact one_dvd _
  · -- pick a nonidentity element of `W` and build the Lemma 5 setup
    obtain ⟨w, hwW, hwbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hWne)
    have hw1 : w ≠ 1 := fun h =>
      hwbot (h ▸ Subgroup.one_mem ⊥)
    obtain ⟨s⟩ := hyp.lemmaFiveSetup_of_orderThree_of_mem_W hwW hw1 hst hQsuz
      hm hQ0card hcardQ inductionHypothesis
    have hZcard : Nat.card ↥(Subgroup.center hyp.Q) = 2 ^ m := by
      rw [s.centerEqQ0,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv,
        hQ0card]
    -- the plane coordinates
    obtain ⟨ψ, mu, hmusurj, hadd, hsc⟩ :=
      Suzuki2Groups.exists_planeCoordinates_of_isomorphicSplit
        s.isplit s.freeQuotient hm s.cardActor hZcard
    -- basic facts about `ψ`
    have hψone : ψ 1 = 0 := by
      have h := hadd 1 1
      rw [mul_one] at h
      have h0 : ψ 1 + 0 = ψ 1 + ψ 1 := by
        rw [add_zero]
        exact h
      exact (add_left_cancel h0).symm
    have hψsymm_zero : ψ.symm 0 = 1 := by
      apply ψ.injective
      rw [ψ.apply_symm_apply, hψone]
    have hψsymm_add : ∀ a b : GaloisField 2 m × GaloisField 2 m,
        ψ.symm (a + b) = ψ.symm a * ψ.symm b := by
      intro a b
      apply ψ.injective
      rw [ψ.apply_symm_apply, hadd, ψ.apply_symm_apply, ψ.apply_symm_apply]
    have hψinv : ∀ x : ↥hyp.Q ⧸ Subgroup.center hyp.Q,
        ψ x⁻¹ = - ψ x := by
      intro x
      have h := hadd x⁻¹ x
      rw [inv_mul_cancel, hψone] at h
      exact eq_neg_of_add_eq_zero_left h.symm
    -- every element of `W` fixes the center pointwise
    have hWfix : ∀ v : ↥hyp.W, ∀ z ∈ Subgroup.center hyp.Q,
        hyp.conjQByW v z = z :=
      fun v => hyp.conjQByW_fixes_center s.centerEqQ0 v
    -- the induced action of `W` on the plane
    set act : ↥hyp.W → (GaloisField 2 m × GaloisField 2 m) →
        (GaloisField 2 m × GaloisField 2 m) := fun v c =>
      ψ (Suzuki2Groups.quotientCongr (hyp.conjQByW v) (hWfix v) (ψ.symm c))
      with hactdef
    have hact_apply : ∀ (v : ↥hyp.W) (q : ↥hyp.Q ⧸ Subgroup.center hyp.Q),
        act v (ψ q) =
          ψ (Suzuki2Groups.quotientCongr (hyp.conjQByW v) (hWfix v) q) := by
      intro v q
      rw [hactdef]
      simp only [Equiv.symm_apply_apply]
    have hact_add : ∀ (v : ↥hyp.W) (a b : GaloisField 2 m × GaloisField 2 m),
        act v (a + b) = act v a + act v b := by
      intro v a b
      rw [hactdef]
      simp only
      rw [hψsymm_add, map_mul, hadd]
    -- commutation with the induced actor action at the quotient level
    have hcommQ : ∀ (v : ↥hyp.W) (k : ↥hyp.actualKActor)
        (q : ↥hyp.Q ⧸ Subgroup.center hyp.Q),
        Suzuki2Groups.quotientCongr (hyp.conjQByW v) (hWfix v)
          (quotientMulAutHom
            (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k q) =
        quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k
          (Suzuki2Groups.quotientCongr (hyp.conjQByW v) (hWfix v) q) :=
      fun v k q =>
      Suzuki2Groups.quotientCongr_comm_quotientMulAutHom _
        (hyp.conjQByW v) (hWfix v) k
        (hyp.conjQByW_commute_actualKActor v k) q
    have hact_smul : ∀ (v : ↥hyp.W) (c : GaloisField 2 m)
        (x : GaloisField 2 m × GaloisField 2 m),
        act v (c • x) = c • act v x := by
      intro v c x
      rcases eq_or_ne c 0 with rfl | hc
      · rw [zero_smul, zero_smul, hactdef]
        simp only
        rw [hψsymm_zero, map_one, hψone]
      · obtain ⟨k, hk⟩ := hmusurj (Units.mk0 c hc)
        have hcval : (mu k : GaloisField 2 m) = c := by rw [hk]; rfl
        have hsymm_smul : ψ.symm (c • x) =
            quotientMulAutHom
              (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k
              (ψ.symm x) := by
          apply ψ.injective
          rw [ψ.apply_symm_apply, hsc, ψ.apply_symm_apply, hcval]
        rw [hactdef]
        simp only
        rw [hsymm_smul, hcommQ, hsc, hcval]
    -- the linear representation of `W` on the plane
    set rhoW : Representation (GaloisField 2 m) ↥hyp.W
        (GaloisField 2 m × GaloisField 2 m) :=
      { toFun := fun v =>
          { toFun := act v
            map_add' := hact_add v
            map_smul' := fun c x => hact_smul v c x }
        map_one' := by
          apply LinearMap.ext
          intro c
          show act 1 c = c
          rw [hactdef]
          simp only
          obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm c)
          rw [← hx, Suzuki2Groups.quotientCongr_mk]
          have hone : hyp.conjQByW 1 x = x := by
            rw [map_one]
            rfl
          rw [hone, hx, ψ.apply_symm_apply]
        map_mul' := by
          intro v u
          apply LinearMap.ext
          intro c
          show act (v * u) c = act v (act u c)
          rw [hactdef]
          simp only
          rw [Equiv.symm_apply_apply]
          obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm c)
          rw [← hx, Suzuki2Groups.quotientCongr_mk,
            Suzuki2Groups.quotientCongr_mk, Suzuki2Groups.quotientCongr_mk]
          have hmul : hyp.conjQByW (v * u) x =
              hyp.conjQByW v (hyp.conjQByW u x) := by
            rw [map_mul]
            rfl
          rw [hmul] } with hrhoWdef
    have hrhoW_apply : ∀ (v : ↥hyp.W)
        (q : ↥hyp.Q ⧸ Subgroup.center hyp.Q),
        rhoW v (ψ q) =
          ψ (Suzuki2Groups.quotientCongr (hyp.conjQByW v) (hWfix v) q) :=
      fun v q => hact_apply v q
    -- identification of `Q ⧸ Z(Q)`-subgroup images with invariance data
    have hengine : ∀ (v : ↥hyp.W), (v : G) ≠ 1 →
        ∀ (U : Subgroup (↥hyp.Q ⧸ Subgroup.center hyp.Q)),
        IsAInvariant (quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype)) U →
        Nat.card ↥U = Nat.card ↥(Subgroup.center hyp.Q) →
        U.map (Suzuki2Groups.quotientCongr (hyp.conjQByW v)
          (hWfix v)).toMonoidHom ≠ U := by
      intro v hv1 U hUinv hUcard
      obtain ⟨hω1, hωodd, -, -, hωfix⟩ :=
        hyp.conjQByW_omega_facts v.2 hv1 hst hm hQ0card hcardQ
          inductionHypothesis s.centerEqQ0
      exact Suzuki2Groups.map_quotientCongr_ne_of_fixedPoints_le
        (le_refl _) s.centerSq s.sqMem s.invMem hUinv hUcard
        s.transCenter s.centerNeBot
        (hyp.conjQByW v) hω1 hωodd (hWfix v) hωfix
    -- faithfulness
    have hfaith : Function.Injective rhoW := by
      have hker : ∀ v : ↥hyp.W, rhoW v = 1 → v = 1 := by
        intro v hv
        by_contra hvne
        have hv1 : (v : G) ≠ 1 := fun h => hvne (Subtype.ext h)
        have hid : ∀ q : ↥hyp.Q ⧸ Subgroup.center hyp.Q,
            Suzuki2Groups.quotientCongr (hyp.conjQByW v) (hWfix v) q = q := by
          intro q
          apply ψ.injective
          rw [← hrhoW_apply, hv]
          rfl
        apply hengine v hv1 s.isplit.split.left s.isplit.split.leftInvariant
          s.isplit.split.leftCard
        ext y
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rwa [hid]
        · intro hy
          exact ⟨y, hy, hid y⟩
      intro v u hvu
      have hmul : rhoW (v⁻¹ * u) = 1 := by
        rw [map_mul, ← hvu, ← map_mul, inv_mul_cancel, map_one]
      have := hker _ hmul
      rwa [inv_mul_eq_one] at this
    -- odd order
    have hodd : Odd (Nat.card ↥hyp.W) := by
      have h3 : Nat.card ↥hyp.W ∣ Nat.card ↥hyp.D :=
        Subgroup.card_dvd_of_le (hyp.W_le_V.trans hyp.V_le_D)
      exact hyp.D_odd.of_dvd_nat h3
    -- dimension two
    have hdim : Module.finrank (GaloisField 2 m)
        (GaloisField 2 m × GaloisField 2 m) = 2 := by
      rw [Module.finrank_prod, Module.finrank_self]
    -- projective freeness
    have hprojfree : ∀ e : ↥hyp.W, e ≠ 1 →
        ∀ L : Projectivization (GaloisField 2 m)
          (GaloisField 2 m × GaloisField 2 m),
        (OddOrder.BG.Ch1.S02.representationToGeneralLinearGroup rhoW e) •
          L ≠ L := by
      intro e he L hfix
      induction L using Projectivization.ind with
      | h vec hvec =>
      rw [Projectivization.smul_mk] at hfix
      obtain ⟨c, hc₀⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).1 hfix
      have hc : c • vec = rhoW e vec := hc₀
      set S : Submodule (GaloisField 2 m)
          (GaloisField 2 m × GaloisField 2 m) :=
        Submodule.span (GaloisField 2 m) {vec} with hSdef
      have hSact : ∀ x ∈ S, rhoW e x ∈ S := by
        intro x hx
        rw [hSdef, Submodule.mem_span_singleton] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [map_smul]
        have hex : rhoW e vec ∈ S := by
          rw [← hc]
          exact Submodule.smul_mem _ c
            (Submodule.mem_span_singleton_self vec)
        exact Submodule.smul_mem _ a hex
      -- the corresponding subgroup of the quotient
      set U : Subgroup (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
        { carrier := ψ ⁻¹' S
          one_mem' := by
            simp only [Set.mem_preimage, hψone]
            exact Submodule.zero_mem S
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_preimage] at ha hb ⊢
            rw [hadd]
            exact Submodule.add_mem S ha hb
          inv_mem' := by
            intro a ha
            simp only [Set.mem_preimage] at ha ⊢
            rw [hψinv]
            exact Submodule.neg_mem S ha } with hUdef
      have hUmem : ∀ x : ↥hyp.Q ⧸ Subgroup.center hyp.Q,
          x ∈ U ↔ ψ x ∈ S := fun x => Iff.rfl
      -- cardinality of the line
      have hUcard : Nat.card ↥U = Nat.card ↥(Subgroup.center hyp.Q) := by
        have h1 : Nat.card ↥U = Nat.card ↥S := by
          apply Nat.card_congr
          exact ψ.subtypeEquiv (fun x => Iff.rfl)
        have hrank : Module.finrank (GaloisField 2 m) ↥S = 1 :=
          finrank_span_singleton hvec
        have h2 : Nat.card ↥S = 2 ^ m := by
          haveI : Fintype ↥S := Fintype.ofFinite _
          haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
          rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank
            (K := GaloisField 2 m) (V := ↥S), hrank, pow_one,
            ← Nat.card_eq_fintype_card, GaloisField.card 2 m hm]
        rw [h1, h2, hZcard]
      -- `K`-invariance of the line
      have hUinv : IsAInvariant (quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype)) U := by
        intro k
        apply le_antisymm
        · rintro y ⟨x, hx, rfl⟩
          have hx' : ψ x ∈ S := hx
          show ψ (quotientMulAutHom
            (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k x) ∈ S
          rw [hsc]
          exact Submodule.smul_mem S _ hx'
        · intro y hy
          have hy' : ψ y ∈ S := hy
          refine ⟨quotientMulAutHom
            (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k⁻¹ y,
            ?_, ?_⟩
          · show ψ (quotientMulAutHom
              (IsAInvariant.of_characteristic hyp.actualKActor.subtype)
              k⁻¹ y) ∈ S
            rw [hsc]
            exact Submodule.smul_mem S _ hy'
          · change quotientMulAutHom _ k (quotientMulAutHom _ k⁻¹ y) = y
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
              MulAut.one_apply]
      -- `e`-invariance of the line, contradicting the moved-summand engine
      have he1 : (e : G) ≠ 1 := fun h => he (Subtype.ext h)
      apply hengine e he1 U hUinv hUcard
      have hle : U.map (Suzuki2Groups.quotientCongr (hyp.conjQByW e)
          (hWfix e)).toMonoidHom ≤ U := by
        rintro z ⟨x, hx, rfl⟩
        have hx' : ψ x ∈ S := hx
        show ψ (Suzuki2Groups.quotientCongr (hyp.conjQByW e)
          (hWfix e) x) ∈ S
        rw [← hrhoW_apply]
        exact hSact _ hx'
      have hcardle : Nat.card
          ↥(U.map (Suzuki2Groups.quotientCongr (hyp.conjQByW e)
            (hWfix e)).toMonoidHom) = Nat.card ↥U := by
        apply Nat.card_congr
        exact (Subgroup.equivMapOfInjective U _
          (Suzuki2Groups.quotientCongr (hyp.conjQByW e)
            (hWfix e)).injective).toEquiv.symm
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardle.symm)
    -- the general two-dimensional theorem
    obtain ⟨hcyc, hdvd⟩ :=
      OddOrder.RepresentationTheory.isCyclic_and_card_dvd_card_add_one_of_projective_no_nontrivial_fixed
        rhoW hfaith hodd hdim hprojfree
    refine ⟨hcyc, ?_⟩
    rwa [GaloisField.card 2 m hm] at hdvd

/-- **Peterfalvi Part II, Ch. I §3, Lemma 5** (p. 107, complete statement).
Suppose `|st| = 3` and `Q` is a Suzuki `2`-group of order `q³` with
`q = |Q₀| = 2^m`.  Then `W` is cyclic, `|W|` divides `q + 1`, and if
`W ≠ 1` then `Q` is a Suzuki `2`-group of type B. -/
theorem lemmaFive_of_orderThree
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω) :
    IsCyclic ↥hyp.W ∧ Nat.card ↥hyp.W ∣ 2 ^ m + 1 ∧
      (hyp.W ≠ ⊥ → Suzuki2Groups.IsTypeB.{uG, 0} ↥hyp.Q) := by
  obtain ⟨hcyc, hdvd⟩ := hyp.isCyclic_W_and_card_dvd_of_orderThree hst hQsuz
    hm hQ0card hcardQ inductionHypothesis
  refine ⟨hcyc, hdvd, fun hWne => ?_⟩
  obtain ⟨w, hwW, hwbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hWne)
  exact hyp.isTypeB_Q_of_orderThree_of_mem_W hwW
    (fun h => hwbot (h ▸ Subgroup.one_mem ⊥)) hst hQsuz hm hQ0card hcardQ
    inductionHypothesis

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
