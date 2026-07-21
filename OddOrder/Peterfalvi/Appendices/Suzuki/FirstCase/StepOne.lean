/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.FieldAction

/-!
# Peterfalvi Part II, Ch. II, step (1): fixed points on `Q₀`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (1), p. 108.

The fixed points of `P` on `Q₀` number exactly two: at most two by (B1),
and the orbit count of the `p`-group `P` acting on the `2^p` elements of
`Q₀` gives `|C_{Q₀}(P)| ≡ 2^p ≡ 2 (mod p)` by Fermat's little theorem.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)
open scoped Pointwise

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (1), fixed-point count** (p. 108):
`|C_{Q₀}(P)| = 2`. -/
theorem card_Q0_inf_centralizer_eq_two :
    Nat.card ↥(fc.toHypothesis.Q0 ⊓
      Subgroup.centralizer (fc.P : Set G)) = 2 := by
  classical
  -- the action of `P` on `Q₀` by conjugation
  set actP : ↥fc.P →* MulAut ↥fc.toHypothesis.Q0 :=
    fc.toHypothesis.conjQ0.comp
      (Subgroup.inclusion (fc.P_le_V.trans fc.toHypothesis.V_le_D))
    with hactdef
  letI : MulAction ↥fc.P ↥fc.toHypothesis.Q0 := MulAction.compHom _ actP
  haveI : Fintype ↥fc.toHypothesis.Q0 := Fintype.ofFinite _
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  have hP : IsPGroup fc.p ↥fc.P :=
    IsPGroup.of_card (by rw [fc.card_P, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints ↥fc.toHypothesis.Q0
  -- the fixed points are exactly the centralized elements
  have hmem : ∀ x : ↥fc.toHypothesis.Q0,
      x ∈ MulAction.fixedPoints ↥fc.P ↥fc.toHypothesis.Q0 ↔
        (x : G) ∈ Subgroup.centralizer (fc.P : Set G) := by
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have happ : actP ⟨g, hg⟩ x = x := hx ⟨g, hg⟩
      have hval := congrArg
        (fun y : ↥fc.toHypothesis.Q0 => (y : G)) happ
      have hconj : g * (x : G) * g⁻¹ = (x : G) := hval
      calc g * (x : G) = (g * (x : G) * g⁻¹) * g := by group
        _ = (x : G) * g := by rw [hconj]
    · intro hx g
      show actP g x = x
      apply Subtype.ext
      have hcomm := Subgroup.mem_centralizer_iff.mp hx (g : G) g.2
      show (g : G) * (x : G) * (g : G)⁻¹ = (x : G)
      calc (g : G) * (x : G) * (g : G)⁻¹
          = ((x : G) * (g : G)) * (g : G)⁻¹ := by rw [← hcomm]
        _ = (x : G) := by group
  -- transfer the count to the centralizer subgroup
  have hcardfix :
      Nat.card (MulAction.fixedPoints ↥fc.P ↥fc.toHypothesis.Q0) =
        Nat.card ↥(fc.toHypothesis.Q0 ⊓
          Subgroup.centralizer (fc.P : Set G)) := by
    apply Nat.card_congr
    exact
      { toFun := fun x =>
          ⟨((x : ↥fc.toHypothesis.Q0) : G),
            (x : ↥fc.toHypothesis.Q0).2, (hmem _).mp x.2⟩
        invFun := fun y =>
          ⟨⟨(y : G), y.2.1⟩, (hmem _).mpr y.2.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => rfl }
  -- Fermat: `2^p ≡ 2 (mod p)`
  have h2p : (2 : ℕ) ^ fc.p ≡ 2 [MOD fc.p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact ZMod.pow_card (2 : ZMod fc.p)
  -- assemble
  set c := Nat.card ↥(fc.toHypothesis.Q0 ⊓
    Subgroup.centralizer (fc.P : Set G)) with hcdef
  have hcmod : (2 : ℕ) ≡ c [MOD fc.p] := by
    have h1 : (2 : ℕ) ^ fc.p ≡ c [MOD fc.p] := by
      rw [← fc.card_Q0_eq_two_pow, ← hcardfix]
      exact hmod
    exact h2p.symm.trans h1
  have hle : c ≤ 2 := fc.card_Q0_inf_centralizer_le_two
  have hp3 : 3 ≤ fc.p := by
    have h2 := fc.p_prime.two_le
    have hne := fc.p_ne_two
    omega
  have hmodeq : 2 % fc.p = c % fc.p := hcmod
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmodeq
  omega

/-- A `P`-fixed element of the Fitting subgroup of `D̄` is trivial: its
`μ`-coordinate is a `P`-fixed unit of the field model, hence a unit of the
two-element fixed subfield. -/
theorem fitting_eq_one_of_conjAction_fixed
    {t : ↥(fitting fc.toHypothesis.Dbar)}
    (hfix : ∀ g : ↥fc.P,
      fc.toHypothesis.fittingConjAction (fc.toVbar g) t = t) :
    t = 1 := by
  obtain ⟨F, hField, hFinite, eQ, μ, σhom, hcardF, hσinj, hbridge,
      hunits, hfixmem⟩ := fc.exists_adapted_field_model
  letI : Field F := hField
  letI : Finite F := hFinite
  have hμfix : ∀ g : ↥fc.P,
      σhom g ((μ t : Fˣ) : F) = ((μ t : Fˣ) : F) := by
    intro g
    have hu := hunits g t
    rw [hfix g] at hu
    have hval := congrArg (fun u : Fˣ => (u : F)) hu
    rw [fieldRingAutOnUnits_apply_val] at hval
    exact hval.symm
  rcases hfixmem _ hμfix with h0 | h1
  · exact absurd h0 (Units.ne_zero (μ t))
  · have hμt1 : μ t = 1 := Units.ext h1
    exact μ.injective (by rw [hμt1, map_one])

/-- **Peterfalvi Part II, Ch. II, step (1), trivial `K`-fixed points**
(p. 108): `C_K(P) = 1`.  A `P`-centralized element of `K` maps to a
`P`-fixed unit of the field model, hence to a unit of the two-element
fixed subfield, so its image in `D̄` is trivial and it lies in
`K ∩ W ≤ K ∩ V = 1`. -/
theorem K_inf_centralizer_eq_bot :
    fc.toHypothesis.K ⊓ Subgroup.centralizer (fc.P : Set G) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨hkK, hkC⟩ := hk
  rw [Subgroup.mem_bot]
  have hkD : k ∈ fc.toHypothesis.D := fc.toHypothesis.K_le_D hkK
  set kbar : fc.toHypothesis.Dbar :=
    QuotientGroup.mk ⟨k, hkD⟩ with hkbar
  have hkfit : kbar ∈ fitting fc.toHypothesis.Dbar := by
    rw [← fc.toHypothesis.Kbar_eq_fitting]
    exact ⟨⟨k, hkD⟩, hkK, rfl⟩
  set t : ↥(fitting fc.toHypothesis.Dbar) := ⟨kbar, hkfit⟩ with htdef
  -- `P` fixes `t` under the conjugation action on the Fitting subgroup
  have hfixt : ∀ g : ↥fc.P,
      fc.toHypothesis.fittingConjAction (fc.toVbar g) t = t := by
    intro g
    apply Subtype.ext
    simp only [Hypothesis.fittingConjAction, MonoidHom.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    show ((fc.toVbar g : ↥fc.toHypothesis.Vbar) : fc.toHypothesis.Dbar) *
        kbar *
        (((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
          fc.toHypothesis.Dbar))⁻¹ = kbar
    rw [toVbar_coe, hkbar, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hcomm := Subgroup.mem_centralizer_iff.mp hkC (g : G) g.2
    show (g : G) * k * (g : G)⁻¹ = k
    calc (g : G) * k * (g : G)⁻¹ = (k * (g : G)) * (g : G)⁻¹ := by
          rw [← hcomm]
      _ = k := by group
  have ht1 : t = 1 := fc.fitting_eq_one_of_conjAction_fixed hfixt
  have hkbar1 : kbar = 1 := congrArg Subtype.val ht1
  rw [hkbar, QuotientGroup.eq_one_iff] at hkbar1
  have hkW : k ∈ fc.toHypothesis.W := hkbar1
  have hVK : k ∈ fc.toHypothesis.V ⊓ fc.toHypothesis.K :=
    ⟨fc.toHypothesis.W_le_V hkW, hkK⟩
  rw [fc.toHypothesis.V_inf_K_eq_bot] at hVK
  exact Subgroup.mem_bot.mp hVK

/-- **Peterfalvi Part II, Ch. II, step (1), the decomposition** (p. 108):
every element of `V` is a product `g * w` with `g ∈ P` and `w ∈ W`.  The
quotient `V̄ = V/W` embeds into `Aut F ≅ Gal(F/F₂)`, which has order `p`;
since `P̄ ≤ V̄` already has order `p`, the two coincide. -/
theorem exists_decomp_of_mem_V {v : G} (hv : v ∈ fc.toHypothesis.V) :
    ∃ g ∈ fc.P, (g : G)⁻¹ * v ∈ fc.toHypothesis.W := by
  classical
  -- the semilinear model bounds `|V̄|` by `|Aut F| = p`
  obtain ⟨F, hField, hFinite, A, hcardF, hVcyc, eQ, μ, νe,
      hT, hE, hκ, eL, hL1, hL2, hL3⟩ := fc.toHypothesis.exists_semilinear_equiv
  letI : Field F := hField
  letI : Finite F := hFinite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (RingAut F) :=
    Finite.of_injective (DFunLike.coe : RingAut F → (F → F))
      DFunLike.coe_injective
  -- `F` has characteristic 2
  have hcardF2p : Fintype.card F = 2 ^ fc.p := by
    rw [← Nat.card_eq_fintype_card, hcardF, fc.card_Q0_eq_two_pow]
  set q := ringChar F with hqdef
  haveI hqchar : CharP F q := ringChar.charP F
  have hqprime : q.Prime := CharP.char_is_prime F q
  have hq2 : q = 2 := by
    obtain ⟨n, -, hn⟩ := FiniteField.card F q
    have hdvd : q ∣ 2 ^ fc.p := by
      rw [← hcardF2p, hn]
      exact dvd_pow_self q (by exact_mod_cast n.ne_zero)
    exact (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).mp
      (hqprime.dvd_of_dvd_pow hdvd)
  haveI : CharP F 2 := hq2 ▸ hqchar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  -- `|Aut F| = p`
  have hfinrank : Module.finrank (ZMod 2) F = fc.p := by
    have hpow : (2 : ℕ) ^ Module.finrank (ZMod 2) F = 2 ^ fc.p := by
      calc (2 : ℕ) ^ Module.finrank (ZMod 2) F
          = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) F := by
            rw [ZMod.card]
        _ = Fintype.card F := Module.card_eq_pow_finrank.symm
        _ = 2 ^ fc.p := hcardF2p
    exact Nat.pow_right_injective (le_refl 2) hpow
  have hringaut : Nat.card (RingAut F) = fc.p := by
    rw [OddOrder.RepresentationTheory.natCard_ringAut_eq_finrank F 2,
      hfinrank]
  -- `|V̄| = p`, so `V̄` is the image of `P`
  have hcardVbar_dvd : Nat.card ↥fc.toHypothesis.Vbar ∣ fc.p := by
    rw [← hringaut, Nat.card_congr νe.toEquiv]
    exact Subgroup.card_subgroup_dvd_card A
  have hcardrange : Nat.card ↥fc.toVbar.range = fc.p := by
    rw [← fc.card_P]
    exact (Nat.card_congr
      (MonoidHom.ofInjective fc.toVbar_injective).toEquiv.symm)
  have hple : fc.p ≤ Nat.card ↥fc.toHypothesis.Vbar := by
    rw [← hcardrange]
    exact Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_subgroup_dvd_card fc.toVbar.range)
  have hcardVbar : Nat.card ↥fc.toHypothesis.Vbar = fc.p := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd fc.p_prime _ hcardVbar_dvd)
      with h1 | hp
    · have h2 := fc.p_prime.two_le
      omega
    · exact hp
  have hrange_top : fc.toVbar.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcardrange, hcardVbar]
  -- read off the decomposition
  have hvD : v ∈ fc.toHypothesis.D := fc.toHypothesis.V_le_D hv
  have hzmem : (⟨QuotientGroup.mk ⟨v, hvD⟩, ⟨⟨v, hvD⟩, hv, rfl⟩⟩ :
      ↥fc.toHypothesis.Vbar) ∈ fc.toVbar.range := by
    rw [hrange_top]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := hzmem
  have hval := congrArg
    (fun z : ↥fc.toHypothesis.Vbar => (z : fc.toHypothesis.Dbar)) hg
  simp only [toVbar_coe] at hval
  rw [QuotientGroup.eq] at hval
  have hmemW : (g : G)⁻¹ * v ∈ fc.toHypothesis.W := hval
  exact ⟨(g : G), g.2, hmemW⟩

/-- **Peterfalvi Part II, Ch. II, step (1), the splitting** (p. 108):
`V = W ⋊ P`, stated as `W ⊔ P = V` (the intersection is trivial by
`P_inf_W_eq_bot`). -/
theorem W_join_P_eq_V : fc.toHypothesis.W ⊔ fc.P = fc.toHypothesis.V := by
  apply le_antisymm
  · exact sup_le fc.toHypothesis.W_le_V fc.P_le_V
  · intro v hv
    obtain ⟨g, hg, hw⟩ := fc.exists_decomp_of_mem_V hv
    have hdecomp : v = g * (g⁻¹ * v) := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right hg)
      (Subgroup.mem_sup_left hw)

/-- Conjugation by `D` preserves `W`: `W` is the kernel of the conjugation
action of `D` on `Q₀`. -/
theorem conj_mem_W_of_mem_D {d w : G} (hd : d ∈ fc.toHypothesis.D)
    (hw : w ∈ fc.toHypothesis.W) :
    d * w * d⁻¹ ∈ fc.toHypothesis.W := by
  have hwD : w ∈ fc.toHypothesis.D :=
    fc.toHypothesis.V_le_D (fc.toHypothesis.W_le_V hw)
  have h1 : (⟨w, hwD⟩ : ↥fc.toHypothesis.D) ∈ fc.toHypothesis.conjQ0.ker := by
    rw [fc.toHypothesis.ker_conjQ0]
    exact hw
  have h2 : (⟨d, hd⟩ : ↥fc.toHypothesis.D) * ⟨w, hwD⟩ * (⟨d, hd⟩)⁻¹ ∈
      fc.toHypothesis.conjQ0.ker :=
    (MonoidHom.normal_ker fc.toHypothesis.conjQ0).conj_mem _ h1 _
  rw [fc.toHypothesis.ker_conjQ0] at h2
  exact h2

/-- `P` has prime order, hence is abelian and centralizes itself. -/
theorem P_le_centralizer : fc.P ≤ Subgroup.centralizer (fc.P : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI : IsCyclic ↥fc.P := isCyclic_of_prime_card fc.card_P
  letI : CommGroup ↥fc.P := IsCyclic.commGroup
  have hcomm : (⟨x, hx⟩ : ↥fc.P) * ⟨g, hg⟩ = ⟨g, hg⟩ * ⟨x, hx⟩ :=
    mul_comm _ _
  exact congrArg Subtype.val hcomm

/-- An element of `W` normalizing `P` centralizes it: the commutator lands
in `P ∩ W = 1`. -/
theorem centralizer_of_mem_W_of_mem_normalizer
    {w : G} (hwW : w ∈ fc.toHypothesis.W)
    (hwN : w ∈ Subgroup.normalizer ((fc.P : Set G))) :
    w ∈ Subgroup.centralizer (fc.P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxD : x ∈ fc.toHypothesis.D :=
    fc.toHypothesis.V_le_D (fc.P_le_V hx)
  have hy : w * x * w⁻¹ ∈ fc.P :=
    (Subgroup.mem_normalizer_iff.mp hwN x).mp hx
  have hyx_W : (w * x * w⁻¹) * x⁻¹ ∈ fc.toHypothesis.W := by
    have hconj : x * w⁻¹ * x⁻¹ ∈ fc.toHypothesis.W :=
      fc.conj_mem_W_of_mem_D hxD (fc.toHypothesis.W.inv_mem hwW)
    have heq : (w * x * w⁻¹) * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
    rw [heq]
    exact fc.toHypothesis.W.mul_mem hwW hconj
  have hbot : (w * x * w⁻¹) * x⁻¹ ∈ fc.P ⊓ fc.toHypothesis.W :=
    ⟨fc.P.mul_mem hy (fc.P.inv_mem hx), hyx_W⟩
  rw [fc.P_inf_W_eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at hbot
  calc x * w = (w * x * w⁻¹) * w := by rw [hbot]
    _ = w * x := by group

/-- **Peterfalvi Part II, Ch. II, step (1), self-normalizing centralizer**
(p. 108): `N_G(P) = C_G(P)`.  By §3 Proposition 1(b),
`N_G(P) = C_G(P) N_V(P)`, and `N_V(P) = C_W(P) P ≤ C_G(P)`. -/
theorem normalizer_P_eq_centralizer :
    Subgroup.normalizer ((fc.P : Set G)) =
      Subgroup.centralizer (fc.P : Set G) := by
  apply le_antisymm
  · intro n hn
    have hn' : n ∈ (Subgroup.centralizer (fc.P : Set G) : Set G) *
        ((fc.toHypothesis.V ⊓ Subgroup.normalizer ((fc.P : Set G)) :
          Subgroup G) : Set G) := by
      rw [← fc.toHypothesis.normalizer_eq_centralizer_mul_normalizer_inf_V
        fc.P_le_V]
      exact hn
    rw [Set.mem_mul] at hn'
    obtain ⟨c, hc, v, hv, rfl⟩ := hn'
    apply Subgroup.mul_mem _ hc
    obtain ⟨hvV, hvN⟩ := hv
    obtain ⟨g, hg, hw⟩ := fc.exists_decomp_of_mem_V hvV
    have hgN : g ∈ Subgroup.normalizer ((fc.P : Set G)) :=
      Subgroup.le_normalizer hg
    have hwN : g⁻¹ * v ∈ Subgroup.normalizer ((fc.P : Set G)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hvN
    have hwC := fc.centralizer_of_mem_W_of_mem_normalizer hw hwN
    have hdecomp : v = g * (g⁻¹ * v) := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _ (fc.P_le_centralizer hg) hwC
  · intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxP
      have hcomm := Subgroup.mem_centralizer_iff.mp hc x hxP
      have heq : c * x * c⁻¹ = x := by
        calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [← hcomm]
          _ = x := by group
      rw [heq]
      exact hxP
    · intro hcx
      have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hcx
      have heq : x = c * x * c⁻¹ := by
        have h2 : c * x = c * (c * x * c⁻¹) := by
          calc c * x = (c * x * c⁻¹) * c := by group
            _ = c * (c * x * c⁻¹) := hcomm
        exact mul_left_cancel h2
      rw [heq]
      exact hcx

/-- **Peterfalvi Part II, Ch. II, step (1), the centralizer in `D`**
(p. 108): `C_D(P) = C_W(P) × P`, stated as a join.  Splitting
`d̄ = t·z ∈ D̄ = F(D̄) ⋊ V̄`, centralization of `P̄` forces the components
into `fitting ⊓ V̄ = 1`-separated fixed parts; the Fitting component is
trivial by the field model, so `d ∈ V`, and the `V`-decomposition
finishes. -/
theorem D_inf_centralizer_eq_W_inf_centralizer_join_P :
    fc.toHypothesis.D ⊓ Subgroup.centralizer (fc.P : Set G) =
      (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P := by
  classical
  apply le_antisymm
  swap
  · apply sup_le
    · exact inf_le_inf_right _
        (fc.toHypothesis.W_le_V.trans fc.toHypothesis.V_le_D)
    · intro g hg
      exact ⟨fc.toHypothesis.V_le_D (fc.P_le_V hg), fc.P_le_centralizer hg⟩
  · intro d hd
    obtain ⟨hdD, hdC⟩ := hd
    -- split `d̄ = t * z` in `D̄`
    set dbar : fc.toHypothesis.Dbar := QuotientGroup.mk ⟨d, hdD⟩ with hdbar
    have hsplit : dbar ∈
        (fitting fc.toHypothesis.Dbar : Set fc.toHypothesis.Dbar) *
          (fc.toHypothesis.Vbar : Set fc.toHypothesis.Dbar) := by
      rw [fc.toHypothesis.fitting_isComplement_Vbar.mul_eq]
      trivial
    rw [Set.mem_mul] at hsplit
    obtain ⟨t, htmem, z, hzmem, htz⟩ := hsplit
    -- `d̄` centralizes the image of `P`
    have hcent : ∀ g : ↥fc.P,
        dbar * ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
          fc.toHypothesis.Dbar) =
        ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
          fc.toHypothesis.Dbar) * dbar := by
      intro g
      rw [toVbar_coe, hdbar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hdC (g : G) g.2).symm
    -- component analysis: the `V̄`-conjugate stays, the commutator separates
    have hdisj : fitting fc.toHypothesis.Dbar ⊓ fc.toHypothesis.Vbar = ⊥ :=
      fc.toHypothesis.fitting_isComplement_Vbar.disjoint.eq_bot
    have hcomp : ∀ g : ↥fc.P,
        t * (z * ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
          fc.toHypothesis.Dbar) * z⁻¹) * t⁻¹ =
        ((fc.toVbar g : ↥fc.toHypothesis.Vbar) : fc.toHypothesis.Dbar) := by
      intro g
      have h1 := hcent g
      rw [← htz] at h1
      calc t * (z * ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
              fc.toHypothesis.Dbar) * z⁻¹) * t⁻¹
          = ((t * z) * ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
              fc.toHypothesis.Dbar)) * (z⁻¹ * t⁻¹) := by group
        _ = ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
              fc.toHypothesis.Dbar) := by
            rw [h1]
            group
    -- the Fitting component is `P`-fixed, hence trivial
    have hfixt : ∀ g : ↥fc.P,
        fc.toHypothesis.fittingConjAction (fc.toVbar g) ⟨t, htmem⟩ =
          ⟨t, htmem⟩ := by
      intro g
      set gbar : fc.toHypothesis.Dbar :=
        ((fc.toVbar g : ↥fc.toHypothesis.Vbar) : fc.toHypothesis.Dbar)
        with hgbar
      have hgbarV : gbar ∈ fc.toHypothesis.Vbar := (fc.toVbar g).2
      set u : fc.toHypothesis.Dbar := z * gbar * z⁻¹ with hu
      have huV : u ∈ fc.toHypothesis.Vbar :=
        fc.toHypothesis.Vbar.mul_mem
          (fc.toHypothesis.Vbar.mul_mem hzmem hgbarV)
          (fc.toHypothesis.Vbar.inv_mem hzmem)
      have hcu : t * u * t⁻¹ = gbar := hcomp g
      have hw'V : t * u * t⁻¹ * u⁻¹ ∈ fc.toHypothesis.Vbar := by
        rw [hcu]
        exact fc.toHypothesis.Vbar.mul_mem hgbarV
          (fc.toHypothesis.Vbar.inv_mem huV)
      have hw'F : t * u * t⁻¹ * u⁻¹ ∈ fitting fc.toHypothesis.Dbar := by
        have hconj : u * t⁻¹ * u⁻¹ ∈ fitting fc.toHypothesis.Dbar :=
          Subgroup.Normal.conj_mem inferInstance _
            ((fitting fc.toHypothesis.Dbar).inv_mem htmem) u
        have heq : t * u * t⁻¹ * u⁻¹ = t * (u * t⁻¹ * u⁻¹) := by group
        rw [heq]
        exact (fitting fc.toHypothesis.Dbar).mul_mem htmem hconj
      have hw'bot : t * u * t⁻¹ * u⁻¹ ∈
          fitting fc.toHypothesis.Dbar ⊓ fc.toHypothesis.Vbar :=
        ⟨hw'F, hw'V⟩
      rw [hdisj, Subgroup.mem_bot, mul_inv_eq_one] at hw'bot
      -- so `t` commutes with `u = ḡ`
      have hgu : gbar = u := by rw [← hcu, hw'bot]
      have htg : gbar * t * gbar⁻¹ = t := by
        have h2 : t * gbar * t⁻¹ = gbar := by
          rw [hgu]
          exact hw'bot
        have hcommute : t * gbar = gbar * t := by
          calc t * gbar = (t * gbar * t⁻¹) * t := by group
            _ = gbar * t := by rw [h2]
        calc gbar * t * gbar⁻¹ = (t * gbar) * gbar⁻¹ := by rw [← hcommute]
          _ = t := by group
      apply Subtype.ext
      simp only [Hypothesis.fittingConjAction, MonoidHom.comp_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact htg
    have ht1 : (⟨t, htmem⟩ : ↥(fitting fc.toHypothesis.Dbar)) = 1 :=
      fc.fitting_eq_one_of_conjAction_fixed hfixt
    have ht1' : t = 1 := congrArg Subtype.val ht1
    -- `d̄ = z ∈ V̄`, hence `d ∈ V`
    have hdbarV : dbar ∈ fc.toHypothesis.Vbar := by
      rw [← htz, ht1', one_mul]
      exact hzmem
    obtain ⟨vd, hvdV, hvd⟩ := hdbarV
    have hvw : (vd : G)⁻¹ * d ∈ fc.toHypothesis.W := by
      have heq : QuotientGroup.mk vd = dbar := hvd
      rw [hdbar, QuotientGroup.eq] at heq
      exact heq
    have hdV : d ∈ fc.toHypothesis.V := by
      have hdecomp : d = (vd : G) * ((vd : G)⁻¹ * d) := by group
      rw [hdecomp]
      exact fc.toHypothesis.V.mul_mem hvdV
        (fc.toHypothesis.W_le_V hvw)
    -- decompose inside `V`
    obtain ⟨g, hg, hw⟩ := fc.exists_decomp_of_mem_V hdV
    have hwC : g⁻¹ * d ∈ Subgroup.centralizer (fc.P : Set G) :=
      Subgroup.mul_mem _
        (Subgroup.inv_mem _ (fc.P_le_centralizer hg)) hdC
    have hdecomp : d = g * (g⁻¹ * d) := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right hg)
      (Subgroup.mem_sup_left ⟨hw, hwC⟩)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
