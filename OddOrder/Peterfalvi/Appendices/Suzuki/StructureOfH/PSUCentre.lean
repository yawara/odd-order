/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
import OddOrder.Peterfalvi.Appendices.Suzuki.GaloisCentralizer
import OddOrder.GroupTheory.SylowTransport
import OddOrder.GroupTheory.CentralCommutatorPower
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.TorusCentralizer

/-!
# `Z(F)` has odd order in the `PSU(3, ℓ)` branch

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3 Proposition 1(c) / Ch. III §1 Proposition, p. 117.

Chapter I §3 Proposition 1(c) gives `F = O^{2′}(C_G(P))` with
`F/Z(F) ≅ PSU(3, ℓ)` and `C_Q(P) ≅ S₀`, the Sylow `2`-subgroup of `PSU(3, ℓ)`.
Since `C_Q(P)` is *itself* a Sylow `2`-subgroup of `C_G(P)` (hence of `F`, which
it generates as a normal closure), `F` and `F/Z(F)` have Sylow `2`-subgroups of
the same order, so `Z(F)` has odd order
(`Sylow.not_dvd_natCard_of_natCard_eq`).

This is what lets the Ch. III §1 Proposition lift a statement about
`C_{G₀}(Ω₁(S₀))` back to `F`: a commutator landing in `Z(F)` against a
`2`-element must be trivial (`commute_of_commutatorElement_mem_of_coprime_natCard`).

## Main results

* `CentralizerPSUData.odd_natCard_center_residual` — `|Z(F)|` is odd.
* `CentralizerPSUData.exists_mem_residual_commute_Q0` — the lift step: a
  preimage in `F` of the torus element centralizes `C_{Q₀}(X)` outright.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
open scoped commutatorElement

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] [Finite G]

variable {hyp : Hypothesis G Omega} {X : Subgroup G}
  [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Omega)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Omega)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L}

/-- **`Z(F)` has odd order** in the `PSU(3, ℓ)` branch of Ch. I §3
Proposition 1(c).

`C_Q(P)` is a Sylow `2`-subgroup of `C = C_G(P)` and lies in
`F = O^{2′}(C) = ⟪C_Q(P)⟫^C`, so it is also a Sylow `2`-subgroup of `F`.  Its
order is `|RootGroup n|` (`cQEquivRoot`), which is exactly the order of a Sylow
`2`-subgroup of `PSU(3, ℓ) ≅ F/Z(F)` (`standardRootSylow`).  Equal Sylow orders
above and below the central quotient force `2 ∤ |Z(F)|`. -/
theorem CentralizerPSUData.odd_natCard_center_residual (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X)
    (det : CentralizerPSUData hyp X result data) :
    ¬ 2 ∣ Nat.card
      ↥(Subgroup.center ↥(Subgroup.primeComplementResidual 2
        (Subgroup.centralizer (X : Set G)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  set CQ : Subgroup ↥C := hyp.Q.subgroupOf C with hCQ
  set F : Subgroup ↥C := Subgroup.primeComplementResidual 2 C with hF
  obtain ⟨SP, hSP⟩ :=
    hyp.exists_sylow_two_eq_cQ_of_isPGroup hXV common.cQ_isPGroup
  -- `C_Q ≤ F`, so the Sylow `2`-subgroup of `C` is one of `F`
  have hle : CQ ≤ F := by
    rw [hF, common.residual_eq_normalClosure]
    exact Subgroup.le_normalClosure
  have hSPle : (SP : Subgroup ↥C) ≤ F := hSP ▸ hle
  set S : Sylow 2 ↥F := SP.subtype hSPle with hS
  -- its order is the order of the unitary root group
  have hScard : Nat.card ↥(S : Subgroup ↥F) = Nat.card (RootGroup data.n) := by
    have h1 : Nat.card ↥(S : Subgroup ↥F) = Nat.card ↥(SP : Subgroup ↥C) := by
      rw [hS, Sylow.coe_subtype]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSPle).toEquiv
    rw [h1, hSP]
    exact Nat.card_congr det.cQEquivRoot.toEquiv
  -- a Sylow `2`-subgroup of `F/Z(F) ≅ PSU(3, ℓ)` has the same order
  set T : Sylow 2 (↥F ⧸ Subgroup.center ↥F) := default with hT
  have hTcard : Nat.card ↥(T : Subgroup (↥F ⧸ Subgroup.center ↥F)) =
      Nat.card (RootGroup data.n) := by
    have hn : 0 < data.n := Nat.zero_lt_one.trans data.one_lt_n
    have hequiv := Sylow.transportMulEquiv det.residualQuotientEquiv T
      (standardRootSylow data.n hn)
    rw [Nat.card_congr hequiv.toEquiv, coe_standardRootSylow]
    exact (Nat.card_congr (rootEquivStandardRoot data.n).toEquiv).symm
  exact Sylow.not_dvd_natCard_of_natCard_eq S T (hScard.trans hTcard.symm)

/-! ## The lift step -/

/-- **The lift step of Ch. III §1, Proposition** (p. 117).

The `PSU(3, ℓ)` computation (`exists_ne_one_odd_centralizing_involutions_of_sylowTwo`)
produces `d ≠ 1` of odd order in `F/Z(F)` centralizing the involutions of a Sylow
`2`-subgroup containing the image of `C_Q(X)`.  Any preimage `x ∈ F` then has
`⁅x, y⁆ ∈ Z(F)` for every `y ∈ C_{Q₀}(X)`; since `|Z(F)|` is odd
(`odd_natCard_center_residual`) and `y` is an involution, that commutator is
trivial (`commute_of_commutatorElement_mem_of_coprime_natCard`).

The conclusion also records `d ≠ 1` and its odd order — both are needed for the
final parity contradiction. -/
theorem CentralizerPSUData.exists_mem_residual_commute_Q0 (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X)
    (det : CentralizerPSUData hyp X result data) :
    ∃ x : ↥(Subgroup.primeComplementResidual 2 (Subgroup.centralizer (X : Set G))),
      QuotientGroup.mk (s := Subgroup.center _) x ≠ 1 ∧
      Odd (orderOf (QuotientGroup.mk (s := Subgroup.center _) x)) ∧
      ∀ y ∈ hyp.Q0, y ∈ Subgroup.centralizer (X : Set G) →
        Commute ((x : ↥(Subgroup.centralizer (X : Set G))) : G) y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  set CQ : Subgroup ↥C := hyp.Q.subgroupOf C with hCQdef
  set F : Subgroup ↥C := Subgroup.primeComplementResidual 2 C with hFdef
  set Z : Subgroup ↥F := Subgroup.center ↥F with hZdef
  have hZodd : ¬ 2 ∣ Nat.card ↥Z :=
    det.odd_natCard_center_residual hXV common
  -- `C_Q(X)` is a Sylow `2`-subgroup of `F`
  obtain ⟨SP, hSP⟩ := hyp.exists_sylow_two_eq_cQ_of_isPGroup hXV common.cQ_isPGroup
  have hCQF : CQ ≤ F := by
    rw [hFdef, common.residual_eq_normalClosure]
    exact Subgroup.le_normalClosure
  have hSPle : (SP : Subgroup ↥C) ≤ F := hSP ▸ hCQF
  set S : Sylow 2 ↥F := SP.subtype hSPle with hSdef
  set π : ↥F →* (↥F ⧸ Z) := QuotientGroup.mk' Z with hπdef
  -- a Sylow `2`-subgroup of `F/Z(F)` containing the image of `S`
  obtain ⟨T, hTle⟩ := (S.isPGroup'.map π).exists_le_sylow
  -- the `PSU(3, ℓ)` computation, transported along `F/Z(F) ≅ standardPermGroup n`
  set e := det.residualQuotientEquiv with hedef
  obtain ⟨g, hgne, hgodd, hgfix⟩ :=
    exists_ne_one_odd_centralizing_involutions_of_sylowTwo data.n data.one_lt_n
      (Sylow.mapEquiv e T)
  set d : ↥F ⧸ Z := e.symm g with hddef
  have hdne : d ≠ 1 := by
    intro h
    exact hgne (by simpa [hddef] using congrArg e h)
  have hdorder : orderOf d = orderOf g := by
    simp [hddef]
  have hdodd : Odd (orderOf d) := by rw [hdorder]; exact hgodd
  have hdfix : ∀ u ∈ (T : Subgroup (↥F ⧸ Z)), u ^ 2 = 1 → d * u = u * d := by
    intro u hu hsq
    have hmem : e u ∈ (Sylow.mapEquiv e T : Subgroup (standardPermGroup data.n)) := by
      rw [Sylow.coe_mapEquiv]
      exact ⟨u, hu, rfl⟩
    have hsq' : (e u) ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
    have hcomm := hgfix _ hmem hsq'
    have h2 := congrArg e.symm hcomm
    simpa [hddef] using h2
  -- pick any preimage
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (s := Z) d
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [hx]; exact hdne
  · rw [hx]; exact hdodd
  intro y hy0 hyC
  -- realise `y` inside `F`
  have hyCQ : (⟨y, hyC⟩ : ↥C) ∈ CQ := Subgroup.mem_subgroupOf.mpr (hyp.Q0_le_Q hy0)
  have hyFmem : (⟨y, hyC⟩ : ↥C) ∈ F := hCQF hyCQ
  set yF : ↥F := ⟨⟨y, hyC⟩, hyFmem⟩ with hyFdef
  have hyS : yF ∈ (S : Subgroup ↥F) := by
    rw [hSdef, Sylow.coe_subtype]
    exact Subgroup.mem_subgroupOf.mpr (hSP ▸ hyCQ)
  have hysq : yF ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hy0.1
  have hyT : QuotientGroup.mk (s := Z) yF ∈ (T : Subgroup (↥F ⧸ Z)) :=
    hTle ⟨yF, hyS, rfl⟩
  have hyTsq : (QuotientGroup.mk (s := Z) yF) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hysq]
    rfl
  have hcomm := hdfix _ hyT hyTsq
  -- the commutator falls into `Z(F)`
  have hmemZ : ⁅x, yF⁆ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    rw [show (QuotientGroup.mk (s := Z) ⁅x, yF⁆) =
        ⁅QuotientGroup.mk (s := Z) x, QuotientGroup.mk (s := Z) yF⁆ from rfl]
    rw [hx, commutatorElement_eq_one_iff_commute]
    exact hcomm
  have hcop : Nat.Coprime (Nat.card ↥Z) (orderOf yF) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hysq) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hZodd).symm
  have hcommF : Commute x yF :=
    OddOrder.GroupTheory.commute_of_commutatorElement_mem_of_coprime_natCard
      le_rfl hmemZ hcop
  -- descend to `G`
  have hval := congrArg (fun z : ↥F => ((z : ↥C) : G)) hcommF.eq
  exact hval

/-! ## The `PSU(3, ℓ)` branch is incompatible with `W = 1` -/

/-- **Peterfalvi Part II, Ch. III §1, Proposition** (p. 117): "It follows that
`F/Z(F)` is not isomorphic to `PSU(3, ℓ)`."

Assume `W = 1`.  The lift step gives `x ∈ F` centralizing `C_{Q₀}(X)` whose image
`d` in `F/Z(F)` is non-trivial of odd order.  In particular `x` centralizes the
distinguished involution `s`, so `x ∈ C_G(s) ≤ H` (Ch. I §3 Prop 1(b)) and
`x = q v` with `q ∈ Q`, `v ∈ V` (`C_H(s) = QV`).  Since `W = 1` makes `V`
abelian, `V ≤ C_G(X)`, so `q ∈ C_Q(X)`; and `q ∈ Q` centralizes `Q₀`, so `v`
inherits from `x` the property of centralizing `C_{Q₀}(X)`.  The theorem of
Galois (`centralizer_V_centralizer_Q0_of_W_eq_bot`) then puts `v ∈ X`, which is
central in `C_G(X)` and hence in `F`, so `d` is the image of the `2`-element `q`.
A non-trivial element of odd order cannot be a `2`-element. -/
theorem CentralizerPSUData.false_of_W_eq_bot (hXV : X ≤ hyp.V) (hW : hyp.W = ⊥)
    (common : CentralizerCommonData hyp X)
    (det : CentralizerPSUData hyp X result data) : False := by
  classical
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  set CQ : Subgroup ↥C := hyp.Q.subgroupOf C with hCQdef
  set F : Subgroup ↥C := Subgroup.primeComplementResidual 2 C with hFdef
  obtain ⟨x, hdne, hdodd, hcomm⟩ :=
    det.exists_mem_residual_commute_Q0 hXV common
  set xG : G := ((x : ↥C) : G) with hxG
  -- `x` centralizes the distinguished involution
  set s : G := hyp.distinguishedInvolution with hs
  have hs0 : s ∈ hyp.Q0 :=
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
  have hsC : s ∈ C := by
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    have hgV : g ∈ hyp.V := hXV hg
    rw [hyp.V_eq_centralizer_distinguishedInvolution] at hgV
    exact (Subgroup.mem_centralizer_iff.mp hgV.2 s rfl).symm
  have hxs : Commute xG s := hcomm s hs0 hsC
  -- so `x ∈ H` and factors as `q v`
  have hxH : xG ∈ hyp.H :=
    hyp.centralizer_le_H_of_mem_Q (hyp.Q0_le_Q hs0)
      hyp.distinguishedInvolution_ne_one
      (Subgroup.mem_centralizer_singleton_iff.mpr hxs)
  obtain ⟨q, hqQ, v, hvV, hqv⟩ :=
    hyp.exists_mem_Q_mem_V_of_mem_H_of_commute_distinguishedInvolution hxH hxs
  -- `V ≤ C_G(X)` because `W = 1` makes `V` abelian
  have hvC : v ∈ C := hyp.V_le_centralizer_of_le_V_of_W_eq_bot hW hXV hvV
  have hxC : xG ∈ C := (x : ↥C).2
  have hqC : q ∈ C := by
    have : q = xG * v⁻¹ := by rw [hqv]; group
    rw [this]
    exact C.mul_mem hxC (C.inv_mem hvC)
  -- `v` centralizes `C_{Q₀}(X)`, hence lies in `X` by the theorem of Galois
  have hvGal : v ∈ hyp.V ⊓ Subgroup.centralizer
      ((hyp.Q0 ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
    refine ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hxy : Commute xG y := hcomm y hy.1 hy.2
    have hqy : Commute q y := by
      exact Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hy.1) q hqQ
    have hv : v = q⁻¹ * xG := by rw [hqv]; group
    rw [hv]
    calc y * (q⁻¹ * xG) = (y * q⁻¹) * xG := by group
      _ = (q⁻¹ * y) * xG := by rw [hqy.inv_left.eq]
      _ = q⁻¹ * (y * xG) := by group
      _ = q⁻¹ * (xG * y) := by rw [hxy.symm.eq]
      _ = (q⁻¹ * xG) * y := by group
  have hvX : v ∈ X := by
    rw [← hyp.centralizer_V_centralizer_Q0_of_W_eq_bot hW hXV]
    exact hvGal
  -- transport the factorisation into `F`
  have hqCQ : (⟨q, hqC⟩ : ↥C) ∈ CQ := Subgroup.mem_subgroupOf.mpr hqQ
  have hCQF : CQ ≤ F := by
    rw [hFdef, common.residual_eq_normalClosure]
    exact Subgroup.le_normalClosure
  have hqF : (⟨q, hqC⟩ : ↥C) ∈ F := hCQF hqCQ
  have hvF : (⟨v, hvC⟩ : ↥C) ∈ F := by
    have hveq : (⟨v, hvC⟩ : ↥C) = (⟨q, hqC⟩ : ↥C)⁻¹ * (x : ↥C) := by
      apply Subtype.ext
      change v = q⁻¹ * xG
      rw [hqv]; group
    rw [hveq]
    exact F.mul_mem (F.inv_mem hqF) x.2
  set qF : ↥F := ⟨⟨q, hqC⟩, hqF⟩ with hqFdef
  set vF : ↥F := ⟨⟨v, hvC⟩, hvF⟩ with hvFdef
  have hxqv : x = qF * vF := by
    apply Subtype.ext; apply Subtype.ext
    change xG = q * v
    exact hqv
  -- `v ∈ X` is central in `C_G(X)`, hence in `F`
  have hvZ : vF ∈ Subgroup.center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext; apply Subtype.ext
    change ((w : ↥C) : G) * v = v * ((w : ↥C) : G)
    exact (Subgroup.mem_centralizer_iff.mp (w : ↥C).2 v hvX).symm
  -- so the image of `x` is the image of the `2`-element `q`
  have himg : QuotientGroup.mk (s := Subgroup.center ↥F) x =
      QuotientGroup.mk (s := Subgroup.center ↥F) qF := by
    rw [hxqv, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff vF).mpr hvZ, mul_one]
  obtain ⟨k, hk⟩ := common.cQ_isPGroup (⟨⟨q, hqC⟩, hqCQ⟩ : ↥CQ)
  have hqpow : qF ^ 2 ^ k = 1 := by
    apply Subtype.ext; apply Subtype.ext
    change q ^ 2 ^ k = 1
    exact congrArg (fun z : ↥CQ => ((z : ↥C) : G)) hk
  have hmkpow : (QuotientGroup.mk (s := Subgroup.center ↥F) x) ^ 2 ^ k = 1 := by
    rw [himg, ← QuotientGroup.mk_pow, hqpow]
    rfl
  have hdvd : orderOf (QuotientGroup.mk (s := Subgroup.center ↥F) x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hmkpow
  have hone : orderOf (QuotientGroup.mk (s := Subgroup.center ↥F) x) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
          (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hdodd))).symm)
      dvd_rfl hdvd
  exact hdne (orderOf_eq_one_iff.mp hone)

end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
