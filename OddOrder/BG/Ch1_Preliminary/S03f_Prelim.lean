/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.BG.Ch1_Preliminary.S01_Solvable

/-!
# BG §3: standalone preliminaries for Theorem 3.6

Committable, reusable helper lemmas extracted from the Theorem 3.6 development (`S03f_Thm36`).
Kept separate from the (multi-session, `sorry`-bearing) assembly scaffold so that finished pieces
can land on their own.

## Main results

* `fitting_eq_opCore_of_oPiCore_compl_eq_bot`: if `O_{p'}(G) = ⊥` then `F(G) = O_p(G)`.  Used at
  BG Theorem 3.6 (3.9) (`V = F(H) = O_p(H)`).
* `mulAut_eq_one_of_coprime_orderOf_of_frattini`: element form of Burnside's Theorem 1.8 — a
  `p'`-order automorphism of a finite `p`-group acting trivially modulo `Φ` is trivial.
* `isPGroup_of_forall_eq_one_of_not_dvd_orderOf`: a finite group with no nontrivial `p'`-element is
  a `p`-group.
* `oPiCore_compl_quotient_frattini_fitting_eq_bot`: BG Theorem 3.6 (3.9) substep — if `F(Hb)` is a
  `p`-group then `O_{p'}(Hb / Φ(F(Hb))) = ⊥`.
-/

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement

/-- **`F(G) = O_p(G)` when `O_{p'}(G) = ⊥`** (BG Theorem 3.6 (3.9)).

The Fitting subgroup is the supremum of the `p`-cores `O_q(G)` over the prime factors `q` of `|G|`
(`fitting_eq_iSup_primeFactors`).  Each `O_q(G)` with `q ≠ p` is a normal `q`-group, hence a normal
`{p}ᶜ`-group, hence `≤ O_{p'}(G) = ⊥`; so only the `q = p` term survives and `F(G) = O_p(G)`. -/
theorem fitting_eq_opCore_of_oPiCore_compl_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (h : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) G = ⊥) :
    OddOrder.Isaacs.Ch01.fitting G = OddOrder.Isaacs.Ch01.opCore p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ (OddOrder.Isaacs.Ch01.opCore_le_fitting ⟨p, hp⟩ G)
  rw [OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors]
  refine iSup_le (fun q => ?_)
  haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
  by_cases hq : (q : ℕ) = p
  · subst hq; exact le_refl _
  · have hle : OddOrder.Isaacs.Ch01.opCore (q : ℕ) G
        ≤ OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) G := by
      refine OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
      intro r hr
      obtain ⟨nq, hnq⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup (q : ℕ) G).exists_card_eq
      rw [hnq] at hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrq : r = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
        (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
      simp [hrq, hq]
    rw [h] at hle
    exact le_trans hle bot_le

/-- **Element form of BG Theorem 1.8 (Burnside)**: a `p'`-order automorphism `f` of a finite
`p`-group `H` all of whose powers act trivially modulo `Φ(H)` is the identity.

This is `burnside_operator` applied to the cyclic group `⟨f⟩` (coprimality from the `p'`-order). -/
theorem mulAut_eq_one_of_coprime_orderOf_of_frattini {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] (hH : IsPGroup p H)
    (f : MulAut H) (hcop : Nat.Coprime (orderOf f) p)
    (htriv : ∀ z : ℤ, ∀ r : H, ∃ x ∈ _root_.frattini H, (f ^ z) r = r * x) :
    f = 1 := by
  classical
  set B : Subgroup (MulAut H) := Subgroup.zpowers f with hB
  set ψ : ↥B →* MulAut H := B.subtype with hψ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  have hcop' : Nat.Coprime (Nat.card ↥B) (Nat.card H) := by
    rw [hB, Nat.card_zpowers, hn]
    exact Nat.Coprime.pow_right n hcop
  have htriv' : ∀ b : ↥B, ∀ r : H, ∃ x ∈ _root_.frattini H, (ψ b) r = r * x := by
    rintro ⟨b, hb⟩ r
    rw [hB, Subgroup.mem_zpowers_iff] at hb
    obtain ⟨z, rfl⟩ := hb
    exact htriv z r
  have hconc := OddOrder.BG.Ch1.S01.burnside_operator hH (φ := ψ) hcop' htriv'
  ext r
  rw [MulAut.one_apply]
  exact hconc ⟨f, Subgroup.mem_zpowers f⟩ r

/-- A finite group with no nontrivial `p'`-element is a `p`-group: the `p'`-part `g ^ (p ^ vₚ)`
of any element has order coprime to `p`, hence is trivial, so `g` has `p`-power order. -/
theorem isPGroup_of_forall_eq_one_of_not_dvd_orderOf {p : ℕ} [hp : Fact p.Prime]
    {W : Type*} [Group W] [Finite W]
    (h : ∀ w : W, ¬ p ∣ orderOf w → w = 1) : IsPGroup p W := by
  intro g
  refine ⟨(orderOf g).factorization p, h _ ?_⟩
  have ho : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hdvd : p ^ (orderOf g).factorization p ∣ orderOf g := Nat.ordProj_dvd _ _
  rw [orderOf_pow g, Nat.gcd_eq_right hdvd]
  exact hp.out.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hp.out ho)

/-- The image under `V.subtype` of the Frattini subgroup of `V = F(Hb)` is **characteristic** in
`Hb`: `Φ(V)` is characteristic in the characteristic subgroup `V`
(characteristic-of-characteristic).

The characteristic strength (over mere normality) is needed so that, for `Hb = ↥H` with `H ◁ G`, the
further lift `Φ(V).map H.subtype` is normal in `G` (mathlib instance
`ConjAct.normal_of_characteristic_of_normal`). -/
theorem frattini_fitting_map_characteristic {Hb : Type*} [Group Hb] [Finite Hb] :
    ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting Hb)).map
      (OddOrder.Isaacs.Ch01.fitting Hb).subtype).Characteristic := by
  set V : Subgroup Hb := OddOrder.Isaacs.Ch01.fitting Hb with hVdef
  haveI hVchar : V.Characteristic := by rw [hVdef]; infer_instance
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨x, hxPhi, rfl⟩ := hy
  rw [Subgroup.mem_map] at hxPhi
  obtain ⟨k, hkfr, rfl⟩ := hxPhi
  -- restrict `φ` to an automorphism `ψ` of `↥V` (using `V` characteristic)
  have hVmap : V.map φ.toMonoidHom = V := Subgroup.characteristic_iff_map_eq.mp hVchar φ
  set ψ : ↥V ≃* ↥V := (φ.subgroupMap V).trans (MulEquiv.subgroupCongr hVmap) with hψ
  have hψk : ψ k ∈ _root_.frattini ↥V := by
    have hmap := Subgroup.characteristic_iff_map_eq.mp (frattini_characteristic (G := ↥V)) ψ
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hkfr
  exact ⟨ψ k, hψk, rfl⟩

/-- **BG Theorem 3.6 (3.9), key substep**: if the Fitting subgroup `V = F(Hb)` of a finite solvable
group is a `p`-group, then `O_{p'}(Hb / Φ(V)) = ⊥`.

Let `Q = Hb / Φ(V)`, `Ō = O_{p'}(Q)`, and `W` the preimage of `Ō` in `Hb`.  The image `V̄ = V/Φ(V)`
(a `p`-group) and `Ō` (a `p'`-group) are coprime normal subgroups of `Q`, hence centralize each
other, so `⁅V, W⁆ ≤ Φ(V)`.  Thus every `p'`-element `w` of `W` acts trivially on `V/Φ(V)`, and by
Burnside (Theorem 1.8, `mulAut_eq_one_of_coprime_orderOf_of_frattini`) trivially on `V`; so
`w ∈ C_Hb(V) ≤ V` (Proposition 1.3, `centralizer_fitting_le_fitting`), and being a `p'`-element of
the `p`-group `V` it is trivial.  Hence `W` is a `p`-group, so its image `Ō` is both a `p`- and a
`p'`-group, i.e. trivial. -/
theorem oPiCore_compl_quotient_frattini_fitting_eq_bot
    {p : ℕ} [hp : Fact p.Prime] {Hb : Type*} [Group Hb] [Finite Hb] [IsSolvable Hb]
    (hVp : IsPGroup p ↥(OddOrder.Isaacs.Ch01.fitting Hb))
    [hPhiNorm : ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting Hb)).map
      (OddOrder.Isaacs.Ch01.fitting Hb).subtype).Normal] :
    OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ)
      (Hb ⧸ ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting Hb)).map
        (OddOrder.Isaacs.Ch01.fitting Hb).subtype)) = ⊥ := by
  classical
  set V : Subgroup Hb := OddOrder.Isaacs.Ch01.fitting Hb with hVdef
  haveI hVnorm : V.Normal := by rw [hVdef]; infer_instance
  set Phi : Subgroup Hb := (_root_.frattini ↥V).map V.subtype with hPhidef
  set Ō : Subgroup (Hb ⧸ Phi) := OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) (Hb ⧸ Phi) with hOdef
  set W : Subgroup Hb := Ō.comap (QuotientGroup.mk' Phi) with hWdef
  set Vbar : Subgroup (Hb ⧸ Phi) := V.map (QuotientGroup.mk' Phi) with hVbardef
  -- `Vbar` is a normal `p`-group; `Ō` is a `p'`-group.
  haveI hVbarNorm : Vbar.Normal :=
    hVbardef ▸ hVnorm.map (QuotientGroup.mk' Phi) (QuotientGroup.mk'_surjective Phi)
  have hVbarP : IsPGroup p ↥Vbar :=
    hVbardef ▸ hVp.of_surjective (MonoidHom.subgroupMap (QuotientGroup.mk' Phi) V)
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Phi) V)
  have hO_p' : ¬ p ∣ Nat.card ↥Ō := by
    intro hd
    have hmem := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := Hb ⧸ Phi) ({p}ᶜ : Set ℕ) p
      (Nat.mem_primeFactors.mpr ⟨hp.out, hd, Nat.card_pos.ne'⟩)
    simp at hmem
  -- `⁅Vbar, Ō⁆ = ⊥` (coprime normal subgroups centralize).
  have hcop : Nat.Coprime (Nat.card ↥Vbar) (Nat.card ↥Ō) := by
    obtain ⟨k, hk⟩ := hVbarP.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (hp.out.coprime_iff_not_dvd.mpr hO_p')
  have hcomm_bot : (⁅Vbar, Ō⁆ : Subgroup (Hb ⧸ Phi)) = ⊥ := by
    have hle : (⁅Vbar, Ō⁆ : Subgroup (Hb ⧸ Phi)) ≤ Vbar ⊓ Ō := Subgroup.commutator_le_inf Vbar Ō
    rw [Subgroup.inf_eq_bot_of_coprime hcop] at hle
    exact le_bot_iff.mp hle
  -- `⁅V, W⁆ ≤ Φ(V)` (pull back the commutator).
  have hVW_le_Phi : (⁅V, W⁆ : Subgroup Hb) ≤ Phi := by
    rw [Subgroup.commutator_le]
    intro v hv w hw
    have hmv : QuotientGroup.mk' Phi v ∈ Vbar := hVbardef ▸ Subgroup.mem_map_of_mem _ hv
    have hmw : QuotientGroup.mk' Phi w ∈ Ō := (Subgroup.mem_comap).mp hw
    have hmem : QuotientGroup.mk' Phi ⁅v, w⁆ ∈ (⊥ : Subgroup (Hb ⧸ Phi)) := by
      rw [← hcomm_bot, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator hmv hmw
    rw [Subgroup.mem_bot] at hmem
    have hker : ⁅v, w⁆ ∈ (QuotientGroup.mk' Phi).ker := MonoidHom.mem_ker.mpr hmem
    rwa [QuotientGroup.ker_mk'] at hker
  -- every `p'`-element of `W` is trivial.
  have hWp' : ∀ w : ↥W, ¬ p ∣ orderOf w → w = 1 := by
    rintro ⟨g, hgW⟩ hg_p'
    have hord_eq : orderOf (⟨g, hgW⟩ : ↥W) = orderOf g :=
      (orderOf_injective W.subtype (Subgroup.subtype_injective W) ⟨g, hgW⟩).symm
    rw [hord_eq] at hg_p'
    set f : MulAut ↥V := MulAut.conjNormal (G := Hb) (H := V) g with hf
    have hf_ord : orderOf f ∣ orderOf g := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hf, ← map_pow, pow_orderOf_eq_one, map_one]
    have hf_p' : ¬ p ∣ orderOf f := fun hd => hg_p' (hd.trans hf_ord)
    have hfcop : Nat.Coprime (orderOf f) p := (hp.out.coprime_iff_not_dvd.mpr hf_p').symm
    have hftriv : ∀ z : ℤ, ∀ r : ↥V, ∃ x ∈ _root_.frattini ↥V, (f ^ z) r = r * x := by
      intro z r
      refine ⟨r⁻¹ * (f ^ z) r, ?_, by group⟩
      set x : ↥V := r⁻¹ * (f ^ z) r with hx
      have hcoe : ((f ^ z) r : Hb) = (g ^ z) * (r : Hb) * (g ^ z)⁻¹ := by
        rw [hf, ← map_zpow MulAut.conjNormal g z, MulAut.conjNormal_apply]
      have hxcoe : (x : Hb) = ⁅(r : Hb)⁻¹, g ^ z⁆ := by
        rw [hx, Subgroup.coe_mul, Subgroup.coe_inv, hcoe, commutatorElement_def]; group
      have hmemVW : ⁅(r : Hb)⁻¹, g ^ z⁆ ∈ (⁅V, W⁆ : Subgroup Hb) :=
        Subgroup.commutator_mem_commutator (V.inv_mem r.2) (W.zpow_mem hgW z)
      have hxPhi : (x : Hb) ∈ Phi := by rw [hxcoe]; exact hVW_le_Phi hmemVW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxPhi
      rw [Subgroup.coe_subtype] at hyx
      have hyx' : y = x := Subtype.coe_injective hyx
      rwa [hyx'] at hy
    have hf1 : f = 1 := mulAut_eq_one_of_coprime_orderOf_of_frattini hVp f hfcop hftriv
    have hg_cent : g ∈ Subgroup.centralizer (V : Set Hb) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : ((MulAut.conjNormal (G := Hb) (H := V) g) ⟨v, hv⟩ : Hb) = v := by
        rw [show (MulAut.conjNormal (G := Hb) (H := V) g) = f from hf.symm, hf1, MulAut.one_apply]
      rw [MulAut.conjNormal_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hgV : g ∈ V := by
      have := OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting (G := Hb)
      rw [← hVdef] at this
      exact this hg_cent
    obtain ⟨m, hm⟩ := hVp ⟨g, hgV⟩
    have hordV : orderOf (⟨g, hgV⟩ : ↥V) = orderOf g :=
      (orderOf_injective V.subtype (Subgroup.subtype_injective V) ⟨g, hgV⟩).symm
    have hdvd : orderOf g ∣ p ^ m := by
      rw [← hordV]; exact orderOf_dvd_of_pow_eq_one hm
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · have hgone : orderOf g = 1 := by rw [ha, ha0, pow_zero]
      exact Subtype.ext (orderOf_eq_one_iff.mp hgone)
    · exact absurd (ha ▸ dvd_pow_self p hapos.ne') hg_p'
  -- `W` is a `p`-group, hence its image `Ō` is a `p`-group; being also `p'`, `Ō = ⊥`.
  have hWp : IsPGroup p ↥W := isPGroup_of_forall_eq_one_of_not_dvd_orderOf hWp'
  have hO_eq : Ō = W.map (QuotientGroup.mk' Phi) :=
    hWdef ▸ (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Phi) Ō).symm
  have hO_pgroup : IsPGroup p ↥Ō :=
    hO_eq ▸ hWp.of_surjective (MonoidHom.subgroupMap (QuotientGroup.mk' Phi) W)
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Phi) W)
  obtain ⟨k, hk⟩ := hO_pgroup.exists_card_eq
  have hk0 : k = 0 := by by_contra hk0; exact hO_p' (hk ▸ dvd_pow_self p hk0)
  exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])

end OddOrder.BG.Ch1.S03f
