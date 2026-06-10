/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.PLengthTransfer

/-!
# BG §3: standalone preliminaries for Theorem 3.6

Committable, reusable helper lemmas extracted from the Theorem 3.6 development (`S03f_Thm36`).
Kept separate from the (multi-session, `sorry`-bearing) assembly scaffold so that finished pieces
can land on their own.

## Main results

* `fitting_eq_opCore_of_oPiCore_compl_eq_bot`: if `O_{p'}(G) = ⊥` then `F(G) = O_p(G)`.  Used at
  BG Theorem 3.6 (3.9) (`V = F(H) = O_p(H)`).
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
    have hf1 : f = 1 :=
      OddOrder.BG.Ch1.S01.mulAut_eq_one_of_coprime_orderOf_of_frattini hVp f hfcop hftriv
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

section /- transport helpers for the Theorem 3.6 assembly (Phase B–F) -/

open scoped Pointwise

/-- **Push an invariant subgroup of an invariant ambient subgroup back to the whole group**: if
`U ≤ G` is `A`-invariant and `L ≤ ↥U` is invariant under the restricted action, then
`L.map U.subtype ≤ G` is `A`-invariant.

(Public version of a helper that exists `private`ly in `S01_Solvable` and `S04e_GorThm37`;
consolidating the three copies into `Ch03_SplitExtensions` is part of the Theorem 3.6 cleanup.) -/
theorem isAInvariant_map_subtype_of_restrict
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {U : Subgroup G} (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    {L : Subgroup ↥U} (hL : OddOrder.Isaacs.Ch03.IsAInvariant hU.restrict L) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (L.map U.subtype) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  exact ⟨(hU.restrict a) l, hL.smul_mem a hl,
    OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val hU a l⟩

/-- **A subgroup of `H ⊴ G` that is normal in `↥H` and `R`-invariant is normal in `G = HR`**: with
`H ⊔ R = ⊤`, conjugation by any `g = h * r` preserves `X.map H.subtype` (the `r`-part by
`R`-invariance under the conjugation action, the `h`-part by normality in `↥H`).

Used at BG Theorem 3.6 (3.14) for `C_V(K)` and `[V,K]` (normal in `↥H` via (3.12), `R`-invariant
since `V` is characteristic and `K` is `R`-invariant), and again in Phase D. -/
theorem normal_map_subtype_of_isAInvariant_conjNormal
    {G : Type*} [Group G] {H R : Subgroup G} [H.Normal] (hsup : H ⊔ R = ⊤)
    {X : Subgroup ↥H} [hXn : X.Normal]
    (hX_inv : OddOrder.Isaacs.Ch03.IsAInvariant
      ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) X) :
    (X.map H.subtype).Normal := by
  constructor
  rintro _ ⟨x, hx, rfl⟩ g
  -- decompose `g = h * r` with `h ∈ H`, `r ∈ R` (normal product, `H ⊔ R = ⊤`).
  have hg : g ∈ (H : Set G) * (R : Set G) := by
    rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]; trivial
  obtain ⟨h, hh, r, hr, rfl⟩ := hg
  -- conjugate by `r` first (`R`-invariance), then by `h` (normality in `↥H`).
  set y : ↥H := ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) ⟨r, hr⟩ x with hy
  have hyX : y ∈ X := hX_inv.smul_mem ⟨r, hr⟩ hx
  have hyval : (y : G) = r * (x : G) * r⁻¹ := by
    simp only [hy, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hXn.conj_mem y hyX ⟨h, hh⟩, ?_⟩
  rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hyval]
  group

/-- One inequality of `fitting_map_eq_of_mulEquiv`: the image of the Fitting subgroup under an
isomorphism is a normal nilpotent subgroup, hence contained in the Fitting subgroup. -/
theorem fitting_map_le_of_mulEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (f : G ≃* G') :
    (OddOrder.Isaacs.Ch01.fitting G).map f.toMonoidHom ≤ OddOrder.Isaacs.Ch01.fitting G' := by
  haveI : ((OddOrder.Isaacs.Ch01.fitting G).map f.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance f.toMonoidHom f.surjective
  haveI : Group.IsNilpotent ↥((OddOrder.Isaacs.Ch01.fitting G).map f.toMonoidHom) := by
    have e' := Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting G) f.toMonoidHom
      f.injective
    exact nilpotent_of_surjective e'.toMonoidHom e'.surjective
  exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting

/-- **The Fitting subgroup transports along group isomorphisms**: `F(G).map e = F(G')` for
`e : G ≃* G'`.  (The image is a normal nilpotent subgroup, hence `≤ F(G')`; symmetrically with
`e.symm`.)  Used at BG Theorem 3.6 (3.15) (`K = F(N_H(K))` via `N_H(K) ≃* H/V`). -/
theorem fitting_map_eq_of_mulEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') :
    (OddOrder.Isaacs.Ch01.fitting G).map e.toMonoidHom = OddOrder.Isaacs.Ch01.fitting G' := by
  refine le_antisymm (fitting_map_le_of_mulEquiv e) ?_
  have h2 := fitting_map_le_of_mulEquiv e.symm
  rw [Subgroup.map_equiv_eq_comap_symm', MulEquiv.symm_symm] at h2
  have h3 := Subgroup.map_mono (f := e.toMonoidHom) h2
  rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at h3

/-- **Hall subgroups transport along group isomorphisms** (cardinality and index are preserved).
Used in the Frattini argument at BG Theorem 3.6 (3.12): the conjugate of a Hall `p'`-subgroup of
`U` under `MulAut.conjNormal h` is again a Hall `p'`-subgroup. -/
theorem isHallSubgroup_map_of_mulEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {π : Set ℕ} {K : Subgroup G} (e : G ≃* G')
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup π K) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (K.map e.toMonoidHom) := by
  have hcard : Nat.card ↥(K.map e.toMonoidHom) = Nat.card ↥K :=
    Subgroup.card_map_of_injective e.injective
  have hidx : (K.map e.toMonoidHom).index = K.index := by
    have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index (K.map e.toMonoidHom)
    rw [hcard, ← Nat.card_congr e.toEquiv] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
  exact ⟨fun q hq => hK.1 q (hcard ▸ hq), fun q hq => hK.2 q (hidx ▸ hq)⟩

/-- **A group of `p`-length one with `O_{p'}(W) = ⊥` has a normal Sylow `p`-subgroup**: every
`p`-subgroup lies in `O_p(W)`.  (`O_{p',p}(W) = O_p(W)` by
`oPiPrimePiCore_eq_oPiCore_of_compl_bot`, and `W/O_p(W)` is then a `p'`-group, so the image of a
`p`-subgroup is trivial.)  Used at BG Theorem 3.6 (3.22) for `W = [VXP, R₀]`. -/
theorem le_opCore_of_hasPLengthOne_of_oPiCore_compl_eq_bot
    {p : ℕ} [hp : Fact p.Prime] {W : Type*} [Group W] [Finite W]
    (hpl : hasPLengthOne p W)
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) W = ⊥)
    {Q : Subgroup W} (hQ : IsPGroup p ↥Q) :
    Q ≤ OddOrder.Isaacs.Ch01.opCore p W := by
  rw [hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot hOp'] at hpl
  have hQmap : Q.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W)) = ⊥ := by
    have hQp : IsPGroup p
        ↥(Q.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W))) :=
      hQ.map _
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hdvd : Nat.card
        ↥(Q.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W)))
        ∣ Nat.card (W ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W) :=
      Subgroup.card_subgroup_dvd_card _
    have hk0 : k = 0 := by
      by_contra hk0
      exact hpl ((hk ▸ dvd_pow_self p hk0).trans hdvd)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hQmap
  rwa [← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]

end

end OddOrder.BG.Ch1.S03f
