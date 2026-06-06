/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.PLength

/-!
# BG Lemma 1.21 — `p`-length one の移送補題 (foundation)

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994), §1
(mmd `references/bg/local-analysis.mmd` L564)。`hasPLengthOne` の移送補題群 (a)–(e) の土台。

`hasPLengthOne p G := ¬ p ∣ |G / O_{p',p}(G)|`。`O_{p',p}(G)` は定義上
`comap mk' (O_p(G/O_{p'}(G)))` なので、第 3 同型でほどくと `G/O_{p',p}(G) ≅ (G/O_{p'}(G))/O_p(…)`。
この橋 (`card_quotient_oPiPrimePiCore_eq` / `hasPLengthOne_iff_card_quotient`) が Lemma 1.21(a)–(e)
の共通の出発点。下流: BG Thm 3.6 前段還元 (3.8)/(3.9)/(3.11) と Thm 10.6 reduction (1.21(a))。

残: 移送補題 (a) 部分群単調性 / (b) normal `p'` 商 / (c) normal `p` 商 / (d) `⟨p-elts⟩` 特徴づけ /
(e) `H∩N=1` 商。プラン `notes/bg/s03_thm36_plan.md`。
-/

namespace OddOrder.BG.Ch1

open OddOrder.Isaacs

variable {p : ℕ}

/-- **Bridge** (third isomorphism): `|G / O_{p',p}(G)| = |(G/O_{p'}(G)) / O_p(G/O_{p'}(G))|`.
`O_{p',p}(G)` is by definition the preimage of `O_p(G/O_{p'}(G))` under `G → G/O_{p'}(G)`, so the
two quotients are isomorphic. This is the computational form of `hasPLengthOne` used to derive the
Lemma 1.21 transfer lemmas. -/
theorem card_quotient_oPiPrimePiCore_eq (G : Type*) [Group G] [Finite G] :
    Nat.card (G ⧸ Ch03.oPiPrimePiCore ({p} : Set ℕ) G) =
      Nat.card ((G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) ⧸
        Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)) := by
  classical
  set K : Subgroup G := Ch03.oPiCore (({p} : Set ℕ)ᶜ) G with hK
  set q : G →* G ⧸ K := QuotientGroup.mk' K with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hKle : K ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) G :=
    Ch03.oPiCore_compl_le_oPiPrimePiCore ({p} : Set ℕ) G
  -- `(O_{p',p}(G)).map q = O_p(G/K)` since `O_{p',p}(G) = comap q (O_p(G/K))` and `q` surjective.
  have hmap : (Ch03.oPiPrimePiCore ({p} : Set ℕ) G).map q
      = Ch03.oPiCore ({p} : Set ℕ) (G ⧸ K) := by
    rw [hq]
    exact Subgroup.map_comap_eq_self_of_surjective hsurj _
  refine Nat.card_congr ?_
  rw [← hmap]
  exact (QuotientGroup.quotientQuotientEquivQuotient K _ hKle).toEquiv.symm

/-- `hasPLengthOne` rephrased via the bridge: `G` has `p`-length one iff the `p`-core
`O_p(G/O_{p'}(G))` contains a full Sylow `p`-subgroup of `G/O_{p'}(G)` (its quotient is `p'`). -/
theorem hasPLengthOne_iff_card_quotient (G : Type*) [Group G] [Finite G] :
    hasPLengthOne p G ↔
      ¬ p ∣ Nat.card ((G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) ⧸
        Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)) := by
  rw [hasPLengthOne, card_quotient_oPiPrimePiCore_eq G]

/-- The `π`-core commutes with quotient by a normal `π`-subgroup:
`O_π(G/H) = O_π(G) / H` when `H ⊴ G` is a `π`-subgroup. (The reusable engine for the
Lemma 1.21 transfer lemmas: (b) uses `π = {p}ᶜ`, (c) uses `π = {p}`.) -/
theorem oPiCore_quotient_eq_of_isPiGroup {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    {H : Subgroup G} [H.Normal] (hπH : Ch03.Subgroup.IsPiGroup π H) :
    Ch03.oPiCore π (G ⧸ H) = (Ch03.oPiCore π G).map (QuotientGroup.mk' H) := by
  classical
  set q : G →* G ⧸ H := QuotientGroup.mk' H with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective H
  refine le_antisymm ?_ (Ch03.oPiCore.map_le_of_surjective _ q hsurj)
  set Kbar : Subgroup (G ⧸ H) := Ch03.oPiCore π (G ⧸ H) with hKbar
  haveI hKbarN : Kbar.Normal := by rw [hKbar]; infer_instance
  set N : Subgroup G := Kbar.comap q with hN
  haveI hNnormal : N.Normal := by rw [hN]; infer_instance
  have hKbar_pi : Ch03.Subgroup.IsPiGroup π Kbar := by rw [hKbar]; exact Ch03.oPiCore.isPiGroup _
  -- `|N| = |H| · |Kbar|` (the restriction `q : N → Kbar` is onto with kernel `H`).
  have hidx : N.index = Kbar.index := by rw [hN]; exact Subgroup.index_comap_of_surjective Kbar hsurj
  have hKpos : 0 < Kbar.index := Nat.card_pos
  have hcardN : Nat.card N = Nat.card H * Nat.card Kbar := by
    have key : Nat.card N * Kbar.index = (Nat.card H * Nat.card Kbar) * Kbar.index :=
      calc Nat.card N * Kbar.index = Nat.card N * N.index := by rw [hidx]
        _ = Nat.card G := Subgroup.card_mul_index N
        _ = Nat.card H * Nat.card (G ⧸ H) := (Subgroup.card_mul_index H).symm
        _ = Nat.card H * (Nat.card Kbar * Kbar.index) := by
              rw [← Subgroup.card_mul_index Kbar]
        _ = (Nat.card H * Nat.card Kbar) * Kbar.index := by ring
    exact Nat.eq_of_mul_eq_mul_right hKpos key
  -- `N` is a `π`-group: `π(|N|) = π(|H|) ∪ π(|Kbar|) ⊆ π`.
  have hNpi : Ch03.Subgroup.IsPiGroup π N := by
    intro r hr
    rw [hcardN, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hr
    rcases Finset.mem_union.mp hr with h | h
    · exact hπH r h
    · exact hKbar_pi r h
  have hNle : N ≤ Ch03.oPiCore π G := Ch03.Subgroup.IsPiGroup.le_oPiCore hNpi
  have hKN : Kbar = N.map q := (Subgroup.map_comap_eq_self_of_surjective hsurj Kbar).symm
  rw [hKN]; exact Subgroup.map_mono hNle

/-- A normal subgroup with order prime to `p` is a `{p}ᶜ`-group. -/
private theorem isPiGroup_compl_of_not_dvd {G : Type*} [Group G] {H : Subgroup G}
    (hHp' : ¬ p ∣ Nat.card H) : Ch03.Subgroup.IsPiGroup (({p} : Set ℕ)ᶜ) H := by
  intro r hr
  have hrp : r ≠ p := fun h => hHp' (h ▸ Nat.dvd_of_mem_primeFactors hr)
  simpa using hrp

/-- **BG Lemma 1.21(b)** (mmd L567): if `H ⊴ G` is a normal `p'`-subgroup and `G/H` has
`p`-length one, then `G` has `p`-length one. -/
theorem hasPLengthOne_of_isPiPrime_normal_quotient [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} [H.Normal] (hHp' : ¬ p ∣ Nat.card H)
    (hquot : hasPLengthOne p (G ⧸ H)) : hasPLengthOne p G := by
  classical
  rw [hasPLengthOne_iff_card_quotient] at hquot ⊢
  have hHle : H ≤ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G :=
    Ch03.Subgroup.IsPiGroup.le_oPiCore (isPiGroup_compl_of_not_dvd hHp')
  have hcorr : Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)
      = (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H) :=
    oPiCore_quotient_eq_of_isPiGroup _ (isPiGroup_compl_of_not_dvd hHp')
  haveI hmapN : ((Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  -- `φ : (G/H)/O_{p'}(G/H) ≃* G/O_{p'}(G)`.
  have φ : ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)) ≃*
      (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) :=
    (QuotientGroup.quotientMulEquivOfEq hcorr).trans
      (QuotientGroup.quotientQuotientEquivQuotient H _ hHle)
  -- `O_p` commutes with `φ`, so the `O_p`-quotient indices match.
  have hOp : (Ch03.oPiCore ({p} : Set ℕ)
        ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H))).map φ
      = Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) :=
    Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) φ
  have hcard_quot :
      Nat.card ((G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) ⧸
          Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G))
        = Nat.card (((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)) ⧸
          Ch03.oPiCore ({p} : Set ℕ) ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H))) := by
    show (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G)).index
        = (Ch03.oPiCore ({p} : Set ℕ)
            ((G ⧸ H) ⧸ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H))).index
    rw [← hOp]
    exact Subgroup.index_map_equiv _ φ
  rw [hcard_quot]; exact hquot

/-- When `O_{p'}(G) = ⊥`, the `p`-length-one core simplifies: `O_{p',p}(G) = O_p(G)`. -/
theorem oPiPrimePiCore_eq_oPiCore_of_compl_bot {G : Type*} [Group G] [Finite G]
    (h : Ch03.oPiCore (({p} : Set ℕ)ᶜ) G = ⊥) :
    Ch03.oPiPrimePiCore ({p} : Set ℕ) G = Ch03.oPiCore ({p} : Set ℕ) G := by
  have key : ∀ (M : Subgroup G) [M.Normal], M = ⊥ →
      Subgroup.comap (QuotientGroup.mk' M) (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M))
        = Ch03.oPiCore ({p} : Set ℕ) G := by
    intro M _ hM
    subst hM
    rw [show (QuotientGroup.mk' (⊥ : Subgroup G))
        = (QuotientGroup.quotientBot (G := G)).symm.toMonoidHom from rfl]
    rw [Subgroup.comap_equiv_eq_map_symm']
    simp only [MulEquiv.symm_symm]
    exact Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) (QuotientGroup.quotientBot (G := G))
  exact key _ h

/-- A normal `p`-subgroup is a `{p}`-group. -/
private theorem isPiGroup_singleton_of_isPGroup [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hHp : IsPGroup p ↥H) : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := by
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hHp
  have hrdvd : r ∣ p ^ k := hk ▸ Nat.dvd_of_mem_primeFactors hr
  exact (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp (hrp.prime.dvd_of_dvd_pow hrdvd)

/-- **BG Lemma 1.21(c)** (mmd L568): if `H ⊴ G` is a normal `p`-subgroup with `O_{p'}(G/H) = 1`
and `G/H` has `p`-length one, then `G` has `p`-length one. -/
theorem hasPLengthOne_of_isPGroup_normal_quotient [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} [H.Normal] (hHp : IsPGroup p ↥H)
    (hOp' : Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H) = ⊥)
    (hquot : hasPLengthOne p (G ⧸ H)) : hasPLengthOne p G := by
  classical
  -- `O_{p'}(G) ≤ H` (it maps into `O_{p'}(G/H) = ⊥`), and being `≤ H` it is a `p`-group; also
  -- a `{p}ᶜ`-group, hence trivial.
  have hOp'G : Ch03.oPiCore (({p} : Set ℕ)ᶜ) G = ⊥ := by
    have hle : Ch03.oPiCore (({p} : Set ℕ)ᶜ) G ≤ H := by
      have h1 : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H)
          ≤ Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H) :=
        Ch03.oPiCore.map_le_of_surjective _ _ (QuotientGroup.mk'_surjective H)
      rw [hOp', le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
      exact h1
    have hpgroup : IsPGroup p ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) :=
      hHp.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hp_ndvd : ¬ p ∣ Nat.card ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) G) := fun hd =>
      (Ch03.oPiCore.isPiGroup _ p (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))
        (Set.mem_singleton p)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpgroup
    have hk0 : k = 0 := by by_contra hk0; exact hp_ndvd (hk ▸ dvd_pow_self p hk0)
    exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
  -- Reduce both sides to `O_p`-quotients via `O_{p',p} = O_p` (since `O_{p'} = ⊥`).
  rw [hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot hOp'G]
  rw [hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot hOp'] at hquot
  -- `H ≤ O_p(G)` and `O_p(G/H) = O_p(G).map mk'`, so `(G/H)/O_p(G/H) ≃* G/O_p(G)`.
  have hHpi : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := isPiGroup_singleton_of_isPGroup hHp
  have hHleOp : H ≤ Ch03.oPiCore ({p} : Set ℕ) G := Ch03.Subgroup.IsPiGroup.le_oPiCore hHpi
  have hcorr : Ch03.oPiCore ({p} : Set ℕ) (G ⧸ H)
      = (Ch03.oPiCore ({p} : Set ℕ) G).map (QuotientGroup.mk' H) :=
    oPiCore_quotient_eq_of_isPiGroup _ hHpi
  haveI hmapN : ((Ch03.oPiCore ({p} : Set ℕ) G).map (QuotientGroup.mk' H)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  have φ : ((G ⧸ H) ⧸ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ H)) ≃*
      (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) :=
    (QuotientGroup.quotientMulEquivOfEq hcorr).trans
      (QuotientGroup.quotientQuotientEquivQuotient H _ hHleOp)
  rw [(Nat.card_congr φ.toEquiv).symm]
  exact hquot

end OddOrder.BG.Ch1
