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

/-- The `p'`-core commutes with quotient by a normal `p'`-subgroup:
`O_{p'}(G/H) = O_{p'}(G) / H` when `H ⊴ G` is a `p'`-subgroup. -/
theorem oPiCore_compl_quotient_eq [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [H.Normal] (hHp' : ¬ p ∣ Nat.card H) :
    Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)
      = (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H) := by
  classical
  set q : G →* G ⧸ H := QuotientGroup.mk' H with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective H
  refine le_antisymm ?_ (Ch03.oPiCore.map_le_of_surjective _ q hsurj)
  set Kbar : Subgroup (G ⧸ H) := Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H) with hKbar
  haveI hKbarN : Kbar.Normal := by rw [hKbar]; infer_instance
  set N : Subgroup G := Kbar.comap q with hN
  haveI hNnormal : N.Normal := by rw [hN]; infer_instance
  -- `Kbar` is a `p'`-group, so `p ∤ |Kbar|`.
  have hKbar_pi : Ch03.Subgroup.IsPiGroup (({p} : Set ℕ)ᶜ) Kbar := by
    rw [hKbar]; exact Ch03.oPiCore.isPiGroup _
  have hKbar_p' : ¬ p ∣ Nat.card Kbar := fun hd =>
    (hKbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)) (Set.mem_singleton p)
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
  have hNp' : ¬ p ∣ Nat.card N := by
    rw [hcardN]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd with h | h
    · exact hHp' h
    · exact hKbar_p' h
  have hNpi : Ch03.Subgroup.IsPiGroup (({p} : Set ℕ)ᶜ) N := by
    intro r hr
    have hrp : r ≠ p := fun h => hNp' (h ▸ Nat.dvd_of_mem_primeFactors hr)
    simpa using hrp
  have hNle : N ≤ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G := Ch03.Subgroup.IsPiGroup.le_oPiCore hNpi
  have hKN : Kbar = N.map q := (Subgroup.map_comap_eq_self_of_surjective hsurj Kbar).symm
  rw [hKN]; exact Subgroup.map_mono hNle

/-- **BG Lemma 1.21(b)** (mmd L567): if `H ⊴ G` is a normal `p'`-subgroup and `G/H` has
`p`-length one, then `G` has `p`-length one. -/
theorem hasPLengthOne_of_isPiPrime_normal_quotient [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} [H.Normal] (hHp' : ¬ p ∣ Nat.card H)
    (hquot : hasPLengthOne p (G ⧸ H)) : hasPLengthOne p G := by
  classical
  rw [hasPLengthOne_iff_card_quotient] at hquot ⊢
  have hHle : H ≤ Ch03.oPiCore (({p} : Set ℕ)ᶜ) G := by
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
    intro r hr
    have hrp : r ≠ p := fun h => hHp' (h ▸ Nat.dvd_of_mem_primeFactors hr)
    simpa using hrp
  have hcorr : Ch03.oPiCore (({p} : Set ℕ)ᶜ) (G ⧸ H)
      = (Ch03.oPiCore (({p} : Set ℕ)ᶜ) G).map (QuotientGroup.mk' H) :=
    oPiCore_compl_quotient_eq hHp'
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

end OddOrder.BG.Ch1
