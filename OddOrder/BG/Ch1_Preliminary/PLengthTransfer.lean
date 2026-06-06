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

end OddOrder.BG.Ch1
