/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Quasisimple
import OddOrder.Isaacs.Ch02_Subnormality.Basic

/-!
# Isaacs Ch. 9 — §9A: components と Theorem 9.4 (pp. 273-274)

Isaacs, *Finite Group Theory* (AMS GSM 92), §9A 続き:

- `IsComponent`: `G` の **component** = subnormal かつ quasisimple な部分群 (書籍 p. 273).
  transport API: `IsComponent.subgroupOf` (書籍の「含まれる部分群でも component」の remark),
  `IsComponent.map_mk'` (商への転送; Thm 9.4 の帰納で使用).
- **Lemma 9.3** (`commutator_eq_bot_of_isMinimalNormal_of_isComponent`): `N` minimal normal,
  `H` component, `H ⊄ N` ⇒ `⁅N,H⁆ = ⊥`.
- **Theorem 9.4** (`IsComponent.commutator_eq_bot_of_ne`): 相異なる component は可換.

Lemma 9.3 は Thm 2.6 (`Ch02.isMinimalNormal_le_normalizer_of_isSubnormal`) を使うため
`[Finite G]` を要する (Thm 9.4 は `|G|` 帰納法なのでいずれにせよ有限).

## 実装ノート (Thm 9.4 の帰納構造)

`Nat.card G ≤ n` の `n` についての通常帰納法 (型を跨ぐため `∀ G` を内側に量化):

1. `H ⊔ K < ⊤` → `↥(H ⊔ K)` に帰納 (`IsComponent.subgroupOf` で転送, `subtype` で引き戻し).
2. `G` simple → subnormal 非自明部分群は `⊤` のみで `H = K` となり矛盾.
3. minimal normal `N` を取り (`Ch02.exists_isMinimalNormal_le_of_normal`),
   `H ≤ N` / `K ≤ N` は Lemma 9.3 で即決 (`commutator_eq_bot_of_le_isMinimalNormal`).
4. 両方 `⊄ N` で像が異なれば `G/N` に帰納 → `⁅H,K⁆ ≤ N` → Lemma 9.3 + three subgroups
   lemma の rotate + `H` perfect で `⁅H,K⁆ = ⊥` (local `key`).
5. 像が一致すれば `H ⊔ N = K ⊔ N = ⊤` (手順 1 の仮定から) → Thm 2.6 で `H, K ◁ G` →
   `⁅H,K⁆ ≤ H ⊓ K`. `⁅H,K⁆ ≠ ⊥` なら中の minimal normal `M ≤ H ⊓ K` を取り,
   `M` での同じ場合分けが全て矛盾または `key` で閉じる.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped commutatorElement

universe u

variable {G : Type*} [Group G]

section /- 9A: components (p. 273) -/

/-- **Component** (Isaacs p. 273): subnormal かつ quasisimple な部分群. -/
structure IsComponent (H : Subgroup G) : Prop where
  isSubnormal : H.IsSubnormal
  isQuasisimple : IsQuasisimple ↥H

/-- component は nontrivial. -/
theorem IsComponent.ne_bot {H : Subgroup G} (hH : IsComponent H) : H ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot H).mp hH.isQuasisimple.nontrivial

/-- **Isaacs p. 273 remark**: `G` の component は, それを含む任意の部分群の component. -/
theorem IsComponent.subgroupOf {H X : Subgroup G} (hH : IsComponent H) (hle : H ≤ X) :
    IsComponent (H.subgroupOf X) where
  isSubnormal := hH.isSubnormal.subgroupOf
  isQuasisimple :=
    hH.isQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm

/-- component の商への転送: `H ⊄ N` なら `H` の `G/N`-像も component
(subnormal 性は像で保存, quasisimple 性は Lemma 9.2 の商 + 第一同型定理). -/
theorem IsComponent.map_mk' {N H : Subgroup G} [N.Normal]
    (hH : IsComponent H) (hnle : ¬H ≤ N) :
    IsComponent (H.map (QuotientGroup.mk' N)) where
  isSubnormal := hH.isSubnormal.map (QuotientGroup.mk'_surjective N)
  isQuasisimple := by
    have hker : ((QuotientGroup.mk' N).comp H.subtype).ker = N.subgroupOf H := by
      ext x
      simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    have hrange : ((QuotientGroup.mk' N).comp H.subtype).range
        = H.map (QuotientGroup.mk' N) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hq : IsQuasisimple (↥H ⧸ N.subgroupOf H) :=
      hH.isQuasisimple.quotient (Subgroup.Normal.subgroupOf ‹N.Normal› H)
        fun htop => hnle (Subgroup.subgroupOf_eq_top.mp htop)
    exact hq.of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange _)).trans (MulEquiv.subgroupCongr hrange))

end

section /- 9A: Lemma 9.3 と Theorem 9.4 (pp. 273-274) -/

/-- **Isaacs Lemma 9.3**: `N` minimal normal, `H` component with `H ⊄ N` ⇒ `⁅N,H⁆ = ⊥`.

書籍証明そのまま: `H ∩ N` は `H` の proper normal ゆえ Lemma 9.2 で `Z(H)` に入る.
Thm 2.6 で `N` は `H` を正規化するので `⁅N,H⁆ ≤ H ∩ N ≤ Z(H) ≤ C_G(H)`, three subgroups
lemma の rotate と `H = H'` (perfect) で `⁅H,N⁆ = ⁅⁅H,H⁆,N⁆ = ⊥`. -/
theorem commutator_eq_bot_of_isMinimalNormal_of_isComponent [Finite G] {N H : Subgroup G}
    (hN : Ch02.IsMinimalNormal N) (hH : IsComponent H) (hnle : ¬H ≤ N) :
    ⁅N, H⁆ = ⊥ := by
  haveI hNn : N.Normal := hN.1
  have hNle : N ≤ Subgroup.normalizer (H : Set G) :=
    Ch02.isMinimalNormal_le_normalizer_of_isSubnormal hH.isSubnormal hN
  have h1 : ⁅N, H⁆ ≤ H := Subgroup.le_normalizer_iff_commutator_le_right.mp hNle
  have h2 : ⁅N, H⁆ ≤ N := Subgroup.commutator_le_left N H
  -- `⁅N,H⁆ ≤ H ⊓ N ≤ Z(H)` (Lemma 9.2), よって `⁅N,H⁆ ≤ C_G(H)`
  have hcent : ⁅N, H⁆ ≤ Subgroup.centralizer (H : Set G) := by
    intro x hx
    have hxH : x ∈ H := h1 hx
    have hsub : N.subgroupOf H ≤ center ↥H :=
      hH.isQuasisimple.normal_le_center (Subgroup.Normal.subgroupOf hNn H)
        fun htop => hnle (Subgroup.subgroupOf_eq_top.mp htop)
    have hxc : (⟨x, hxH⟩ : ↥H) ∈ center ↥H :=
      hsub (by rw [Subgroup.mem_subgroupOf]; exact h2 hx)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨h, hh⟩)
  -- three subgroups lemma
  have h3 : ⁅⁅N, H⁆, H⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
  have h4 : ⁅⁅H, N⁆, H⁆ = ⊥ := by rw [Subgroup.commutator_comm H N]; exact h3
  have h5 : ⁅⁅H, H⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h4 h3
  haveI := hH.isQuasisimple.isPerfect
  rw [Subgroup.commutator_eq_self] at h5
  rw [Subgroup.commutator_comm N H]
  exact h5

/-- Lemma 9.3 の使い勝手形: `K ≤ N` (minimal normal), `H` component `⊄ N` ⇒ `⁅H,K⁆ = ⊥`. -/
theorem commutator_eq_bot_of_le_isMinimalNormal [Finite G] {N H K : Subgroup G}
    (hN : Ch02.IsMinimalNormal N) (hH : IsComponent H) (hKle : K ≤ N) (hnle : ¬H ≤ N) :
    ⁅H, K⁆ = ⊥ :=
  le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hKle).trans_eq
    ((Subgroup.commutator_comm H N).trans
      (commutator_eq_bot_of_isMinimalNormal_of_isComponent hN hH hnle)))

/-- Theorem 9.4 の帰納核: `Nat.card G ≤ n` の任意の有限群で distinct components は可換. -/
private theorem components_commute_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ {H K : Subgroup G}, IsComponent H → IsComponent K → H ≠ K → ⁅H, K⁆ = ⊥ := by
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro G _ _ hcard H K hH hK hne
    by_cases hsup : H ⊔ K = ⊤
    swap
    · -- Case 1: `X := H ⊔ K` が proper → `↥X` に帰納
      have hXlt : Nat.card ↥(H ⊔ K) < Nat.card G :=
        lt_of_not_ge fun hge => hsup (Subgroup.eq_top_of_le_card _ hge)
      have hne' : H.subgroupOf (H ⊔ K) ≠ K.subgroupOf (H ⊔ K) := fun heq => hne (by
        have h := congrArg (Subgroup.map (H ⊔ K).subtype) heq
        rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr le_sup_left, inf_eq_left.mpr le_sup_right] at h)
      have hres := IH ↥(H ⊔ K) (Nat.le_of_lt_succ (lt_of_lt_of_le hXlt hcard))
        (hH.subgroupOf le_sup_left) (hK.subgroupOf le_sup_right) hne'
      have hmap := congrArg (Subgroup.map (H ⊔ K).subtype) hres
      rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_left,
        inf_eq_left.mpr le_sup_right, Subgroup.map_bot] at hmap
    · by_cases hsimple : IsSimpleGroup G
      · -- Case 2: `G` simple → 非自明 subnormal は `⊤` のみ → `H = K` 矛盾
        exfalso
        rcases hH.isSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple with hb | ht
        · exact hH.ne_bot hb
        rcases hK.isSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple with hb' | ht'
        · exact hK.ne_bot hb'
        exact hne (ht.trans ht'.symm)
      · -- Case 3+: minimal normal `N` を取る
        haveI : Nontrivial G := by
          haveI := hH.isQuasisimple.nontrivial
          obtain ⟨x, hx1⟩ := exists_ne (1 : ↥H)
          exact ⟨(x : G), 1, fun h => hx1 (Subtype.ext h)⟩
        obtain ⟨N₀, hN₀normal, hN₀bot, hN₀top⟩ :
            ∃ N₀ : Subgroup G, N₀.Normal ∧ N₀ ≠ ⊥ ∧ N₀ ≠ ⊤ := by
          by_contra hno
          push Not at hno
          exact hsimple ⟨fun N' hN' => by
            by_cases hb : N' = ⊥
            · exact Or.inl hb
            · exact Or.inr (hno N' hN' hb)⟩
        haveI := hN₀normal
        obtain ⟨N, hNmin, hNle⟩ := Ch02.exists_isMinimalNormal_le_of_normal N₀ hN₀bot
        have hNtop : N ≠ ⊤ := fun h => hN₀top (top_le_iff.mp (h ▸ hNle))
        haveI := hNmin.1
        -- `key`: minimal normal `N'` で両成分の像が異なれば商への帰納 + rotate で閉じる
        have key : ∀ (N' : Subgroup G) [N'.Normal], Ch02.IsMinimalNormal N' → ¬H ≤ N' →
            ¬K ≤ N' → H.map (QuotientGroup.mk' N') ≠ K.map (QuotientGroup.mk' N') →
            ⁅H, K⁆ = ⊥ := by
          intro N' hinst hN' hHle hKle hbar
          have hcardq : Nat.card (G ⧸ N') < Nat.card G := by
            have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
            have h2 : 1 < Nat.card ↥N' := (Subgroup.one_lt_card_iff_ne_bot _).mpr hN'.2.1
            calc Nat.card (G ⧸ N')
                < Nat.card (G ⧸ N') * Nat.card ↥N' :=
                  lt_mul_of_one_lt_right Nat.card_pos h2
              _ = Nat.card G := hmul.symm
          have hbot := IH (G ⧸ N') (Nat.le_of_lt_succ (lt_of_lt_of_le hcardq hcard))
            (hH.map_mk' hHle) (hK.map_mk' hKle) hbar
          have hle : ⁅H, K⁆ ≤ N' := by
            have hmap : (⁅H, K⁆).map (QuotientGroup.mk' N') = ⊥ := by
              rw [Subgroup.map_commutator]; exact hbot
            have h := (Subgroup.map_eq_bot_iff _).mp hmap
            rwa [QuotientGroup.ker_mk'] at h
          have h93 : ⁅N', H⁆ = ⊥ :=
            commutator_eq_bot_of_isMinimalNormal_of_isComponent hN' hH hHle
          have h1 : ⁅⁅H, K⁆, H⁆ = ⊥ :=
            le_bot_iff.mp ((Subgroup.commutator_mono hle le_rfl).trans_eq h93)
          have h2 : ⁅⁅K, H⁆, H⁆ = ⊥ := by rw [Subgroup.commutator_comm K H]; exact h1
          have h5 : ⁅⁅H, H⁆, K⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
          haveI := hH.isQuasisimple.isPerfect
          rwa [Subgroup.commutator_eq_self] at h5
        by_cases hHN : H ≤ N
        · by_cases hKN : K ≤ N
          · exact absurd (top_le_iff.mp (hsup ▸ sup_le hHN hKN)) hNtop
          · rw [Subgroup.commutator_comm]
            exact commutator_eq_bot_of_le_isMinimalNormal hNmin hK hHN hKN
        · by_cases hKN : K ≤ N
          · exact commutator_eq_bot_of_le_isMinimalNormal hNmin hH hKN hHN
          · by_cases hbar : H.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N)
            swap
            · exact key N hNmin hHN hKN hbar
            · -- Case 5: `H ⊔ N = K ⊔ N = ⊤` → `H, K ◁ G` → minimal `M ≤ ⁅H,K⁆` で場合分け
              have hHN_sup : H ⊔ N = K ⊔ N := by
                have h := congrArg (Subgroup.comap (QuotientGroup.mk' N)) hbar
                rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq,
                  QuotientGroup.ker_mk'] at h
              have hKle' : K ≤ H ⊔ N := by rw [hHN_sup]; exact le_sup_left
              have hHNtop : H ⊔ N = ⊤ :=
                top_le_iff.mp (by rw [← hsup]; exact sup_le le_sup_left hKle')
              have hKNtop : K ⊔ N = ⊤ := hHN_sup ▸ hHNtop
              have hHnormal : H.Normal := by
                rw [← Subgroup.normalizer_eq_top_iff]
                refine top_le_iff.mp ?_
                rw [← hHNtop]
                exact sup_le Subgroup.le_normalizer
                  (Ch02.isMinimalNormal_le_normalizer_of_isSubnormal hH.isSubnormal hNmin)
              have hKnormal : K.Normal := by
                rw [← Subgroup.normalizer_eq_top_iff]
                refine top_le_iff.mp ?_
                rw [← hKNtop]
                exact sup_le Subgroup.le_normalizer
                  (Ch02.isMinimalNormal_le_normalizer_of_isSubnormal hK.isSubnormal hNmin)
              haveI := hHnormal
              haveI := hKnormal
              have hHK : ⁅H, K⁆ ≤ H ⊓ K :=
                le_inf (Subgroup.commutator_le_left H K) (Subgroup.commutator_le_right H K)
              by_cases hcomm : ⁅H, K⁆ = ⊥
              · exact hcomm
              · haveI : (⁅H, K⁆).Normal := Subgroup.commutator_normal H K
                obtain ⟨M, hMmin, hMle⟩ :=
                  Ch02.exists_isMinimalNormal_le_of_normal ⁅H, K⁆ hcomm
                haveI := hMmin.1
                have hMH : M ≤ H := hMle.trans (hHK.trans inf_le_left)
                have hMK : M ≤ K := hMle.trans (hHK.trans inf_le_right)
                have hMtop : M ≠ ⊤ := fun h =>
                  hne ((top_le_iff.mp (h ▸ hMH)).trans (top_le_iff.mp (h ▸ hMK)).symm)
                by_cases hHM : H ≤ M
                · -- `H = M ≤ K`; `K ⊄ M` (さもなくば `⊤ = H ⊔ K ≤ M`)
                  have hKM : ¬K ≤ M := fun hkm =>
                    hMtop (top_le_iff.mp (by rw [← hsup]; exact sup_le hHM hkm))
                  have h93 := commutator_eq_bot_of_isMinimalNormal_of_isComponent hMmin hK hKM
                  rw [le_antisymm hHM hMH]
                  exact h93
                · by_cases hKM : K ≤ M
                  · -- `K = M`, `H ⊄ M`
                    have h93 :=
                      commutator_eq_bot_of_isMinimalNormal_of_isComponent hMmin hH hHM
                    rw [le_antisymm hKM hMK, Subgroup.commutator_comm]
                    exact h93
                  · by_cases hbarM :
                        H.map (QuotientGroup.mk' M) = K.map (QuotientGroup.mk' M)
                    · -- 像一致 → `H ⊔ M = K ⊔ M` かつ `M ≤ H ⊓ K` → `H = K` 矛盾
                      exfalso
                      have hsupM : H ⊔ M = K ⊔ M := by
                        have h := congrArg (Subgroup.comap (QuotientGroup.mk' M)) hbarM
                        rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq,
                          QuotientGroup.ker_mk'] at h
                      rw [sup_eq_left.mpr hMH, sup_eq_left.mpr hMK] at hsupM
                      exact hne hsupM
                    · exact key M hMmin hHM hKM hbarM

/-- **Isaacs Theorem 9.4**: 有限群の相異なる component は可換 (`⁅H,K⁆ = ⊥`). -/
theorem IsComponent.commutator_eq_bot_of_ne {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (hH : IsComponent H) (hK : IsComponent K) (hne : H ≠ K) :
    ⁅H, K⁆ = ⊥ :=
  components_commute_aux (Nat.card G) G le_rfl hH hK hne

end

end OddOrder.Isaacs.Ch09
