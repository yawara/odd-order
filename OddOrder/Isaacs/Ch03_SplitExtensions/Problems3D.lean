/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.PiParts
import OddOrder.Isaacs.Ch01_Sylow.Problems

/-!
# Isaacs §3D の演習 (書籍 p. 95)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 3D。
§3D は `π`-separable 群と Hall–Higman Lemma 1.2.3 (Thm 3.21) の節。

* **3D.1(a)** `G` が `p`-可解で `O_{p'}(G) = 1` なら `Z(P) ≤ O_p(G)`
  (`center_sylow_le_oPiCore_of_oPiCore_compl_eq_bot`)。
* **3D.2** `Z ≤ Z(G)` なら `O_π(G/Z) = \overline{O_π(G)}`
  (`oPiCore_quotient_central_eq_map`)。
* **3D.5** `G` が `p`-可解で `P ∈ Syl_p(G)` が `K` (位数が `p` で割れない) を正規化するなら
  `K ≤ O_{p'}(G)` (`le_oPiCore_compl_of_sylow_le_normalizer`)。

3D.1(b) (`p`-length ≤ `P` の冪零類) と 3D.3 / 3D.4 は別 leaf。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3D: π-separable + Hall-Higman (pp. 89-95) -/

variable {G : Type*} [Group G]

/-- 正規な `π`-部分群は任意の `π`-Hall 部分群に含まれる形の Sylow 版:
`O_p(G)` は任意の Sylow `p`-部分群に含まれる。 -/
theorem oPiCore_singleton_le_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    oPiCore ({p} : Set ℕ) G ≤ (P : Subgroup G) :=
  Subgroup.IsPiGroup.normal_le_hall (oPiCore.isPiGroup ({p} : Set ℕ))
    (Ch01.sylow_isHallSubgroup_singleton P)

/-- **Isaacs Problem 3D.1(a)** (書籍 p. 95): `G` が `p`-可解 (= `{p}`-separable) で
`O_{p'}(G) = 1` なら, Sylow `p`-部分群 `P` の中心は `O_p(G)` に含まれる。

`O_p(G) ≤ P` なので `Z(P)` は `O_p(G)` を中心化し, Hall–Higman 1.2.3
(`hall_higman_1_2_3`) が `C_G(O_p(G)) ≤ O_p(G)` を与える。 -/
theorem center_sylow_le_oPiCore_of_oPiCore_compl_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    [IsPiSeparable ({p} : Set ℕ) G] (P : Sylow p G)
    (hbot : oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    (P : Subgroup G) ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)
      ≤ oPiCore ({p} : Set ℕ) G := by
  refine le_trans ?_ (hall_higman_1_2_3 ({p} : Set ℕ) hbot)
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  exact Subgroup.mem_centralizer_iff.mp hz.2 o (oPiCore_singleton_le_sylow P ho)

/-- **Isaacs Problem 3D.5** (書籍 p. 95, `O_{p'}(G) = 1` の場合): `G` が `p`-可解で
`O_{p'}(G) = 1`, Sylow `p`-部分群 `P` が `K` を正規化し `p ∤ |K|` なら `K = 1`。

`O_p(G) ≤ P ≤ N_G(K)` と `K ≤ N_G(O_p(G))` から `[K, O_p(G)] ≤ K ⊓ O_p(G) = 1`,
すなわち `K ≤ C_G(O_p(G)) ≤ O_p(G)` (Hall–Higman)。`K` は `p'`-群なので `K = 1`。 -/
theorem eq_bot_of_sylow_le_normalizer_of_oPiCore_compl_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    [IsPiSeparable ({p} : Set ℕ) G] (P : Sylow p G) {K : Subgroup G}
    (hbot : oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥)
    (hPK : (P : Subgroup G) ≤ Subgroup.normalizer (K : Set G))
    (hK : ¬ p ∣ Nat.card ↥K) : K = ⊥ := by
  set O : Subgroup G := oPiCore ({p} : Set ℕ) G with hO
  have hOP : O ≤ (P : Subgroup G) := oPiCore_singleton_le_sylow P
  -- `K ⊓ O = ⊥` (位数が互いに素)
  have hinf : K ⊓ O = ⊥ := by
    refine (Subgroup.eq_bot_iff_card (K ⊓ O)).mpr ?_
    have hdvdK : Nat.card ↥(K ⊓ O) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_left
    have hdvdO : Nat.card ↥(K ⊓ O) ∣ Nat.card ↥O := Subgroup.card_dvd_of_le inf_le_right
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have hqp : q = p := by
      refine oPiCore.isPiGroup (G := G) ({p} : Set ℕ) q ?_
      exact Nat.mem_primeFactors.mpr ⟨hq, hqdvd.trans hdvdO, Nat.card_pos.ne'⟩
    exact hK (hqp ▸ hqdvd.trans hdvdK)
  -- `K` は `O` を中心化する
  have hcent : K ≤ Subgroup.centralizer (O : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    -- `[o, x] ∈ K ⊓ O = ⊥`
    have h1 : o * x * o⁻¹ * x⁻¹ ∈ K := by
      refine mul_mem ?_ (inv_mem hx)
      have := (Subgroup.mem_normalizer_iff.mp (hPK (hOP ho)) x).mp hx
      exact this
    have h2 : o * x * o⁻¹ * x⁻¹ ∈ O := by
      have : x * o⁻¹ * x⁻¹ ∈ O := (oPiCore.normal ({p} : Set ℕ) G).conj_mem o⁻¹ (inv_mem ho) x
      have hmul := mul_mem ho this
      simpa [mul_assoc] using hmul
    have hbot' : o * x * o⁻¹ * x⁻¹ = 1 := by
      have : o * x * o⁻¹ * x⁻¹ ∈ K ⊓ O := Subgroup.mem_inf.mpr ⟨h1, h2⟩
      rwa [hinf, Subgroup.mem_bot] at this
    have hxo : o * x * o⁻¹ = x := mul_inv_eq_one.mp hbot'
    calc o * x = (o * x * o⁻¹) * o := by group
      _ = x * o := by rw [hxo]
  -- Hall–Higman で `K ≤ O`, ゆえに `K ≤ K ⊓ O = ⊥`
  have hKO : K ≤ O := hcent.trans (hall_higman_1_2_3 ({p} : Set ℕ) hbot)
  rw [← hinf]
  exact le_antisymm (le_inf le_rfl hKO) inf_le_left

/-- **Isaacs Problem 3D.5** (書籍 p. 95): `G` が `p`-可解で `P ∈ Syl_p(G)` が
`p ∤ |K|` なる部分群 `K` を正規化するなら `K ≤ O_{p'}(G)`。

`Ḡ := G/O_{p'}(G)` では `O_{p'}(Ḡ) = 1` (`oPiCore_quotient_self_eq_bot`) なので
上の場合が使え, `K̄ = 1` すなわち `K ≤ O_{p'}(G)`。 -/
theorem le_oPiCore_compl_of_sylow_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    [IsPiSeparable ({p} : Set ℕ) G] (P : Sylow p G) {K : Subgroup G}
    (hPK : (P : Subgroup G) ≤ Subgroup.normalizer (K : Set G))
    (hK : ¬ p ∣ Nat.card ↥K) : K ≤ oPiCore {q | q ∉ ({p} : Set ℕ)} G := by
  set N : Subgroup G := oPiCore {q | q ∉ ({p} : Set ℕ)} G with hN
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective N
  -- `Ḡ` の Sylow `p`-部分群としての `P̄`
  obtain ⟨Pbar, hPbar⟩ := Ch01.exists_sylow_coe_eq_of_isHallSubgroup_singleton
    (Ch01.IsHallSubgroup.map_of_surjective hfsurj (Ch01.sylow_isHallSubgroup_singleton P))
  have hKbar : ¬ p ∣ Nat.card ↥(K.map f) := fun hdvd =>
    hK (hdvd.trans (Subgroup.card_map_dvd K f))
  have hPKbar : (Pbar : Subgroup (G ⧸ N)) ≤ Subgroup.normalizer ((K.map f : Subgroup (G ⧸ N)) :
      Set (G ⧸ N)) := by
    rw [hPbar]
    rintro - ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hh
      exact ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hPK hx) k).mp hk, by simp⟩
    · obtain ⟨k, hk, hkh⟩ := hh
      refine ⟨x⁻¹ * k * x, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.mp (hPK hx) (x⁻¹ * k * x)).mpr ?_
        have hxk : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
        rw [hxk]
        exact hk
      · rw [map_mul, map_mul, map_inv, hkh]
        group
  have hbot : K.map f = ⊥ :=
    eq_bot_of_sylow_le_normalizer_of_oPiCore_compl_eq_bot Pbar
      (oPiCore_quotient_self_eq_bot {q | q ∉ ({p} : Set ℕ)}) hPKbar hKbar
  intro x hx
  have : f x = 1 := by
    have : f x ∈ K.map f := ⟨x, hx, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  rwa [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

end -- 3D

end OddOrder.Isaacs.Ch03
