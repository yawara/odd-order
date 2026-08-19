/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.PiParts
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch03_SplitExtensions.PiLength

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

open _root_.OddOrder.Isaacs.Ch03.Subgroup Pointwise

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

/-- 中心に含まれる部分群は正規。 -/
theorem normal_of_le_center {A : Subgroup G} (hA : A ≤ Subgroup.center G) : A.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc : g * n = n * g := Subgroup.mem_center_iff.mp (hA hn) g
  have heq : g * n * g⁻¹ = n := by rw [hc]; group
  rw [heq]
  exact hn

/-- `A ≤ K` のとき `|A| · [K : A] = |K|`。 -/
theorem card_mul_relIndex [Finite G] {A K : Subgroup G} (hAK : A ≤ K) :
    Nat.card ↥A * A.relIndex K = Nat.card ↥K := by
  have h := Subgroup.card_mul_index (A.subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv] at h

/-- **Isaacs Problem 3D.2** (書籍 p. 95): `Z ≤ Z(G)` なら `O_π(G/Z) = \overline{O_π(G)}`
(bar は `G/Z` への像)。

`⊇` は像が正規 `π`-部分群であること。`⊆` は `K := O_π(G/Z)` の引き戻しについて,
`Z` の `π'`-部分 `Z_{π'}` (`Z` は可換ゆえ冪零) が `K` の**中心的な**正規 Hall `π'`-部分群に
なるので Schur–Zassenhaus で補元 `H` が取れ, `H` は `K` の唯一の Hall `π`-部分群ゆえ
`G`-正規, したがって `H ≤ O_π(G)` かつ `K = Z_{π'} H ≤ Z · O_π(G)`。 -/
theorem oPiCore_quotient_center_eq_map [Finite G] {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (π : Set ℕ) :
    oPiCore π (G ⧸ Z) = (oPiCore π G).map (QuotientGroup.mk' Z) := by
  classical
  have hZnil : Group.IsNilpotent ↥Z := by
    refine ⟨⟨1, ?_⟩⟩
    rw [Subgroup.upperCentralSeries_one, eq_top_iff]
    intro a _
    refine Subgroup.mem_center_iff.mpr fun b => ?_
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZ b.2) a).symm
  have hfsurj : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  refine le_antisymm ?_ ?_
  swap
  · have : ((oPiCore π G).map (QuotientGroup.mk' Z)).Normal :=
      (oPiCore.normal π G).map _ hfsurj
    exact Subgroup.IsPiGroup.le_oPiCore (Subgroup.IsPiGroup.map_quotient (oPiCore.isPiGroup π))
  -- `K` = `O_π(G/Z)` の引き戻し
  set Q : Subgroup (G ⧸ Z) := oPiCore π (G ⧸ Z) with hQ
  set K : Subgroup G := Q.comap (QuotientGroup.mk' Z) with hKdef
  have hZK : Z ≤ K := by
    have h := Subgroup.ker_le_comap (QuotientGroup.mk' Z) Q
    rwa [QuotientGroup.ker_mk'] at h
  have hKnormal : K.Normal := (oPiCore.normal π (G ⧸ Z)).comap _
  have hKmap : K.map (QuotientGroup.mk' Z) = Q :=
    Subgroup.map_comap_eq_self_of_surjective hfsurj _
  -- `|K| = |Z| · |Q|`
  have hcardK : Nat.card ↥K = Nat.card ↥Z * Nat.card ↥Q := by
    have h1 : K.index = Q.index := Q.index_comap_of_surjective hfsurj
    refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := Q))) ?_
    calc Nat.card ↥K * Q.index
        = Nat.card ↥K * K.index := by rw [h1]
      _ = Nat.card G := Subgroup.card_mul_index K
      _ = Nat.card (G ⧸ Z) * Nat.card ↥Z := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      _ = Nat.card ↥Q * Q.index * Nat.card ↥Z := by rw [Subgroup.card_mul_index]
      _ = Nat.card ↥Z * Nat.card ↥Q * Q.index := by ring
  -- `Z` の `π`/`π'`-部分
  have hZp := isHallPart_nilPiPart (N := Z) π hZnil
  have hZc := isHallPart_nilPiPart (N := Z) (πᶜ) hZnil
  have hZcN : (nilPiPart Z πᶜ).Normal := normal_of_le_center (hZc.1.trans hZ)
  have hinfZ : nilPiPart Z π ⊓ nilPiPart Z πᶜ = ⊥ := by
    refine (Subgroup.eq_bot_iff_card _).mpr ?_
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : q ∈ π := hZp.isPiGroup q (Nat.mem_primeFactors.mpr
      ⟨hq, hqdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    have h2 : q ∈ πᶜ := hZc.isPiGroup q (Nat.mem_primeFactors.mpr
      ⟨hq, hqdvd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
    exact h2 h1
  have hcardZ : Nat.card ↥(nilPiPart Z π) * Nat.card ↥(nilPiPart Z πᶜ) = Nat.card ↥Z := by
    have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card (nilPiPart Z π) (nilPiPart Z πᶜ)
    rw [hinfZ, ← Subgroup.mul_normal (nilPiPart Z π) (nilPiPart Z πᶜ),
      IsHallPart.sup_eq hZp hZc] at h
    simpa using h.symm
  -- `[K : Z_{π'}] = |Z_π| · |Q|` は `π`-数
  have hZcK : nilPiPart Z πᶜ ≤ K := hZc.1.trans hZK
  have hrelval : (nilPiPart Z πᶜ).relIndex K = Nat.card ↥(nilPiPart Z π) * Nat.card ↥Q := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(nilPiPart Z πᶜ))) ?_
    rw [card_mul_relIndex hZcK, hcardK, ← hcardZ]
    ring
  have hrelpi : ∀ q ∈ ((nilPiPart Z πᶜ).relIndex K).primeFactors, q ∈ π := by
    intro q hq
    rw [hrelval, Nat.mem_primeFactors] at hq
    rcases hq.1.dvd_mul.mp hq.2.1 with h | h
    · exact hZp.isPiGroup q (Nat.mem_primeFactors.mpr ⟨hq.1, h, Nat.card_pos.ne'⟩)
    · exact oPiCore.isPiGroup (G := G ⧸ Z) π q (Nat.mem_primeFactors.mpr
        ⟨hq.1, h, Nat.card_pos.ne'⟩)
  -- Schur–Zassenhaus
  have : ((nilPiPart Z πᶜ).subgroupOf K).Normal := Subgroup.normal_subgroupOf
  have hcard_sub : Nat.card ↥((nilPiPart Z πᶜ).subgroupOf K) = Nat.card ↥(nilPiPart Z πᶜ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZcK).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥((nilPiPart Z πᶜ).subgroupOf K))
      ((nilPiPart Z πᶜ).subgroupOf K).index := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hqdvd
    refine hZc.isPiGroup q (Nat.mem_primeFactors.mpr
      ⟨hq, hcard_sub ▸ hqdvd.1, Nat.card_pos.ne'⟩) ?_
    exact hrelpi q (Nat.mem_primeFactors.mpr ⟨hq, hqdvd.2, Subgroup.index_ne_zero_of_finite⟩)
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  -- `H := H'` を `G` に落とす
  have hHK : H'.map K.subtype ≤ K := Subgroup.map_subtype_le H'
  have hHsub : (H'.map K.subtype).subgroupOf K = H' :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective H'
  have hcardH : Nat.card ↥(H'.map K.subtype) = (nilPiPart Z πᶜ).relIndex K := by
    have hmul := hH'.card_mul_card
    have hcH : Nat.card ↥(H'.map K.subtype) = Nat.card ↥H' :=
      Subgroup.card_map_of_injective K.subtype_injective
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(nilPiPart Z πᶜ))) ?_
    rw [hcH, card_mul_relIndex hZcK, ← hcard_sub]
    exact hmul
  -- `H` は `K` の Hall `π`-部分
  have hHall : IsHallPart K (H'.map K.subtype) π := by
    refine ⟨hHK, ?_, ?_⟩
    · intro q hq
      refine hrelpi q ?_
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hcardH] at hq
    · intro q hq hqpi
      -- `[K : H] = |Z_{π'}|` は `π'`-数
      have hidxH : (H'.map K.subtype).relIndex K = Nat.card ↥(nilPiPart Z πᶜ) := by
        refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(H'.map K.subtype))) ?_
        rw [card_mul_relIndex hHK, hcardH, ← card_mul_relIndex hZcK]
        ring
      refine hZc.isPiGroup q ?_ hqpi
      rw [← hidxH]
      exact hq
  -- `K = Z_{π'} ⊔ H`
  have hsupK : nilPiPart Z πᶜ ⊔ H'.map K.subtype = K := by
    have htop := hH'.sup_eq_top
    have := congrArg (Subgroup.map K.subtype) htop
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZcK,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  -- `H` は `G` に正規
  have hHnormK : K ≤ Subgroup.normalizer ((H'.map K.subtype : Subgroup G) : Set G) := by
    have h1 : nilPiPart Z πᶜ ≤ Subgroup.normalizer ((H'.map K.subtype : Subgroup G) : Set G) :=
      fun z hz => Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun h _ =>
          Subgroup.mem_center_iff.mp (hZ (hZc.1 hz)) h)
    have h2 : nilPiPart Z πᶜ ⊔ H'.map K.subtype
        ≤ Subgroup.normalizer ((H'.map K.subtype : Subgroup G) : Set G) :=
      sup_le h1 Subgroup.le_normalizer
    exact hsupK.symm.le.trans h2
  have hHnormal : (H'.map K.subtype).Normal := by
    refine Subgroup.normal_iff_map_conj_eq.mpr fun g => ?_
    have hconjK : (H'.map K.subtype).map (MulAut.conj g).toMonoidHom ≤ K := by
      have hKconj : K.map (MulAut.conj g).toMonoidHom = K :=
        Subgroup.Normal.map_conj_eq K g
      have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hHK
      rwa [hKconj] at this
    have hcardc : Nat.card ↥((H'.map K.subtype).map (MulAut.conj g).toMonoidHom : Subgroup G)
        = Nat.card ↥(H'.map K.subtype) := by
      apply Subgroup.card_map_of_injective
      exact (MulAut.conj g).injective
    have hle : (H'.map K.subtype).map (MulAut.conj g).toMonoidHom ≤ H'.map K.subtype := by
      have hsub : ((H'.map K.subtype).map (MulAut.conj g).toMonoidHom).subgroupOf K
          ≤ (H'.map K.subtype).subgroupOf K := by
        refine isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer hHall.2 ?_ ?_
        · intro r hr
          refine hHall.isPiGroup r ?_
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconjK).toEquiv, hcardc] at hr
        · rw [← Subgroup.subgroupOf_normalizer_eq hHK]
          intro z hz
          exact Subgroup.mem_subgroupOf.mpr (hHnormK (hconjK hz))
      intro z hz
      exact (Subgroup.mem_subgroupOf (H := H'.map K.subtype) (K := K)
        (h := ⟨z, hconjK hz⟩)).mp (hsub (Subgroup.mem_subgroupOf.mpr hz))
    exact Subgroup.eq_of_le_of_card_ge hle hcardc.ge
  -- 仕上げ
  have hHcore : H'.map K.subtype ≤ oPiCore π G :=
    Subgroup.IsPiGroup.le_oPiCore hHall.isPiGroup
  have hKle : K ≤ Z ⊔ oPiCore π G := by
    rw [← hsupK]
    exact sup_le (hZc.1.trans le_sup_left) (hHcore.trans le_sup_right)
  rw [← hKmap]
  refine le_trans (Subgroup.map_mono hKle) ?_
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

/-- **Isaacs Problem 3D.3** (書籍 p. 95): `G` が `π`-separable で
`O_π(G) O_{π'}(G) ≤ Z(G)` なら `G` は可換。

`N := O_{π'}(G)` で割ると `O_{π'}(Ḡ) = 1` なので Hall–Higman 1.2.3 が使え,
3D.2 (`oPiCore_quotient_center_eq_map`) より `O_π(Ḡ)` は `O_π(G)` の像。
`O_π(G) ≤ Z(G)` なのでこの像は `Ḡ` の全体に中心化され, したがって `O_π(Ḡ) = ⊤`,
すなわち `O_π(G) ⊔ N = ⊤ ≤ Z(G)`。 -/
theorem center_eq_top_of_oPiCore_sup_le_center [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    (h : oPiCore π G ⊔ oPiCore {p | p ∉ π} G ≤ Subgroup.center G) :
    Subgroup.center G = ⊤ := by
  set N : Subgroup G := oPiCore {p | p ∉ π} G with hNdef
  have hNZ : N ≤ Subgroup.center G := le_sup_right.trans h
  have hpiZ : oPiCore π G ≤ Subgroup.center G := le_sup_left.trans h
  have h32 : oPiCore π (G ⧸ N) = (oPiCore π G).map (QuotientGroup.mk' N) :=
    oPiCore_quotient_center_eq_map hNZ π
  -- `O_π(Ḡ)` は `Ḡ` 全体に中心化される
  have hcent : (⊤ : Subgroup (G ⧸ N))
      ≤ Subgroup.centralizer ((oPiCore π (G ⧸ N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    intro x _
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [h32] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hcomm : g * a = a * g := Subgroup.mem_center_iff.mp (hpiZ ha) g
    rw [← map_mul, ← map_mul, hcomm]
  have htop : oPiCore π (G ⧸ N) = ⊤ :=
    le_antisymm le_top (hcent.trans (hall_higman_1_2_3 π (oPiCore_quotient_self_eq_bot _)))
  -- 引き戻して `O_π(G) ⊔ N = ⊤`
  have hsup : oPiCore π G ⊔ N = ⊤ := by
    have hpull := congrArg (Subgroup.comap (QuotientGroup.mk' N)) (h32.symm.trans htop)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hpull
  refine le_antisymm le_top ?_
  rw [← hsup]
  exact h

/-! ### Problem 3D.4 — `Φ(G)` 上自明な互いに素な作用は自明 -/

/-- 作用の核 (すべての `g` を固定する `h` の集合)。 -/
def actionKernel (H G : Type*) [Group H] [Group G] [MulDistribMulAction H G] : Subgroup H where
  carrier := {h : H | ∀ g : G, h • g = g}
  one_mem' := fun g => one_smul H g
  mul_mem' := fun {a b} ha hb g => by rw [mul_smul, hb g, ha g]
  inv_mem' := fun {a} ha g => by
    have h1 : a • (a⁻¹ • g) = g := by rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [← ha (a⁻¹ • g), h1]

/-- 特性部分群は作用で不変。 -/
theorem smul_mem_of_characteristic {H G : Type*} [Group H] [Group G] [MulDistribMulAction H G]
    (N : Subgroup G) [N.Characteristic] (x : H) {z : G} (hz : z ∈ N) : x • z ∈ N := by
  have hchar := Subgroup.characteristic_iff_comap_eq.mp
    (inferInstance : N.Characteristic) (MulDistribMulAction.toMulAut H G x)
  have : z ∈ N.comap (MulDistribMulAction.toMulAut H G x).toMonoidHom := by rw [hchar]; exact hz
  exact this

/-- **Isaacs Problem 3D.4** (`q`-群の場合): `Q` が `q`-群として `G` に自己同型で作用し,
`q ∤ |Φ(G)|` で `G/Φ(G)` 上の作用が自明なら, `G` 上の作用も自明。

`Φ(G)` の各剰余類 `gΦ` は `Q`-不変で位数 `|Φ|` は `q` で割れないから,
`IsPGroup.card_modEq_card_fixedPoints` より `gΦ` に `Q`-不動点がある。ゆえに固定部分群 `C` は
`C ⊔ Φ(G) = ⊤` を満たし, `Φ(G)` の非生成性 (`frattini_nongenerating`) から `C = ⊤`。 -/
theorem smul_eq_self_of_isPGroup_of_trivial_mod_frattini {G Q : Type*} [Group G] [Finite G]
    [Group Q] [Finite Q] [MulDistribMulAction Q G] {q : ℕ} [Fact q.Prime]
    (hQ : IsPGroup q Q) (hq : ¬ q ∣ Nat.card ↥(frattini G))
    (htriv : ∀ (x : Q) (g : G), g⁻¹ * (x • g) ∈ frattini G) :
    ∀ (x : Q) (g : G), x • g = g := by
  classical
  have hinv : ∀ (x : Q) (z : G), z ∈ frattini G → x • z ∈ frattini G := fun x z hz =>
    smul_mem_of_characteristic (frattini G) x hz
  set C : Subgroup G :=
    { carrier := {g : G | ∀ x : Q, x • g = g}
      one_mem' := fun x => smul_one x
      mul_mem' := fun {a b} ha hb x => by rw [smul_mul', ha x, hb x]
      inv_mem' := fun {a} ha x => by rw [smul_inv', ha x] } with hCdef
  -- 各剰余類に不動点がある
  have hcoset : ∀ g : G, ∃ c : G, (∀ x : Q, x • c = c) ∧ c⁻¹ * g ∈ frattini G := by
    intro g
    set X : Set G := {y : G | g⁻¹ * y ∈ frattini G} with hXdef
    let : MulAction Q ↥X :=
      { smul := fun x y => ⟨x • (y : G), by
          have h1 : g⁻¹ * (x • (y : G)) = (g⁻¹ * (x • g)) * (x • (g⁻¹ * (y : G))) := by
            rw [smul_mul', smul_inv']
            group
          change g⁻¹ * (x • (y : G)) ∈ frattini G
          rw [h1]
          exact mul_mem (htriv x g) (hinv x _ y.2)⟩
        one_smul := fun y => Subtype.ext (one_smul Q (y : G))
        mul_smul := fun x₁ x₂ y => Subtype.ext (mul_smul x₁ x₂ (y : G)) }
    have hcardX : Nat.card ↥X = Nat.card ↥(frattini G) := by
      refine Nat.card_congr ⟨fun y => ⟨g⁻¹ * (y : G), y.2⟩, fun z => ⟨g * (z : G), ?_⟩, ?_, ?_⟩
      · change g⁻¹ * (g * (z : G)) ∈ frattini G
        rw [← mul_assoc, inv_mul_cancel, one_mul]
        exact z.2
      · intro y; exact Subtype.ext (by simp)
      · intro z; exact Subtype.ext (by simp)
    have hmod := hQ.card_modEq_card_fixedPoints (α := ↥X)
    have hne : Nat.card (MulAction.fixedPoints Q ↥X) ≠ 0 := by
      intro h0
      refine hq ?_
      rw [← hcardX]
      have : Nat.card ↥X ≡ 0 [MOD q] := by rw [← h0]; exact hmod
      exact (Nat.modEq_zero_iff_dvd).mp this
    obtain ⟨c⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
    refine ⟨((c : ↥X) : G), fun x => ?_, ?_⟩
    · exact congrArg (Subtype.val : ↥X → G) (c.2 x)
    · have hmem : g⁻¹ * ((c : ↥X) : G) ∈ frattini G := (c : ↥X).2
      simpa using inv_mem hmem
  -- `C ⊔ Φ(G) = ⊤`
  have hsup : C ⊔ frattini G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨c, hcfix, hcg⟩ := hcoset g
    have h1 : c ∈ C := hcfix
    have h2 : g = c * (c⁻¹ * g) := by group
    rw [h2]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hcg)
  have hCtop : C = ⊤ := frattini_nongenerating hsup
  intro x g
  have : g ∈ C := by rw [hCtop]; trivial
  exact this x

/-- **Isaacs Problem 3D.4** (書籍 p. 95): `H` が `G` に自己同型で作用し, `|H|` と `|Φ(G)|` が
互いに素で `G/Φ(G)` 上の作用が自明なら, `G` 上の作用も自明。

書籍 Hint どおり `H` の各 Sylow `q`-部分群に `q`-群の場合を適用する。すべての Sylow が
作用の核に入るので, 核の指数はどの素数でも割れず `1`。 -/
theorem smul_eq_self_of_trivial_mod_frattini {G H : Type*} [Group G] [Finite G] [Group H]
    [Finite H] [MulDistribMulAction H G]
    (hcop : Nat.Coprime (Nat.card H) (Nat.card ↥(frattini G)))
    (htriv : ∀ (h : H) (g : G), g⁻¹ * (h • g) ∈ frattini G) :
    ∀ (h : H) (g : G), h • g = g := by
  classical
  set K : Subgroup H := actionKernel H G with hKdef
  have hKtop : K = ⊤ := by
    rw [← Subgroup.index_eq_one]
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have : Fact q.Prime := ⟨hq⟩
    have hqH : q ∣ Nat.card H := hqdvd.trans (Subgroup.index_dvd_card K)
    obtain ⟨S⟩ : Nonempty (Sylow q H) := inferInstance
    -- `S` は作用の核に入る
    have hSK : (S : Subgroup H) ≤ K := by
      let : MulDistribMulAction ↥(S : Subgroup H) G :=
        MulDistribMulAction.compHom G (S : Subgroup H).subtype
      have hqPhi : ¬ q ∣ Nat.card ↥(frattini G) := fun hdvd =>
        Nat.Prime.one_lt hq |>.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hqH hdvd))
      have := smul_eq_self_of_isPGroup_of_trivial_mod_frattini (Q := ↥(S : Subgroup H))
        S.isPGroup' hqPhi (fun x g => htriv (x : H) g)
      intro s hs
      exact fun g => this ⟨s, hs⟩ g
    -- 位数の矛盾
    have hcardS : Nat.card ↥(S : Subgroup H) = q ^ (Nat.card H).factorization q :=
      S.card_eq_multiplicity
    have h1 : q ^ ((Nat.card H).factorization q + 1) ∣ Nat.card H := by
      have hSdvd : q ^ (Nat.card H).factorization q ∣ Nat.card ↥K :=
        hcardS ▸ Subgroup.card_dvd_of_le hSK
      have hmul : Nat.card ↥K * K.index = Nat.card H := Subgroup.card_mul_index K
      calc q ^ ((Nat.card H).factorization q + 1)
          = q ^ (Nat.card H).factorization q * q := pow_succ q _
        _ ∣ Nat.card ↥K * K.index := Nat.mul_dvd_mul hSdvd hqdvd
        _ = Nat.card H := hmul
    have := (Nat.Prime.pow_dvd_iff_le_factorization hq (Nat.card_pos (α := H)).ne').mp h1
    omega
  intro h g
  have : h ∈ K := by rw [hKtop]; trivial
  exact this g

/-! ### Problem 3D.1(b) — `p`-length ≤ Sylow `p`-部分群の冪零類 -/

/-- **3D.1(b) の要**: `Z(P) ≤ O_{p',p}(G)`。

`N := O_{p'}(G)` で割ると `z ∈ Z(P)` の像は `P̄ = PN/N` を中心化し (`[z̄, x̄] = 1`),
かつ `z̄ ∈ P̄` なので `z̄ ∈ Z(P̄) ≤ O_p(Ḡ)` (3D.1(a))。ゆえに `z ∈ O_{p',p}(G)`。
`P ≅ P̄` の同型を作る必要はない。 -/
theorem center_sylow_le_oPiPrimePiCore [Finite G] {p : ℕ} [Fact p.Prime]
    [IsPiSeparable ({p} : Set ℕ) G] (P : Sylow p G) :
    (P : Subgroup G) ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)
      ≤ oPiPrimePiCore ({p} : Set ℕ) G := by
  set N : Subgroup G := oPiCore {q | q ∉ ({p} : Set ℕ)} G with hN
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  obtain ⟨Pbar, hPbar⟩ := Ch01.exists_sylow_coe_eq_of_isHallSubgroup_singleton
    (Ch01.IsHallSubgroup.map_of_surjective hsurj (Ch01.sylow_isHallSubgroup_singleton P))
  intro z hz
  have hmem : (QuotientGroup.mk' N) z ∈ (Pbar : Subgroup (G ⧸ N))
      ⊓ Subgroup.centralizer ((Pbar : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hPbar]
      exact ⟨z, hz.1, rfl⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [hPbar] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hz.2 x hx]
  exact center_sylow_le_oPiCore_of_oPiCore_compl_eq_bot (G := G ⧸ N) Pbar
    (oPiCore_quotient_self_eq_bot _) hmem

universe u

/-- 3D.1(b) の帰納本体 (`P` の冪零類に関する帰納)。 -/
private theorem hasPiLengthLE_nilpotencyClass_aux :
    ∀ (c : ℕ) {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
      [IsPiSeparable ({p} : Set ℕ) G] (P : Sylow p G),
      Group.nilpotencyClass ↥(P : Subgroup G) ≤ c → HasPiLengthLE ({p} : Set ℕ) G c := by
  intro c
  induction c with
  | zero =>
    intro G _ _ p _ _ P hc
    have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
    have : Subsingleton ↥(P : Subgroup G) :=
      Group.nilpotencyClass_zero_iff_subsingleton.mp (Nat.le_zero.mp hc)
    have hcard : Nat.card ↥(P : Subgroup G) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have hmult := P.card_eq_multiplicity
    rw [hcard] at hmult
    have hfac : (Nat.card G).factorization p = 0 :=
      (Nat.pow_eq_one.mp hmult.symm).resolve_left (Nat.Prime.ne_one Fact.out)
    have hnd : ¬ p ∣ Nat.card G := by
      intro hdvd
      have hpos := Nat.Prime.factorization_pos_of_dvd Fact.out
        (Nat.card_pos (α := G)).ne' hdvd
      omega
    refine hasPiLengthLE_zero_of_isPiGroup (fun r hr hrp => ?_)
    exact hnd (hrp ▸ (Nat.mem_primeFactors.mp hr).2.1)
  | succ n ih =>
    intro G _ _ p _ _ P hc
    have hPnil : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
    set M : Subgroup G := oPiPrimePiCore ({p} : Set ℕ) G with hM
    have hsurjM : Function.Surjective (QuotientGroup.mk' M) := QuotientGroup.mk'_surjective M
    obtain ⟨Q, hQ⟩ := Ch01.exists_sylow_coe_eq_of_isHallSubgroup_singleton
      (Ch01.IsHallSubgroup.map_of_surjective hsurjM (Ch01.sylow_isHallSubgroup_singleton P))
    -- `Z(↥P)` は `↥P → ↥(P.map (mk' M))` の核に入る
    have hZM := center_sylow_le_oPiPrimePiCore (G := G) P
    have hker : ∀ x ∈ Subgroup.center ↥(P : Subgroup G),
        ((QuotientGroup.mk' M).subgroupMap (P : Subgroup G)) x = 1 := by
      intro x hx
      have hxM : (x : G) ∈ M := by
        refine hZM (Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩)
        exact congrArg (Subtype.val : ↥(P : Subgroup G) → G)
          (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
      refine Subtype.ext ?_
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hxM
    -- 商への持ち上げは全射
    have hlift : Function.Surjective (QuotientGroup.lift (Subgroup.center ↥(P : Subgroup G))
        ((QuotientGroup.mk' M).subgroupMap (P : Subgroup G)) hker) := by
      intro y
      obtain ⟨x, hx⟩ := MonoidHom.subgroupMap_surjective (QuotientGroup.mk' M)
        (P : Subgroup G) y
      exact ⟨QuotientGroup.mk' _ x, hx⟩
    -- 類の降下
    have hclass : Group.nilpotencyClass ↥(Q : Subgroup (G ⧸ M)) ≤ n := by
      rw [hQ]
      refine le_trans (Group.nilpotencyClass_le_of_surjective _ hlift) ?_
      rw [Group.nilpotencyClass_quotient_center]
      omega
    have hIH : HasPiLengthLE ({p} : Set ℕ) (G ⧸ M) n := ih Q hclass
    rw [HasPiLengthLE, piUpperSeries_succ_eq_comap, hIH, Subgroup.comap_top]

/-- **Isaacs Problem 3D.1(b)** (書籍 p. 95): `G` が `p`-可解なら `G` の `p`-length は
Sylow `p`-部分群 `P` の冪零類以下。

`P` の冪零類に関する帰納。類 `0` (= `P` 自明) なら `p ∤ |G|` で `p`-length `0`。
一般には `M := O_{p',p}(G)` に落とすと, 3D.1(a) から `Z(P) ≤ M` なので `G/M` の
Sylow `p`-部分群は `P/Z(P)` の商, したがって類が 1 下がる。`π`-length の shift
(`piUpperSeries_succ_eq_comap`) で帰納が閉じる。 -/
theorem hasPiLengthLE_nilpotencyClass {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [IsPiSeparable ({p} : Set ℕ) G] (P : Sylow p G) :
    HasPiLengthLE ({p} : Set ℕ) G (Group.nilpotencyClass ↥(P : Subgroup G)) :=
  hasPiLengthLE_nilpotencyClass_aux _ P le_rfl

end -- 3D

end OddOrder.Isaacs.Ch03
