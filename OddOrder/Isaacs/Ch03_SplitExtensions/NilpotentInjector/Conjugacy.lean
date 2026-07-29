/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.Injector
import OddOrder.Isaacs.Ch03_SplitExtensions.Carter.Defs

/-!
# Isaacs Problem 3C.8 — nilpotent injector の共役性

有限可解群の 2 つの nilpotent injector は共役である
(`exists_conj_of_isNilpotentInjector`)。書籍は証明を与えない (3C.7 と同じ challenge
problem) ので証明は自前で、Mann の構造定理の経路を採る。

## 証明

`I_p := nilPiPart I {p}` とおくと:

* `I_p` は `C(p)` の Sylow `p`-部分群 (`isHallPart_pCentralizer_of_isNilpotentInjector`)
  なので, `J_p` と `C(p)` の元 `c` で共役 (`hall_C` を `↥C(p)` に適用)。
* `c ∈ C(p)` による共役は `q ≠ p` の `I_q` を**動かさない**
  (`map_conj_eq_self_of_mem_pCentralizer`)。
* よって素数を 1 つずつ処理してよい (`Finset` 上の帰納)。
* すべての素数で `I_p = J_p` になれば, 位数の比較で `I = J`
  (`eq_of_nilPiPart_eq`): `|I|` の `p`-部分は `|I_p|` に等しく, どれも `I ⊓ J` の位数を
  割るので `|I| ∣ |I ⊓ J|`, したがって `I ≤ J` で極大性から `I = J`。

## Main results

- `exists_conj_of_isNilpotentInjector` — **Problem 3C.8**。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C.8: 共役性 -/

variable {G : Type*} [Group G]

/-- `{p}`-Hall 部分の位数は `|N|` の `p`-部分。 -/
theorem card_isHallPart_singleton [Finite G] {p : ℕ} [Fact p.Prime] {N A : Subgroup G}
    (h : IsHallPart N A ({p} : Set ℕ)) :
    Nat.card ↥A = p ^ (Nat.card ↥N).factorization p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_of_isPiGroup_singleton h.isPiGroup)
  have hmul : Nat.card ↥A * A.relIndex N = Nat.card ↥N := by
    have := Subgroup.card_mul_index (A.subgroupOf N)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv] at this
  have hidx : (A.relIndex N).factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    refine Or.inr (Or.inl fun hdvd => ?_)
    exact h.relIndex_no_pi p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, by
        intro h0
        rw [h0, mul_zero] at hmul
        exact Nat.card_pos.ne' hmul.symm⟩) rfl
  have hidx0 : A.relIndex N ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact Nat.card_pos.ne' hmul.symm
  have hpow : (p ^ n).factorization p = n := by
    simp [Nat.Prime.factorization_pow (Fact.out : Nat.Prime p)]
  have hkey : (Nat.card ↥N).factorization p = n := by
    conv_lhs => rw [← hmul]
    rw [Nat.factorization_mul (Nat.card_pos.ne' : Nat.card ↥A ≠ 0) hidx0, Finsupp.add_apply,
      hidx, add_zero, hn, hpow]
  rw [hn, hkey]

/-- injector の共役はまた injector。 -/
theorem IsNilpotentInjector.map_conj [Finite G] {I : Subgroup G} (hI : IsNilpotentInjector I)
    (c : G) : IsNilpotentInjector (I.map (MulAut.conj c).toMonoidHom) := by
  refine ⟨isNilpotent_map_conj hI.1 c, ?_, ?_⟩
  · have hF : (Ch01.fitting G).map (MulAut.conj c).toMonoidHom = Ch01.fitting G :=
      Subgroup.Normal.map_conj_eq (Ch01.fitting G) c
    rw [← hF]
    exact Subgroup.map_mono hI.2.1
  · intro J hIJ hJ
    have hback : I ≤ J.map (MulAut.conj c⁻¹).toMonoidHom := by
      have := Subgroup.map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) hIJ
      rwa [map_conj_trans, inv_mul_cancel, map_conj_one] at this
    have heq := hI.2.2 (J.map (MulAut.conj c⁻¹).toMonoidHom) hback (isNilpotent_map_conj hJ c⁻¹)
    have := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) heq
    rwa [map_conj_trans, mul_inv_cancel, map_conj_one] at this

/-- すべての素数で `{p}`-部分が一致する 2 つの injector は等しい。

`|I_p| = |I|` の `p`-部分で, `I_p = J_p ≤ I ⊓ J` なので `|I|` の各素数冪が `|I ⊓ J|` を
割る。ゆえに `|I| ∣ |I ⊓ J|` で `I ≤ J`, 極大性から `I = J`。 -/
theorem eq_of_nilPiPart_eq [Finite G] [IsSolvable G] {I J : Subgroup G}
    (hI : IsNilpotentInjector I) (hJ : IsNilpotentInjector J)
    (h : ∀ p : ℕ, p.Prime → nilPiPart I ({p} : Set ℕ) = nilPiPart J ({p} : Set ℕ)) : I = J := by
  have hdvd : Nat.card ↥I ∣ Nat.card ↥(I ⊓ J) := by
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
    rw [Finsupp.le_def]
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      have hIp := isHallPart_nilPiPart (N := I) ({p} : Set ℕ) hI.1
      have hle : nilPiPart I ({p} : Set ℕ) ≤ I ⊓ J :=
        le_inf hIp.1 (h p hp ▸ (isHallPart_nilPiPart (N := J) ({p} : Set ℕ) hJ.1).1)
      have hcard := card_isHallPart_singleton hIp
      have hpow : p ^ (Nat.card ↥I).factorization p ∣ Nat.card ↥(I ⊓ J) := by
        rw [← hcard]
        exact Subgroup.card_dvd_of_le hle
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hpow
    · have hzero : (Nat.card ↥I).factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        exact Or.inl hp
      simp [hzero]
  have hle : Nat.card ↥I ≤ Nat.card ↥(I ⊓ J) := Nat.le_of_dvd Nat.card_pos hdvd
  have hIJ : I ≤ J := by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : I ⊓ J ≤ I) hle
    exact this ▸ inf_le_right
  exact (hI.2.2 J hIJ hJ.1).symm

/-- 3C.8 の帰納本体: `π` の外側の素数で `{p}`-部分が一致していれば共役。 -/
private theorem exists_conj_aux [Finite G] [IsSolvable G] (π : Finset ℕ) :
    ∀ {I J : Subgroup G}, IsNilpotentInjector I → IsNilpotentInjector J →
      (∀ p : ℕ, p.Prime → p ∉ π →
        nilPiPart I ({p} : Set ℕ) = nilPiPart J ({p} : Set ℕ)) →
      ∃ g : G, I.map (MulAut.conj g).toMonoidHom = J := by
  classical
  induction π using Finset.induction_on with
  | empty =>
    intro I J hI hJ hyp
    exact ⟨1, by rw [map_conj_one, eq_of_nilPiPart_eq hI hJ fun p hp => hyp p hp (by simp)]⟩
  | @insert p s hps ih =>
    intro I J hI hJ hyp
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      have hIp := isHallPart_pCentralizer_of_isNilpotentInjector hI (p := p)
      have hJp := isHallPart_pCentralizer_of_isNilpotentInjector hJ (p := p)
      obtain ⟨c, hcmem, hc⟩ : ∃ c ∈ pCentralizer G p,
          (nilPiPart I ({p} : Set ℕ)).map (MulAut.conj c).toMonoidHom
            = nilPiPart J ({p} : Set ℕ) := by
        obtain ⟨y, hy⟩ := hall_C (G := ↥(pCentralizer G p)) hIp.2 hJp.2
        exact ⟨(y : G), y.2, (map_conj_eq_iff_subgroupOf hIp.1 hJp.1 y).mp hy⟩
      have hI' : IsNilpotentInjector (I.map (MulAut.conj c).toMonoidHom) := hI.map_conj c
      have hkey : ∀ q : ℕ, q.Prime → q ∉ s →
          nilPiPart (I.map (MulAut.conj c).toMonoidHom) ({q} : Set ℕ)
            = nilPiPart J ({q} : Set ℕ) := by
        intro q hq hqs
        rw [nilPiPart_map_conj ({q} : Set ℕ) hI.1 c]
        by_cases hqp : q = p
        · subst hqp
          exact hc
        · haveI : Fact q.Prime := ⟨hq⟩
          rw [map_conj_eq_self_of_mem_pCentralizer (Ne.symm hqp)
            (isHallPart_pCentralizer_of_isNilpotentInjector hI (p := q)) hcmem]
          exact hyp q hq (by simp [Finset.mem_insert, hqp, hqs])
      obtain ⟨g, hg⟩ := ih hI' hJ hkey
      exact ⟨g * c, by rw [← map_conj_trans]; exact hg⟩
    · refine ih hI hJ fun q hq hqs => hyp q hq ?_
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hqp => hp (hqp ▸ hq), hqs⟩

/-- **Isaacs Problem 3C.8** (書籍 p. 91): 有限可解群の 2 つの nilpotent injector
(= `F(G)` を含む極大な冪零部分群) は共役。

書籍は証明を与えない (challenge problem)。証明は Mann の構造定理経由 (ファイル冒頭)。 -/
theorem exists_conj_of_isNilpotentInjector [Finite G] [IsSolvable G] {I J : Subgroup G}
    (hI : IsNilpotentInjector I) (hJ : IsNilpotentInjector J) :
    ∃ g : G, I.map (MulAut.conj g).toMonoidHom = J := by
  classical
  exact exists_conj_aux (Nat.card G).primeFactors hI hJ fun p hp hpn => by
    -- `p ∤ |G|` なら `I_p = J_p = ⊥`
    have hnot : ¬ p ∣ Nat.card G := fun hdvd =>
      hpn (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
    haveI : Fact p.Prime := ⟨hp⟩
    have hbot : ∀ {K : Subgroup G}, Group.IsNilpotent ↥K → nilPiPart K ({p} : Set ℕ) = ⊥ := by
      intro K hK
      have hpart := isHallPart_nilPiPart (N := K) ({p} : Set ℕ) hK
      refine (Subgroup.card_eq_one.mp ?_)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_of_isPiGroup_singleton hpart.isPiGroup)
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · rw [hn, hn0, pow_zero]
      · exfalso
        refine hnot (dvd_trans (dvd_pow_self p hn0.ne') ?_)
        rw [← hn]
        exact Subgroup.card_subgroup_dvd_card _
    rw [hbot hI.1, hbot hJ.1]

end -- 3C.8: 共役性

end OddOrder.Isaacs.Ch03
