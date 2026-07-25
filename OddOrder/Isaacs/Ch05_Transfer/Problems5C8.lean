/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# Isaacs Problem 5C.8 — 最小奇素数 `p` で `p^3 ∤ |G|` なら正規 `p`-補群 (p. 163)

**主張**: `p > 2` を `|G|` の最小素因数とし `p^3 ∤ |G|` とすると, `G` は正規 `p`-補群を持つ。

**証明**: Sylow `p`-部分群 `P` は位数 `p^n` (`n ≤ 2`) ゆえ可換。Burnside
(`hasNormalPComplement_of_sylow_normalizer_le_centralizer`) より `N_G(P) ≤ C_G(P)` を
示せばよい。`N_G(P)/C_G(P) ↪ Aut(P)` なので `|N_G(P) : C_G(P)|` は `|Aut P|` を割り、
また `|G|` も割る。`P` 可換ゆえ `P ≤ C_G(P)` で `p ∤ |N_G(P) : C_G(P)|`。
素数 `q` がこれを割れば `q ∣ |G|` で最小性から `q ≥ p`, かつ `q ≠ p` ゆえ `q > p`。

⭐ ここで **`|Aut P|` を計算せずに済む**: 位数 `q` の自己同型 `σ` を取り, `⟨σ⟩` の `P` への
作用で軌道数え上げ (`IsPGroup.card_modEq_card_fixedPoints`) すると
`p^n ≡ |Fix σ| (mod q)` で `Fix σ` は `P` の真部分群 (`σ ≠ 1`)。ゆえに
`q ∣ p^n - p^k` (`k < n ≤ 2`) となり `q ∣ p - 1` か `q ∣ p^2 - 1`。前者は `q > p` に反し,
後者は `q ∣ p + 1` から `q = p + 1` (偶数) となって `q` が奇素数であることに反する。

(書籍の標準証明は `|Aut(C_p × C_p)| = |GL_2(F_p)| = p(p-1)^2(p+1)` を使うが、
mathlib に `Aut` の同型計算が無いので軌道数え上げで置き換えた。)
-/

namespace OddOrder.Isaacs.Ch05

variable {G : Type*} [Group G]

section /- 5C.8: 最小奇素数と `p^3 ∤ |G|` (p. 163) -/

/-- ⭐ **軌道数え上げによる自己同型の制約**: 位数 `p^n` の群 `P` の自己同型群の位数を割る
素数 `q ≠ p` は, ある `1 ≤ m ≤ n` に対し `q ∣ p^m - 1` を満たす。

位数 `q` の自己同型 `σ` を取り (`exists_prime_orderOf_dvd_card`), `⟨σ⟩` の `P` への作用で
軌道数え上げ (`IsPGroup.card_modEq_card_fixedPoints`) すると `p^n ≡ |Fix σ| (mod q)`。
`Fix σ = σ.toMonoidHom.eqLocus (MonoidHom.id P)` は `σ ≠ 1` ゆえ真部分群なので
`|Fix σ| = p^k` (`k < n`) で `q ∣ p^n - p^k = p^k (p^{n-k} - 1)`, `q ≠ p` より
`q ∣ p^{n-k} - 1`。

⭐ **`|Aut P|` の具体形 (`|GL_n(F_p)|` 等) を一切使わない**ので, `p = 2` でも `p` 奇でも
そのまま使える (Problem 5C.8 は `p` 奇, 5C.9 は `p = 2` で使う)。 -/
theorem exists_dvd_pow_sub_one_of_dvd_card_mulAut {P : Type*} [Group P] [Finite P] {p n q : ℕ}
    (hp : p.Prime) (hcard : Nat.card P = p ^ n) (hq : q.Prime) (hqp : q ≠ p)
    (hdvd : q ∣ Nat.card (MulAut P)) : ∃ m, 1 ≤ m ∧ m ≤ n ∧ q ∣ p ^ m - 1 := by
  classical
  have hp2le : 2 ≤ p := hp.two_le
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype (MulAut P) := Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (G := MulAut P) q
    (by rwa [← Nat.card_eq_fintype_card])
  -- `S := ⟨σ⟩` は位数 `q` の `q`-群
  have hScard : Nat.card ↥(Subgroup.zpowers σ) = q := by rw [Nat.card_zpowers, hσ]
  have hSp : IsPGroup q ↥(Subgroup.zpowers σ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hScard, pow_one]
  -- 不動点は `σ` の固定部分群
  have hfix : MulAction.fixedPoints ↥(Subgroup.zpowers σ) P
      = ↑(σ.toMonoidHom.eqLocus (MonoidHom.id P)) := by
    ext x
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut P) x :=
        Subgroup.zpowers_le.mpr hx
      exact hle g.2
  have hmod := hSp.card_modEq_card_fixedPoints (α := P)
  rw [hfix] at hmod
  -- `Fix σ` は真部分群
  have hne : σ.toMonoidHom.eqLocus (MonoidHom.id P) ≠ ⊤ := by
    intro htop
    have hs1 : σ = 1 := by
      ext x
      have hx : x ∈ σ.toMonoidHom.eqLocus (MonoidHom.id P) := htop ▸ Subgroup.mem_top x
      exact hx
    rw [hs1, orderOf_one] at hσ
    exact hq.one_lt.ne hσ
  obtain ⟨k, hk, hkcard⟩ :=
    (Nat.dvd_prime_pow hp).mp
      (hcard ▸ Subgroup.card_subgroup_dvd_card (σ.toMonoidHom.eqLocus (MonoidHom.id P)))
  have hkn : k < n := by
    rcases lt_or_eq_of_le hk with hlt | heq
    · exact hlt
    · exact absurd (Subgroup.eq_top_of_card_eq _ (by rw [hkcard, heq, hcard])) hne
  -- `q ∣ p ^ n - p ^ k`
  rw [hcard] at hmod
  have hmod2 : p ^ n ≡ p ^ k [MOD q] := by rw [← hkcard]; exact hmod
  have hple : p ^ k ≤ p ^ n := Nat.pow_le_pow_right hp.one_lt.le hkn.le
  have hqdvd : q ∣ p ^ n - p ^ k := (Nat.modEq_iff_dvd' hple).mp hmod2.symm
  have hfactor : p ^ n - p ^ k = p ^ k * (p ^ (n - k) - 1) := by
    have hsplit : p ^ n = p ^ k * p ^ (n - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mul_sub, mul_one]
  rw [hfactor] at hqdvd
  have hqnp : ¬ q ∣ p ^ k := fun hc =>
    hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hc))
  refine ⟨n - k, by omega, by omega, ?_⟩
  rcases (Nat.Prime.dvd_mul hq).mp hqdvd with hA | hB
  · exact absurd hA hqnp
  · exact hB

/-- 位数 `p^n` (`n ≤ 2`, `p` 奇素数) の群には位数 `q > p` の素数位数自己同型が無い。

`exists_dvd_pow_sub_one_of_dvd_card_mulAut` で `q ∣ p^m - 1` (`m ∈ {1, 2}`) に落とす。
`m = 1` なら `q ∣ p - 1` で `q > p` に反し, `m = 2` なら `q ∣ p + 1` から `q = p + 1` が
偶数となって `q` が奇素数であることに反する。 -/
theorem not_dvd_card_mulAut_of_card_eq_pow {P : Type*} [Group P] [Finite P] {p n q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcard : Nat.card P = p ^ n) (hn : n ≤ 2)
    (hq : q.Prime) (hqp : p < q) : ¬ q ∣ Nat.card (MulAut P) := by
  intro hdvd
  have hp2le : 2 ≤ p := hp.two_le
  obtain ⟨m, hm1, hmn, hq1⟩ :=
    exists_dvd_pow_sub_one_of_dvd_card_mulAut hp hcard hq (by omega) hdvd
  have hm2 : m ≤ 2 := by omega
  interval_cases m
  · rw [pow_one] at hq1
    have := Nat.le_of_dvd (by omega) hq1
    omega
  · have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      rw [Nat.sub_mul, one_mul, Nat.mul_add, mul_one, pow_two]
      omega
    rw [hsq] at hq1
    rcases (Nat.Prime.dvd_mul hq).mp hq1 with hA | hB
    · have := Nat.le_of_dvd (by omega) hA
      omega
    · have hle := Nat.le_of_dvd (by omega) hB
      have hodd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · exact h
      have h2q : (2 : ℕ) ∣ q := by omega
      rcases Nat.Prime.eq_one_or_self_of_dvd hq 2 h2q with h | h <;> omega

/-- ⭐ **Isaacs Problem 5C.8** (p. 163): `p > 2` が `|G|` の最小素因数で `p^3 ∤ |G|` なら
`G` は正規 `p`-補群を持つ。 -/
theorem hasNormalPComplement_of_minFac_of_not_dvd_pow_three [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hmin : (Nat.card G).minFac = p) (h3 : ¬ p ^ 3 ∣ Nat.card G) :
    HasNormalPComplement p G := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  refine hasNormalPComplement_of_sylow_normalizer_le_centralizer P ?_
  -- `|P| = p ^ n` で `n ≤ 2`
  obtain ⟨n, hn⟩ := P.2.exists_card_eq
  have hPdvd : Nat.card ↥(P : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hn2 : n ≤ 2 := by
    by_contra hc
    exact h3 (dvd_trans (pow_dvd_pow p (by omega)) (hn ▸ hPdvd))
  -- `P` は可換
  haveI hPab : IsMulCommutative ↥(P : Subgroup G) := by
    interval_cases n
    · refine IsMulCommutative.of_comm fun a b => ?_
      have hc1 : Nat.card ↥(P : Subgroup G) = 1 := by simpa using hn
      haveI := (Nat.card_eq_one_iff_unique.mp hc1).1
      exact Subsingleton.elim _ _
    · haveI : IsCyclic ↥(P : Subgroup G) :=
        isCyclic_of_prime_card (p := p) (by simpa using hn)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hn
  -- `N_G(P)/C_G(P) ↪ Aut P`
  have key := Subgroup.card_dvd_of_injective _
    (QuotientGroup.kerLift_injective (P : Subgroup G).normalizerMonoidHom)
  rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex] at key
  refine Subgroup.relIndex_eq_one.mp ?_
  by_contra hne
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
  -- `q ∣ |G|` ゆえ `p ≤ q`
  have hrelG : (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer (P : Subgroup G)) ∣ Nat.card G :=
    dvd_trans (Subgroup.relIndex_dvd_card _ _) (Subgroup.card_subgroup_dvd_card _)
  have hqge : p ≤ q := hmin ▸ Nat.minFac_le_of_dvd hq.two_le (hqdvd.trans hrelG)
  -- `p ∤ |N_G(P) : C_G(P)|` (`P` 可換ゆえ `P ≤ C_G(P)`)
  have hpnot : ¬ p ∣ (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer (P : Subgroup G)) := by
    intro hc
    have h1 : (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer (P : Subgroup G)) ∣
        (P : Subgroup G).relIndex (Subgroup.normalizer (P : Subgroup G)) :=
      Subgroup.relIndex_dvd_of_le_left _ P.le_centralizer
    have h2 : (P : Subgroup G).relIndex (Subgroup.normalizer (P : Subgroup G)) ∣
        (P : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_le P.le_normalizer
    exact P.not_dvd_index ((hc.trans h1).trans h2)
  have hqne : q ≠ p := fun hqp => hpnot (hqp ▸ hqdvd)
  exact not_dvd_card_mulAut_of_card_eq_pow hp hp2 hn hn2 hq (by omega) (hqdvd.trans key)

end

end OddOrder.Isaacs.Ch05
