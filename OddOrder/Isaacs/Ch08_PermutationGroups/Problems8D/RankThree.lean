/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.ArrowKernelIndex

/-!
# Isaacs Problem 8D.5 (p. 269) — rank 3 で subdegree が互いに素なとき

`G` が `Ω` に推移的に作用し rank が 3, subdegree が `1 < m < n` で `m` と `n` が
互いに素なら, **`m + 1` は `n` を割る**。

Isaacs のヒント通り `k_m` が `1 + m + n` を割ることを使う。

## 証明の流れ

* `k_m = |K_m(α) : G_α|` は `|G : G_α| = |Ω| = 1 + m + n` を割る
  (`Subgroup.relIndex_dvd_index_of_le`)。
* subdegree は `1, m, n` の 3 つだけで `m`, `n` は互いに素なので, どの subdegree も
  `m` か `n` の一方と互いに素。よって **Thm 8.42 (b)**
  (`relIndex_arrowKernel_dvd_of_isArrow`) から `k_m ∣ n`。
* 差をとって `k_m ∣ m + 1`。他方 **8D.4 (a)** で `m ≤ k_m` なので `k_m = m` か `m + 1`。
  `k_m = m` だと `m ∣ m + 1`, つまり `m ∣ 1` で `m > 1` に反するから `k_m = m + 1`。
* ゆえに `(m + 1) ∣ n`。

## Main results

- `succ_dvd_of_rank_three` — **Problem 8D.5** 本体。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problem 8D.5 -/

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [IsPretransitive G Ω]

/-- **Isaacs Problem 8D.5** (p. 269)。rank 3 の推移作用で subdegree が `1 < m < n`,
`gcd(m, n) = 1` なら `(m + 1) ∣ n`。

rank 3 であることは「どの suborbit の長さも `1`, `m`, `n` のいずれか」(`hsize`) と
`|Ω| = 1 + m + n` (`hΩ`) で表す。 -/
theorem succ_dvd_of_rank_three {m n : ℕ} {α β γ : Ω}
    (hsize : ∀ δ ε : Ω, Set.ncard (orbit ↥(stabilizer G δ) ε) = 1 ∨
      Set.ncard (orbit ↥(stabilizer G δ) ε) = m ∨
      Set.ncard (orbit ↥(stabilizer G δ) ε) = n)
    (hΩ : Nat.card Ω = 1 + m + n)
    (hm : IsArrow G m α β) (hn : IsArrow G n α γ)
    (hm1 : 1 < m) (hmn : m < n) (hcop : Nat.Coprime m n) :
    (m + 1) ∣ n := by
  -- どの subdegree も `m` か `n` と互いに素
  have hcop' : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) m ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) n := by
    intro δ ε
    rcases hsize δ ε with h | h | h
    · exact Or.inl (by rw [h]; exact Nat.coprime_one_left m)
    · exact Or.inr (by rw [h]; exact hcop)
    · exact Or.inl (by rw [h]; exact hcop.symm)
  -- `k_m ∣ n` (Thm 8.42 (b)) と `k_m ∣ |Ω| = 1 + m + n`
  have hkn : (stabilizer G α).relIndex (arrowKernel G m α) ∣ n :=
    relIndex_arrowKernel_dvd_of_isArrow (G := G) (Ω := Ω) (m := m) (n := n) (α := α) (γ := γ)
      hmn hn hcop'
  have hkΩ : (stabilizer G α).relIndex (arrowKernel G m α) ∣ 1 + m + n := by
    have hdvd := Subgroup.relIndex_dvd_index_of_le
      (stabilizer_le_arrowKernel_self (G := G) (Ω := Ω) m α)
    rwa [index_stabilizer_of_transitive, hΩ] at hdvd
  -- 差をとって `k_m ∣ m + 1`
  have hk1 : (stabilizer G α).relIndex (arrowKernel G m α) ∣ m + 1 := by
    have h := Nat.dvd_sub hkΩ hkn
    rwa [show 1 + m + n - n = m + 1 by omega] at h
  -- `m ≤ k_m` (8D.4 (a)) と合わせて `k_m = m + 1`
  have hmk : m ≤ (stabilizer G α).relIndex (arrowKernel G m α) := le_relIndex_arrowKernel hm
  have hkle : (stabilizer G α).relIndex (arrowKernel G m α) ≤ m + 1 :=
    Nat.le_of_dvd (by omega) hk1
  have hkeq : (stabilizer G α).relIndex (arrowKernel G m α) = m + 1 := by
    rcases Nat.lt_or_ge ((stabilizer G α).relIndex (arrowKernel G m α)) (m + 1) with hlt | hge
    · -- `k_m = m` なら `m ∣ m + 1` で `m ∣ 1`
      exfalso
      have hkm : (stabilizer G α).relIndex (arrowKernel G m α) = m := by omega
      rw [hkm] at hk1
      have hd1 : m ∣ 1 := (Nat.dvd_add_right (dvd_refl m)).mp hk1
      have := Nat.le_of_dvd one_pos hd1
      omega
    · omega
  rwa [hkeq] at hkn

end -- Problem 8D.5

end OddOrder.Isaacs.Ch08
