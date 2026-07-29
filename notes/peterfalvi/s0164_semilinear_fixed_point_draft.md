# 0164 β: 半線形固定点定理の実装 draft (2026-07-29)

`OddOrder/Algebra/SemilinearFixedPoint.lean` に入れる予定の
`OddOrder.exists_ne_zero_fixed_of_semilinear` の作業中 draft。
**証明の骨格は完成しているが、mathlib の名前・向きの微調整が 6 箇所残っている**
ため、leaf を green に保つ目的でいったんここへ退避した (issue 0164)。

## 残っている修正 (2026-07-29 時点の build エラー)

1. `Nat.eq_div_of_eq_mul_left` が存在しない → `Nat.eq_div_of_eq_mul_left'` か
   `Nat.div_eq_of_eq_mul_left` を探す。`hEeq` の証明はそのあと 1 行余る
   ("No goals to be solved") ので `rw [← hmul]` を削る。
2. `hT'fix` の最後: 目標が `(v ^ s * c) • e₀ = v • e₀` なので
   `hv : c * v ^ s = v` を使う前に `mul_comm` が要る。
3. `Nat.coprime_primes_right` が存在しない → `¬ p ∣ j` と `p` 素数から
   `Nat.Coprime j p` を出すのは `(Nat.Prime.coprime_iff_not_dvd hp).mpr hjp |>.symm`。
4. `Nat.ModEq.pow_totient` の引数の向きが逆 (`p ^ j.totient ≡ 1 [MOD j]` が出ている)
   → `Nat.ModEq.pow_totient` に渡す coprime の向きを直す。
5. `hjj` の `omega` (指数の `p - 2 + 1 = p - 1`) は `hp.two_le` を context に
   入れてから。
6. 最後の `simpa using hfin` は `Function.iterate_one` 等で仕上げる。

## 証明の骨格 (数学的には完成)

`T (a • e₀) = (σ a * c) • e₀` (`T e₀ = c • e₀`) と `T^[p] = id` から
`σ ^ p = 1` と `c ^ (∑_{i<p} s^i) = 1`。`σ ≠ 1` ゆえ `⟨σ⟩` は位数 `p` で、
`exists_generator_pow_natCard_fixedSet` が生成元 `τ : a ↦ a^s` (`|F| = s^p`) を与える。
`τ = σ^j` と書いて `T' := T^[j]` に取り替える (`p ∤ j` なので `T'` の固定点は
`T` の固定点 — Fermat で `j^{p-1} ≡ 1 mod p`)。あとは
`exists_ne_zero_mul_pow_eq` を当てるだけ。

## draft 本体

```lean
/-! ## The one-dimensional semilinear fixed-point theorem -/

/-- **A semilinear automorphism of prime order has a non-zero fixed vector** on a
line over a finite field, *provided its twist `σ` is non-trivial*.

The twist hypothesis cannot be dropped: an `F`-linear map of prime order on a
line is multiplication by a scalar `c ≠ 1`, and `a * c = a` has no non-zero
solution.

`T (a • e₀) = (σ a * c) • e₀` where `T e₀ = c • e₀`, and `T^[p] = id` forces both
`σ ^ p = 1` and `c ^ (1 + s + ⋯) = 1`.  With `σ ≠ 1` the group `⟨σ⟩` has order
`p`, so `exists_generator_pow_natCard_fixedSet` provides a generator
`τ : a ↦ a ^ s` with `|F| = s ^ p`; replacing `T` by the iterate whose twist is
`τ` (harmless, since a fixed point of `T^[j]` with `p ∤ j` is a fixed point of
`T`) puts us in the situation of `exists_ne_zero_mul_pow_eq`. -/
theorem _root_.OddOrder.exists_ne_zero_fixed_of_semilinear
    {F M : Type*} [Field F] [Finite F] [AddCommGroup M] [Module F M]
    {e₀ : M} (he₀ : e₀ ≠ 0) (hspan : ∀ x : M, ∃ a : F, a • e₀ = x)
    (T : M ≃+ M) (σ : _root_.RingAut F)
    (hsl : ∀ (a : F) (x : M), T (a • x) = σ a • T x)
    {p : ℕ} (hp : p.Prime) (hTp : ∀ x : M, T^[p] x = x) (hσne : σ ≠ 1) :
    ∃ x : M, x ≠ 0 ∧ T x = x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (fun a : F => a • e₀) := smul_left_injective F he₀
  -- iterating the semilinearity
  have hiter : ∀ (n : ℕ) (a : F) (x : M), T^[n] (a • x) = (σ ^ n) a • T^[n] x := by
    intro n
    induction n with
    | zero => intro a x; simp
    | succ n ih =>
      intro a x
      rw [Function.iterate_succ_apply', ih, hsl, Function.iterate_succ_apply']
      congr 1
      rw [pow_succ']
      rfl
  -- the twist has order `p`
  have hσp : σ ^ p = 1 := by
    ext a
    have h1 := hiter p a e₀
    rw [hTp, hTp] at h1
    have h2 : a • e₀ = (σ ^ p) a • e₀ := h1
    exact (hinj h2).symm
  have hσord : orderOf σ = p :=
    (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hσp)).resolve_left
      (fun h => hσne (orderOf_eq_one_iff.mp h))
  -- the distinguished generator of `⟨σ⟩`
  set B : Subgroup (_root_.RingAut F) := Subgroup.zpowers σ with hBdef
  have hBcard : Nat.card B = p := by rw [hBdef, Nat.card_zpowers, hσord]
  obtain ⟨τ, hτB, hτgen, hτpow, hFcard⟩ :=
    exists_generator_pow_natCard_fixedSet (F := F) hp hBcard
  set s : ℕ := Nat.card (fixedSet B) with hs
  -- write `τ` as an iterate of `σ`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, σ ^ j = τ := by
    have hmem : τ ∈ Subgroup.zpowers σ := hBdef ▸ hτB
    exact mem_powers_iff_mem_zpowers.mpr hmem
  -- `p ∤ j`, since `τ ≠ 1`
  have hτne : τ ≠ 1 := by
    intro h
    have h1 : Nat.card B = 1 := by
      rw [← hτgen, h]
      simp
    have := hp.one_lt
    omega
  have hjp : ¬ p ∣ j := by
    intro hdvd
    obtain ⟨k, rfl⟩ := hdvd
    exact hτne (by rw [← hj, pow_mul, hσp, one_pow])
  -- the iterate whose twist is `τ`
  set T' : M → M := (T : M → M)^[j] with hT'
  have hT'sl : ∀ (a : F) (x : M), T' (a • x) = τ a • T' x := by
    intro a x
    rw [hT', hiter j a x, hj]
  have hT'p : ∀ x : M, T'^[p] x = x := by
    intro x
    rw [hT', ← Function.iterate_mul, mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed (hTp x) j
  obtain ⟨c, hc⟩ := hspan (T' e₀)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    have hTe : T' e₀ ≠ 0 := by
      rw [hT']
      intro hz
      have : e₀ = 0 := by
        have hinjT : Function.Injective ((T : M → M)^[j]) :=
          Function.Injective.iterate T.injective j
        have h0 : ((T : M → M)^[j]) 0 = 0 := by
          simpa using Function.iterate_fixed (map_zero T) j
        exact hinjT (by rw [hz, h0])
      exact he₀ this
    exact hTe hc.symm
  -- the norm condition
  have hErec : ∀ n : ℕ, T'^[n] e₀ = c ^ (∑ i ∈ Finset.range n, s ^ i) • e₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hT'sl, hτpow, ← hc, smul_smul]
      congr 1
      rw [← pow_mul, ← pow_succ, geom_sum_succ, mul_comm s]
  -- `s ≥ 2`
  have hFge : 2 ≤ Nat.card F := by
    haveI : Fintype F := Fintype.ofFinite F
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial F)
    omega
  have hs2 : 2 ≤ s := by
    by_contra hcon
    push Not at hcon
    have hle : s ^ p ≤ 1 := by
      calc s ^ p ≤ 1 ^ p := Nat.pow_le_pow_left (by omega) p
        _ = 1 := one_pow p
    rw [hFcard] at hFge
    omega
  -- the geometric sum is the exponent `exists_ne_zero_mul_pow_eq` wants
  have hEeq : (∑ i ∈ Finset.range p, s ^ i) = (Nat.card F - 1) / (s - 1) := by
    have hmul := geom_sum_mul_of_one_le (x := s) (by omega) p
    rw [hFcard]
    refine (Nat.eq_div_of_eq_mul_left (by omega) ?_)
    rw [← hmul]
  -- the norm condition
  have hcE : c ^ (∑ i ∈ Finset.range p, s ^ i) = 1 := by
    have h1 := hErec p
    rw [hT'p] at h1
    have h2 : (1 : F) • e₀ = c ^ (∑ i ∈ Finset.range p, s ^ i) • e₀ := by
      rw [one_smul]; exact h1
    exact (hinj h2).symm
  obtain ⟨v, hv0, hv⟩ :=
    exists_ne_zero_mul_pow_eq (F := F) (s := s) (n := p) (by omega) hFcard hc0
      (by rw [← hEeq]; exact hcE)
  refine ⟨v • e₀, smul_ne_zero hv0 he₀, ?_⟩
  -- `T'` fixes it
  have hT'fix : T' (v • e₀) = v • e₀ := by
    rw [hT'sl, hτpow, ← hc, smul_smul, hv]
  -- transport back to `T` using `p ∤ j`
  have hcop : Nat.Coprime j p := (Nat.coprime_primes_right hp).mpr hjp
  have hferm : j ^ (p - 1) % p = 1 % p := by
    have := Nat.ModEq.pow_totient (Nat.Coprime.symm hcop)
    rwa [Nat.totient_prime hp] at this
  obtain ⟨k, hk⟩ : ∃ k, j ^ (p - 1) = 1 + k * p := by
    have h1 : 1 ≤ j ^ (p - 1) := Nat.one_le_pow _ _ (by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact absurd (dvd_zero p) hjp
      · exact h)
    have h2 : p ∣ j ^ (p - 1) - 1 := (Nat.modEq_iff_dvd' h1).mp hferm.symm
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, by omega⟩
  have hjj : j * j ^ (p - 2) = j ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hfin : (T : M → M)^[j ^ (p - 1)] (v • e₀) = v • e₀ := by
    rw [← hjj, mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed hT'fix (p - 2)
  rw [hk, add_comm, Function.iterate_add_apply] at hfin
  rw [mul_comm, Function.iterate_mul] at hfin
  have hid : ((T : M → M)^[p])^[k] (v • e₀) = v • e₀ :=
    Function.iterate_fixed (hTp (v • e₀)) k
  rw [hid] at hfin
  simpa using hfin

```
