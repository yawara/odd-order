/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch09_MoreSubnormality.StrongConjugacy
import OddOrder.Isaacs.Ch09_MoreSubnormality.SylowSubnormal

/-!
# Isaacs Ch. 9 — §9D: Bartels の定理 (9.28) (pp. 291-292)

Isaacs, *Finite Group Theory* (AMS GSM 92), §9D の **Theorem 9.28 (Bartels)**:
`X^{(G)} = X^{••G}` (強共役が生成する部分群 = subnormal closure)。

定義群と Lem 9.29 / 9.30 は sibling の
[`StrongConjugacy`](StrongConjugacy.lean) にある (1500 行規約による prefix-split)。
Lem 9.31 は [`SylowSubnormal`](SylowSubnormal.lean)。

## 証明の構成 (書籍 p.291-292)

最小反例 (`|G|` 最小, 次いで `|X|` 最小) を取り 6 step で矛盾を導く。帰納法の仮定は
`BartelsIH` として明示パラメータに持たせてあるので, 各 step は単独で sorry-free な
定理になっている。

* **Step 1** `bartels_step_one` — `Y^{(H)} = Z^{(H)} ⇒ Y^{(G)} = Z^{(G)}`
* **Step 2** `bartels_step_two` — 最小反例の `X` は `p`-群
* **Step 3** `bartels_step_three` — `Y` を `H` の Sylow `p` の中へ共役で送れる
* **Step 4** `bartels_step_four` — 極大 `M ⊇ X` の Sylow `p` は `G` の Sylow `p`
* Step 5, 6 — 未実装
-/

universe u

namespace OddOrder.Isaacs.Ch09

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`X^{(K)}` の共役両立性**: `(X^{(K)})^g = (X^g)^{(K^g)}`.

絶対版 `strongClosure_conjAct_smul` の相対版。Bartels Step 3 が
`(Y^h)^{(H)} = (Y^{(H)})^h` (`h ∈ H`) の形で使う。 -/
theorem strongClosureIn_conjAct_smul (c : ConjAct G) (K X : Subgroup G) :
    strongClosureIn (c • K) (c • X) = c • strongClosureIn K X := by
  have key : ∀ (d : ConjAct G) (L W : Subgroup G),
      strongClosureIn (d • L) (d • W) ≤ d • strongClosureIn L W := by
    intro d L W
    refine sSup_le ?_
    rintro V ⟨hV, hVL⟩
    have hback : IsStronglyConjugate W (d⁻¹ • V) := by
      have := hV.conjAct_smul d⁻¹
      rwa [inv_smul_smul] at this
    have hbackL : d⁻¹ • V ≤ L := by
      have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := d⁻¹) |>.mpr hVL
      rwa [inv_smul_smul] at this
    calc V = d • (d⁻¹ • V) := (smul_inv_smul d V).symm
      _ ≤ d • strongClosureIn L W :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (le_sSup ⟨hback, hbackL⟩)
  refine le_antisymm (key c K X) ?_
  have h2 := key c⁻¹ (c • K) (c • X)
  rw [inv_smul_smul, inv_smul_smul] at h2
  calc c • strongClosureIn K X ≤ c • (c⁻¹ • strongClosureIn (c • K) (c • X)) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h2
    _ = strongClosureIn (c • K) (c • X) := smul_inv_smul c _

/-- `h ∈ K` なら `K` は `h` による共役で不変。 -/
theorem conjAct_smul_self_of_mem {K : Subgroup G} {h : G} (hh : h ∈ K) :
    ConjAct.toConjAct h • K = K :=
  Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh)

/-- `ConjAct` による共役作用と `MulAut.conj` による共役作用は一致する
(mathlib の `Sylow` は後者を使うので橋が要る)。 -/
theorem conjAct_smul_eq_mulAut_smul (g : G) (X : Subgroup G) :
    ConjAct.toConjAct g • X = MulAut.conj g • X := by
  rw [conjAct_smul_eq_map, Subgroup.pointwise_smul_def]
  rfl

/-- **有限群の `p`-部分群は与えられた Sylow `p`-部分群の中へ共役で送れる**。

mathlib は `IsPGroup.exists_le_sylow` (ある Sylow に入る) と Sylow の共役性を
別々に持つだけなので, その 2 つを繋ぐ。Bartels Step 3 が使う。 -/
theorem exists_conjAct_smul_le_sylow {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup L} (hQ : IsPGroup p Q) (P : Sylow p L) :
    ∃ g : L, ConjAct.toConjAct g • Q ≤ (P : Subgroup L) := by
  obtain ⟨R, hR⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L R P
  refine ⟨g, ?_⟩
  rw [conjAct_smul_eq_mulAut_smul]
  calc MulAut.conj g • Q ≤ MulAut.conj g • (R : Subgroup L) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hR
    _ = ((g • R : Sylow p L) : Subgroup L) := Sylow.coe_subgroup_smul.symm
    _ = (P : Subgroup L) := by rw [hg]

/-! ### Bartels Step 3 の部品 — 相対版 (すべて `Subgroup G` のまま)

`↥H` / `↥L` を ambient にすると `Sylow p ↥(L.subgroupOf H)` のような二重 subtype が
出てしまうので, 9.31 と「p-部分群の Sylow 内共役」を `Subgroup G` の言葉に直しておく。
どちらも 9.29(a) 相対版と同じく「↥K に降ろして絶対版を使う」だけ。 -/

/-- **Lem 9.31 の相対版**: `S ≤ K` が `K` の中で subnormal, `P ≤ K` が `K` の Sylow `p`
なら `P ⊓ S` は `S` の Sylow `p` (指数が `p` と互いに素)。 -/
theorem not_dvd_relIndex_inf_of_isSubnormal_in [Finite G] {p : ℕ} [Fact p.Prime]
    {K S P : Subgroup G} (hSK : S ≤ K)
    (hS : (S.subgroupOf K).IsSubnormal) (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex K) :
    ¬ p ∣ (P ⊓ S).relIndex S := by
  have hPsub : IsPGroup p ↥(P.subgroupOf K) := hP.comap_subtype
  have hidx : ¬ p ∣ (P.subgroupOf K).index := hPidx
  have habs := not_dvd_relIndex_inf_of_isSubnormal hS (hPsub.toSylow hidx)
  have hinf : P.subgroupOf K ⊓ S.subgroupOf K = (P ⊓ S).subgroupOf K := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hPsub.toSylow_coe hidx, hinf, Subgroup.relIndex_subgroupOf hSK] at habs
  exact habs

/-- **p-部分群の Sylow 内共役, 相対版**: `Y ≤ L` が `p`-群, `Q ≤ L` が `L` の Sylow `p`
なら, ある `h ∈ L` で `Y^h ≤ Q`。 -/
theorem exists_mem_conjAct_smul_le_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {L Y Q : Subgroup G} (hYL : Y ≤ L) (hQL : Q ≤ L) (hY : IsPGroup p ↥Y)
    (hQ : IsPGroup p ↥Q) (hQidx : ¬ p ∣ Q.relIndex L) :
    ∃ h ∈ L, ConjAct.toConjAct h • Y ≤ Q := by
  have hQsub : IsPGroup p ↥(Q.subgroupOf L) := hQ.comap_subtype
  have hidx : ¬ p ∣ (Q.subgroupOf L).index := hQidx
  obtain ⟨g, hg⟩ := exists_conjAct_smul_le_sylow (Q := Y.subgroupOf L) hY.comap_subtype
    (hQsub.toSylow hidx)
  rw [hQsub.toSylow_coe hidx, ← conjAct_smul_subgroupOf] at hg
  refine ⟨(g : G), g.2, ?_⟩
  have hmap := Subgroup.map_mono (f := L.subtype) hg
  rwa [Subgroup.map_subgroupOf_eq_of_le (conjAct_smul_le_of_mem hYL g.2),
    Subgroup.map_subgroupOf_eq_of_le hQL] at hmap

/-- **`p`-部分群は Sylow に伸びる, 相対版**: `Y ≤ K` が `p`-群なら `Y ≤ S ≤ K` で
`S` が `K` の Sylow `p`-部分群となる `S` が取れる (すべて `Subgroup G` の言葉)。

`↥K` の `IsPGroup.exists_le_sylow` を `K.subtype` で押し出しただけ。 -/
theorem exists_sylow_ge_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {K Y : Subgroup G}
    (hYK : Y ≤ K) (hY : IsPGroup p ↥Y) :
    ∃ S : Subgroup G, Y ≤ S ∧ S ≤ K ∧ IsPGroup p ↥S ∧ ¬ p ∣ S.relIndex K := by
  obtain ⟨R, hR⟩ := (hY.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(R : Subgroup ↥K).map K.subtype, ?_, Subgroup.map_subtype_le _,
    R.isPGroup'.map K.subtype, ?_⟩
  · exact fun y hy => ⟨⟨y, hYK hy⟩, hR (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · have hsub : ((R : Subgroup ↥K).map K.subtype).subgroupOf K = (R : Subgroup ↥K) :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    change ¬ p ∣ (((R : Subgroup ↥K).map K.subtype).subgroupOf K).index
    rw [hsub]
    exact R.not_dvd_index

section /- 9D: Bartels Step 2 の部品 — 真部分群による生成 -/

/-- `Nat.Coprime a b` なら `x ∈ ⟨x^a⟩ ⊔ ⟨x^b⟩` (Bezout)。 -/
theorem mem_sup_zpowers_of_coprime {x : G} {a b : ℕ} (h : Nat.Coprime a b) :
    x ∈ Subgroup.zpowers (x ^ a) ⊔ Subgroup.zpowers (x ^ b) := by
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (a : ℤ) * u + (b : ℤ) * v = 1 := by
    refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
    have hg := Nat.gcd_eq_gcd_ab a b
    rw [Nat.Coprime.gcd_eq_one h] at hg
    push_cast at hg ⊢
    linarith
  have hx : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add, huv, zpow_one]
  have hmem : (x ^ a) ^ u * (x ^ b) ^ v ∈ Subgroup.zpowers (x ^ a) ⊔ Subgroup.zpowers (x ^ b) :=
    mul_mem
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) u))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) v))
  rwa [← hx] at hmem

end

/-- `p ∣ orderOf x`, `p` 素数のとき `⟨x^p⟩` は `⟨x⟩` の真部分群。 -/
theorem zpowers_pow_lt_zpowers [Finite G] {x : G} {p : ℕ} (hp : 1 < p) (hpd : p ∣ orderOf x) :
    Subgroup.zpowers (x ^ p) < Subgroup.zpowers x := by
  have hord : 0 < orderOf x := orderOf_pos x
  have hle : Subgroup.zpowers (x ^ p) ≤ Subgroup.zpowers x :=
    (Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) p)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hcard : Nat.card ↥(Subgroup.zpowers (x ^ p)) = Nat.card ↥(Subgroup.zpowers x) := by
    rw [heq]
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow, Nat.gcd_eq_right hpd] at hcard
  have : orderOf x / p < orderOf x := Nat.div_lt_self hord hp
  omega

/-- **Bartels Step 2 の部品**: `p`-群でない有限群 (の部分群) は真部分群たちで生成される。

`x ∈ X` をとり, `⟨x⟩ < X` なら済み。`⟨x⟩ = X` なら `X` は巡回で, `p`-群でないことから
位数は相異なる 2 素数 `p ≠ q` で割れる。`⟨x^p⟩`, `⟨x^q⟩` はいずれも真部分群で,
`Nat.Coprime p q` から `x ∈ ⟨x^p⟩ ⊔ ⟨x^q⟩` (Bezout)。 -/
theorem le_sSup_lt_of_forall_not_isPGroup [Finite G] {X : Subgroup G}
    (h : ∀ p : ℕ, p.Prime → ¬ IsPGroup p ↥X) :
    X ≤ sSup {Y : Subgroup G | Y < X} := by
  intro x hx
  have hCX : Subgroup.zpowers x ≤ X := (Subgroup.zpowers_le).mpr hx
  have hcard0 : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
  rcases lt_or_eq_of_le hCX with hlt | heq
  · have hsub : Subgroup.zpowers x ≤ sSup {Y : Subgroup G | Y < X} := le_sSup hlt
    exact hsub (Subgroup.mem_zpowers x)
  -- `X = ⟨x⟩` (巡回) の場合.
  have hnX : Nat.card ↥X = orderOf x := by rw [← heq, Nat.card_zpowers]
  have hone : Nat.card ↥X ≠ 1 := fun h1 =>
    h 2 Nat.prime_two (IsPGroup.of_card (n := 0) (by simpa using h1))
  obtain ⟨p, hp⟩ : (Nat.card ↥X).primeFactors.Nonempty := by
    refine Nat.nonempty_primeFactors.mpr ?_
    have := Nat.card_pos (α := ↥X)
    omega
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ (Nat.card ↥X).primeFactors, q ≠ p := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥X → r = p := fun r hr hrd =>
      hcon r (Nat.mem_primeFactors.mpr ⟨hr, hrd, hcard0⟩)
    exact h p (Nat.prime_of_mem_primeFactors hp)
      (IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hcard0
        (fun {r} hr hrd => hall r hr hrd)))
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hpd : p ∣ orderOf x := hnX ▸ Nat.dvd_of_mem_primeFactors hp
  have hqd : q ∣ orderOf x := hnX ▸ Nat.dvd_of_mem_primeFactors hq
  have hltp : Subgroup.zpowers (x ^ p) < X := by
    rw [← heq]; exact zpowers_pow_lt_zpowers hpp.one_lt hpd
  have hltq : Subgroup.zpowers (x ^ q) < X := by
    rw [← heq]; exact zpowers_pow_lt_zpowers hqq.one_lt hqd
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqq).mpr (Ne.symm hqp)
  have hsub : Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers (x ^ q)
      ≤ sSup {Y : Subgroup G | Y < X} := sup_le (le_sSup hltp) (le_sSup hltq)
  exact hsub (mem_sup_zpowers_of_coprime (x := x) hcop)

section /- 9D: Theorem 9.28 (Bartels) — Step 1 (p. 291) -/

/-- `X ≤ K` のとき, `X^{(K)}` を `↥K` に降ろすと `↥K` の中の `X^{(↥K)}` に一致する。 -/
theorem strongClosureIn_subgroupOf {K X : Subgroup G} (hXK : X ≤ K) :
    (strongClosureIn K X).subgroupOf K = strongClosure (X.subgroupOf K) := by
  rw [strongClosureIn_eq_map_strongClosure hXK, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

/-- 有限群の真部分群は位数が真に小さい。 -/
theorem card_lt_of_ne_top [Finite G] {K : Subgroup G} (hK : K ≠ ⊤) :
    Nat.card ↥K < Nat.card G := by
  have hmul := Subgroup.card_mul_index K
  have hidx : K.index ≠ 1 := fun h1 => hK (Subgroup.index_eq_one.mp h1)
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have h2 : 1 < K.index := by omega
  calc Nat.card ↥K < Nat.card ↥K * K.index := (Nat.lt_mul_iff_one_lt_right hpos).mpr h2
    _ = Nat.card G := hmul

/-- **Bartels (9.28) の帰納法の仮定**: `G` より真に位数の小さい群では `X^{(H)}` は subnormal。 -/
def BartelsIH (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    ∀ Y : Subgroup H, (strongClosure Y).IsSubnormal

/-- **Bartels (9.28) Step 1, 片側** (書籍 p. 291): `Y, Z ≤ H` が `Y^{(H)} = Z^{(H)}` を
みたし, `Y^{(G)} ≠ G` なら `Y^{(G)} ≤ Z^{(G)}`.

書籍は `Y, Z` を `X` の共役に取るが, 共役性は `Y^{(G)} < G` を出すためだけに使われる
ので, ここでは `Y^{(G)} ≠ ⊤` を直接の仮定にして一般化した。

**証明** (書籍 p.291): `K = Y^{(G)}`, `U = Y^{(H)} = Z^{(H)}` とおく。
`Z ≤ U ≤ K` で `K < G` なので帰納法の仮定から `Z^{(K)}` は `K` の中で subnormal。
9.29(d) で `U = Z^{(U)}` なので `Y ≤ U = Z^{(U)} ≤ Z^{(K)}` (9.29(c))。
9.29(a) を `K` の中で使って `Y^{(K)} ≤ Z^{(K)}`, 最後に `K = Y^{(K)}` (9.29(d)) と
`Z^{(K)} ≤ Z^{(G)}` (9.29(c)) を繋ぐ。 -/
theorem bartels_step_one_le {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {Y Z H : Subgroup G} (hYH : Y ≤ H) (hZH : Z ≤ H)
    (hU : strongClosureIn H Y = strongClosureIn H Z)
    (hK : strongClosure Y ≠ ⊤) :
    strongClosure Y ≤ strongClosure Z := by
  -- `Z ≤ U ≤ K`  (`U = Y^{(H)}`, `K = Y^{(G)}`).
  have hZU : Z ≤ strongClosureIn H Y := by rw [hU]; exact le_strongClosureIn hZH
  have hUK : strongClosureIn H Y ≤ strongClosure Y := strongClosureIn_le H Y
  have hZK : Z ≤ strongClosure Y := hZU.trans hUK
  -- 帰納法の仮定を `↥K` に適用: `Z^{(K)}` は `K` の中で subnormal.
  have hZKsub :
      ((strongClosureIn (strongClosure Y) Z).subgroupOf (strongClosure Y)).IsSubnormal := by
    rw [strongClosureIn_subgroupOf hZK]
    exact hIH ↥(strongClosure Y) (card_lt_of_ne_top hK) _
  -- `U = Z^{(U)}` (9.29(d) 相対版).
  have hUZ : strongClosureIn (strongClosureIn H Y) Z = strongClosureIn H Y := by
    rw [hU]; exact strongClosureIn_strongClosureIn H Z
  -- `Y ≤ U = Z^{(U)} ≤ Z^{(K)}`.
  have hYZK : Y ≤ strongClosureIn (strongClosure Y) Z :=
    ((le_strongClosureIn hYH).trans hUZ.ge).trans (strongClosureIn_mono_left hUK)
  -- 9.29(a) を `K` の中で適用.
  have hstep : strongClosureIn (strongClosure Y) Y ≤ strongClosureIn (strongClosure Y) Z :=
    strongClosureIn_le_of_isSubnormal hYZK (strongClosureIn_le_right _ Z) hZKsub
  calc strongClosure Y = strongClosureIn (strongClosure Y) Y := (strongClosureIn_self Y).symm
    _ ≤ strongClosureIn (strongClosure Y) Z := hstep
    _ ≤ strongClosure Z := strongClosureIn_le _ Z

/-- **Bartels (9.28) Step 1** (書籍 p. 291): `Y, Z ≤ H` が `Y^{(H)} = Z^{(H)}` をみたし
両者の `^{(G)}` が真部分群なら `Y^{(G)} = Z^{(G)}`. -/
theorem bartels_step_one {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {Y Z H : Subgroup G} (hYH : Y ≤ H) (hZH : Z ≤ H)
    (hU : strongClosureIn H Y = strongClosureIn H Z)
    (hKY : strongClosure Y ≠ ⊤) (hKZ : strongClosure Z ≠ ⊤) :
    strongClosure Y = strongClosure Z :=
  le_antisymm (bartels_step_one_le hIH hYH hZH hU hKY)
    (bartels_step_one_le hIH hZH hYH hU.symm hKZ)

end

/-- **Bartels (9.28) Step 2** (書籍 p. 291): 最小反例の `X` は `p`-群。

書籍の議論: `X` が `p`-群でなければ真部分群たちで生成される。
`U = ⟨Y^{(G)} | Y < X⟩` とおくと `X ≤ U ≤ X^{(G)}` (9.29(b))。`|X|` 最小性から各
`Y^{(G)}` は subnormal なので, Wielandt 結合定理の族版で `U ◁◁ G`。すると 9.29(a) で
`X^{(G)} ≤ U`, 逆包含と合わせて `X^{(G)} = U ◁◁ G` となり `X` が反例であることに矛盾。 -/
theorem bartels_step_two {G : Type u} [Group G] [Finite G] {X : Subgroup G}
    (hXmin : ∀ Y : Subgroup G, Y < X → (strongClosure Y).IsSubnormal)
    (hX : ¬ (strongClosure X).IsSubnormal) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥X := by
  by_contra hcon
  push Not at hcon
  -- `U = ⟨Y^{(G)} | Y < X⟩`.
  set U : Subgroup G := sSup (strongClosure '' {Y : Subgroup G | Y < X}) with hUdef
  -- `X ≤ U` (真部分群で生成され, 各 `Y ≤ Y^{(G)}`).
  have hXU : X ≤ U := by
    refine (le_sSup_lt_of_forall_not_isPGroup hcon).trans (sSup_le ?_)
    intro Y hY
    exact (le_strongClosure Y).trans (le_sSup ⟨Y, hY, rfl⟩)
  -- `U ≤ X^{(G)}` (9.29(b)).
  have hUX : U ≤ strongClosure X := by
    refine sSup_le ?_
    rintro _ ⟨Y, hY, rfl⟩
    exact strongClosure_mono hY.le
  -- `U ◁◁ G` (Wielandt 結合定理の族版 + `|X|` 最小性).
  have hUsub : U.IsSubnormal := by
    refine OddOrder.Isaacs.Ch02.isSubnormal_sSup_of_isSubnormal ?_
    rintro _ ⟨Y, hY, rfl⟩
    exact hXmin Y hY
  -- 9.29(a) で `X^{(G)} ≤ U`, ゆえ `X^{(G)} = U ◁◁ G` で矛盾.
  exact hX (le_antisymm (strongClosure_le_of_isSubnormal hUsub X hXU) hUX ▸ hUsub)

/-- **Bartels (9.28) Step 3** (書籍 p. 291): `Y ≤ H < G` (`Y` は `p`-群) と `H` の
Sylow `p`-部分群 `P` に対し, `Y` の共役 `Z ≤ P` で `Z^{(H)} = Y^{(H)}` となるものが取れる。

書籍の議論: `H < G` なので帰納法の仮定で `L = Y^{(H)}` は `H` の中で subnormal。
Lem 9.31 (相対版) で `P ⊓ L` は `L` の Sylow `p`。`Y` は `L` の `p`-部分群なので
`h ∈ L` があって `Y^h ≤ P ⊓ L`。`h ∈ L ≤ H` より `H^h = H`, `L^h = L` なので
`(Y^h)^{(H)} = (Y^{(H)})^h = L`。

(書籍の結論 `Y^{(G)} = Z^{(G)}` は Step 1 を繋げば出る。) -/
theorem bartels_step_three {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {Y H P : Subgroup G} (hYH : Y ≤ H) (hH : H ≠ ⊤)
    (hY : IsPGroup p ↥Y) (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex H) :
    ∃ h ∈ H, ConjAct.toConjAct h • Y ≤ P ∧
      strongClosureIn H (ConjAct.toConjAct h • Y) = strongClosureIn H Y := by
  have hYL : Y ≤ strongClosureIn H Y := le_strongClosureIn hYH
  have hLH : strongClosureIn H Y ≤ H := strongClosureIn_le_right H Y
  -- `Y^{(H)}` は `H` の中で subnormal (帰納法の仮定を ↥H に適用).
  have hLsub : ((strongClosureIn H Y).subgroupOf H).IsSubnormal := by
    rw [strongClosureIn_subgroupOf hYH]
    exact hIH ↥H (card_lt_of_ne_top hH) _
  -- 9.31 相対版: `P ⊓ Y^{(H)}` は `Y^{(H)}` の Sylow `p`.
  have hPL : ¬ p ∣ (P ⊓ strongClosureIn H Y).relIndex (strongClosureIn H Y) :=
    not_dvd_relIndex_inf_of_isSubnormal_in hLH hLsub hP hPidx
  have hPLp : IsPGroup p ↥(P ⊓ strongClosureIn H Y) :=
    hP.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  -- `Y` を `P ⊓ Y^{(H)}` の中へ共役で送る.
  obtain ⟨h, hhL, hhY⟩ :=
    exists_mem_conjAct_smul_le_of_isPGroup hYL inf_le_right hY hPLp hPL
  refine ⟨h, hLH hhL, hhY.trans inf_le_left, ?_⟩
  have hHfix : ConjAct.toConjAct h • H = H := conjAct_smul_self_of_mem (hLH hhL)
  have hLfix : ConjAct.toConjAct h • strongClosureIn H Y = strongClosureIn H Y :=
    conjAct_smul_self_of_mem hhL
  calc strongClosureIn H (ConjAct.toConjAct h • Y)
      = strongClosureIn (ConjAct.toConjAct h • H) (ConjAct.toConjAct h • Y) := by rw [hHfix]
    _ = ConjAct.toConjAct h • strongClosureIn H Y := strongClosureIn_conjAct_smul _ _ _
    _ = strongClosureIn H Y := hLfix

section /- 9D: Bartels Step 4 の道具 — 集合 `𝒦(H)` と共役作用 -/

/-- **`𝒦(H)`** (Isaacs p. 291 の証明中の記法): `H` に含まれる `X` の共役 `Y` たちの
`Y^{(G)}` 全体からなる集合。Step 4 は `G` の `𝒦(M)` への共役作用の stabilizer を見る。 -/
def kappaSet (X H : Subgroup G) : Set (Subgroup G) :=
  {W | ∃ Y : Subgroup G, Y ≤ H ∧ (∃ c : ConjAct G, c • X = Y) ∧ strongClosure Y = W}

theorem mem_kappaSet_self (X : Subgroup G) {H : Subgroup G} (hXH : X ≤ H) :
    strongClosure X ∈ kappaSet X H :=
  ⟨X, hXH, ⟨1, one_smul _ _⟩, rfl⟩

/-- `𝒦` は `H` について単調。 -/
theorem kappaSet_mono {X H K : Subgroup G} (hHK : H ≤ K) : kappaSet X H ⊆ kappaSet X K := by
  rintro W ⟨Y, hYH, hYc, rfl⟩
  exact ⟨Y, hYH.trans hHK, hYc, rfl⟩

/-- **`𝒦` の共役同変性**: `W ∈ 𝒦(H)` なら `W^g ∈ 𝒦(H^g)`。

書籍 p.291 の「`(Y^{(G)})^h = (Y^h)^{(G)}` ゆえ `H` は `𝒦(H)` に共役で作用する」。 -/
theorem mem_kappaSet_conjAct_smul {c : ConjAct G} {X H W : Subgroup G}
    (hW : W ∈ kappaSet X H) : c • W ∈ kappaSet X (c • H) := by
  obtain ⟨Y, hYH, ⟨d, rfl⟩, rfl⟩ := hW
  refine ⟨c • (d • X), Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYH, ⟨c * d, ?_⟩, ?_⟩
  · rw [mul_smul]
  · exact strongClosure_conjAct_smul c _


/-- 共役は `p`-群性を保つ。 -/
theorem isPGroup_conjAct_smul {p : ℕ} {X : Subgroup G} (hX : IsPGroup p ↥X) (c : ConjAct G) :
    IsPGroup p ↥(c • X) :=
  hX.of_injective (Subgroup.equivSMul c X).symm.toMonoidHom
    (Subgroup.equivSMul c X).symm.injective

/-- **`H` は `𝒦(H)` に共役で作用する** (`h ∈ H` の場合)。 -/
theorem mem_kappaSet_smul_of_mem {X H W : Subgroup G} {h : G} (hh : h ∈ H)
    (hW : W ∈ kappaSet X H) : ConjAct.toConjAct h • W ∈ kappaSet X H := by
  have := mem_kappaSet_conjAct_smul (c := ConjAct.toConjAct h) hW
  rwa [conjAct_smul_self_of_mem hh] at this

/-- **Step 4 の下準備** (書籍 p. 291 「By Step 3, we also have `𝒦(M) = 𝒦(P)`」):
`H < G` と `H` の Sylow `p`-部分群 `P` に対し `𝒦(H) = 𝒦(P)`.

`⊇` は単調性。`⊆` は Step 3 で `Y` を `P` の中へ共役で送り, Step 1 で
`(Y^h)^{(G)} = Y^{(G)}` を得る。 -/
theorem kappaSet_eq_of_sylow {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {X H P : Subgroup G} (hH : H ≠ ⊤) (hPH : P ≤ H)
    (hXp : IsPGroup p ↥X) (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex H)
    (hne : ∀ c : ConjAct G, strongClosure (c • X) ≠ ⊤) :
    kappaSet X H = kappaSet X P := by
  refine Set.Subset.antisymm ?_ (kappaSet_mono hPH)
  rintro W ⟨Y, hYH, ⟨c, rfl⟩, rfl⟩
  obtain ⟨h, hhH, hhP, hheq⟩ :=
    bartels_step_three hIH hYH hH (isPGroup_conjAct_smul hXp c) hP hPidx
  have hne' : strongClosure (ConjAct.toConjAct h • (c • X)) ≠ ⊤ := by
    have := hne (ConjAct.toConjAct h * c)
    rwa [mul_smul] at this
  refine ⟨ConjAct.toConjAct h • (c • X), hhP, ⟨ConjAct.toConjAct h * c, (mul_smul _ _ _)⟩, ?_⟩
  exact bartels_step_one hIH (hhP.trans hPH) hYH hheq hne' (hne c)


end

section /- 9D: Bartels Step 4 — 第 1 分岐 (作用の核が非自明なら矛盾) -/

/-- 非自明な正規部分群による商は位数が真に小さい。 -/
theorem card_quotient_lt_of_ne_bot [Finite G] {K : Subgroup G} [K.Normal] (hK : K ≠ ⊥) :
    Nat.card (G ⧸ K) < Nat.card G := by
  have hmul := Subgroup.card_mul_index K
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card ↥K ≠ 1 := fun h1 => hK (Subgroup.eq_bot_of_card_eq K h1)
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have h2 : 1 < Nat.card ↥K := by omega
  have : K.index < Nat.card ↥K * K.index :=
    (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hidx0)).mpr h2
  rw [hmul] at this
  exact this

/-- **`S` の商での像が subnormal かつ `K` が `S` を正規化するなら `S ◁◁ G`**。

書籍 p.291 Step 4 の最後の一手 (`K·X^{(G)} ◁◁ G` かつ `X^{(G)} ◁ K·X^{(G)}`)。 -/
theorem isSubnormal_of_map_quotient {S K : Subgroup G} [K.Normal]
    (hnorm : K ≤ Subgroup.normalizer S)
    (hsub : (S.map (QuotientGroup.mk' K)).IsSubnormal) : S.IsSubnormal := by
  -- `K ⊔ S` は像の引き戻しなので subnormal.
  have hcomap : (S.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = S ⊔ K := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hLsub : (S ⊔ K).IsSubnormal := hcomap ▸ hsub.comap _
  -- `S ◁ (S ⊔ K)` (K も S も `S` を正規化する).
  have hle : S ≤ S ⊔ K := le_sup_left
  have hnormal : (S.subgroupOf (S ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (sup_le Subgroup.le_normalizer hnorm)
  exact Subgroup.IsSubnormal.step S (S ⊔ K) hle hLsub hnormal

/-- **Bartels Step 4 の第 1 分岐**: `G` の `𝒦(G)` への作用の核 `K` が非自明なら
`X^{(G)}` は subnormal (= 最小反例の仮定に矛盾)。

`|G/K| < |G|` なので帰納法の仮定と Lem 9.30 で `X^{(G)}` の像が `Ḡ` で subnormal,
`K` は `X^{(G)}` を正規化するので上の補題が使える。 -/
theorem isSubnormal_strongClosure_of_normalizing_kernel {G : Type u} [Group G] [Finite G]
    (hIH : BartelsIH G) {X K : Subgroup G} [K.Normal] (hK : K ≠ ⊥)
    (hnorm : K ≤ Subgroup.normalizer (strongClosure X)) :
    (strongClosure X).IsSubnormal := by
  refine isSubnormal_of_map_quotient hnorm ?_
  rw [strongClosure_map X (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)]
  exact hIH (G ⧸ K) (card_quotient_lt_of_ne_bot hK) _

/-- `z` が `Y` を中心化するなら `Y^z = Y`。 -/
theorem conjAct_smul_eq_self_of_mem_centralizer {Y : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.centralizer (Y : Set G)) : ConjAct.toConjAct z • Y = Y := by
  refine Subgroup.conjAct_pointwise_smul_eq_self ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hcomm : ∀ w ∈ Y, w * z = z * w := fun w hw => Subgroup.mem_centralizer_iff.mp hz w hw
  constructor
  · intro hy
    have := hcomm y hy
    rw [show z * y * z⁻¹ = y by rw [← this]; group]
    exact hy
  · intro hy
    -- `w = z * y * z⁻¹ ∈ Y` は `z` と可換なので `y = w ∈ Y`.
    have h3 : z * y = z * (z * y * z⁻¹) := by rw [← hcomm _ hy]; group
    rw [mul_left_cancel h3]
    exact hy

/-- **`Z(P)` は `𝒦(P)` に自明に作用する** (書籍 p.291 Step 4)。

`W ∈ 𝒦(P)` は `Y ≤ P` の `Y^{(G)}`。`z` が `P` を中心化すれば `Y^z = Y` なので
`W^z = (Y^z)^{(G)} = W`。 -/
theorem conjAct_smul_eq_self_of_mem_centralizer_of_mem_kappaSet {X P : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.centralizer (P : Set G)) {W : Subgroup G} (hW : W ∈ kappaSet X P) :
    ConjAct.toConjAct z • W = W := by
  obtain ⟨Y, hYP, _, rfl⟩ := hW
  have hzY : ConjAct.toConjAct z • Y = Y := by
    refine conjAct_smul_eq_self_of_mem_centralizer ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp hz w (hYP hw)
  rw [← strongClosure_conjAct_smul, hzY]

end

section /- 9D: Bartels Step 4 — 作用の核 (各点固定部分群) -/

/-- 共役作用は `⊤` を固定する。 -/
@[simp] theorem conjAct_smul_top (c : ConjAct G) : c • (⊤ : Subgroup G) = ⊤ := by
  rw [Subgroup.pointwise_smul_def]
  exact Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulEquiv G c).surjective

/-- 部分群の集合 `S` を**各点固定**する元のなす部分群 (= `S` への共役作用の核)。 -/
def pointwiseStabilizer (S : Set (Subgroup G)) : Subgroup G where
  carrier := {g : G | ∀ W ∈ S, ConjAct.toConjAct g • W = W}
  one_mem' := by intro W _; simp
  mul_mem' := by
    intro a b ha hb W hW
    rw [map_mul, mul_smul, hb W hW, ha W hW]
  inv_mem' := by
    intro a ha W hW
    rw [map_inv, inv_smul_eq_iff, ha W hW]

theorem mem_pointwiseStabilizer_iff {S : Set (Subgroup G)} {g : G} :
    g ∈ pointwiseStabilizer S ↔ ∀ W ∈ S, ConjAct.toConjAct g • W = W := Iff.rfl

/-- 各点固定元は各 `W ∈ S` を正規化する。 -/
theorem mem_normalizer_of_mem_pointwiseStabilizer {S : Set (Subgroup G)} {g : G}
    (hg : g ∈ pointwiseStabilizer S) {W : Subgroup G} (hW : W ∈ S) :
    g ∈ Subgroup.normalizer W :=
  Subgroup.conjAct_pointwise_smul_iff.mp (hg W hW)

/-- `S` が共役で閉じていれば各点固定部分群は正規。 -/
theorem pointwiseStabilizer_normal {S : Set (Subgroup G)}
    (hS : ∀ (c : ConjAct G) (W : Subgroup G), W ∈ S → c • W ∈ S) :
    (pointwiseStabilizer S).Normal := by
  constructor
  intro g hg h W hW
  have hW' : (ConjAct.toConjAct h)⁻¹ • W ∈ S := hS _ W hW
  have hfix := hg _ hW'
  have : ConjAct.toConjAct (h * g * h⁻¹) • W
      = ConjAct.toConjAct h • (ConjAct.toConjAct g • ((ConjAct.toConjAct h)⁻¹ • W)) := by
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul]
  rw [this, hfix, smul_inv_smul]

/-- `𝒦(G)` は共役で閉じている。 -/
theorem kappaSet_top_conjAct_smul_mem (X : Subgroup G) (c : ConjAct G) (W : Subgroup G)
    (hW : W ∈ kappaSet X ⊤) : c • W ∈ kappaSet X ⊤ := by
  have := mem_kappaSet_conjAct_smul (c := c) hW
  rwa [conjAct_smul_top] at this

/-- したがって `𝒦(G)` への作用の核は正規部分群。 -/
instance kappaSetKernel_normal (X : Subgroup G) :
    (pointwiseStabilizer (kappaSet X ⊤)).Normal :=
  pointwiseStabilizer_normal (kappaSet_top_conjAct_smul_mem X)

/-- **Step 4 第 1 分岐への接続**: `𝒦(G)` への作用の核が非自明なら `X^{(G)} ◁◁ G`
(= 最小反例の仮定に矛盾)。 -/
theorem isSubnormal_strongClosure_of_kappaSetKernel_ne_bot {G : Type u} [Group G] [Finite G]
    (hIH : BartelsIH G) {X : Subgroup G}
    (hK : pointwiseStabilizer (kappaSet X ⊤) ≠ ⊥) :
    (strongClosure X).IsSubnormal :=
  isSubnormal_strongClosure_of_normalizing_kernel hIH hK fun _ hg =>
    mem_normalizer_of_mem_pointwiseStabilizer hg (mem_kappaSet_self X le_top)

end

section /- 9D: Bartels Step 4 — 集合としての stabilizer と極大性の二分岐 -/

/-- 部分群の集合 `S` を**集合として保つ**元のなす部分群。 -/
def setwiseStabilizer (S : Set (Subgroup G)) : Subgroup G where
  carrier := {g : G | ∀ W : Subgroup G, ConjAct.toConjAct g • W ∈ S ↔ W ∈ S}
  one_mem' := by intro W; simp
  mul_mem' := by
    intro a b ha hb W
    rw [map_mul, mul_smul, ha, hb]
  inv_mem' := by
    intro a ha W
    rw [map_inv, ← ha ((ConjAct.toConjAct a)⁻¹ • W), smul_inv_smul]

theorem mem_setwiseStabilizer_iff {S : Set (Subgroup G)} {g : G} :
    g ∈ setwiseStabilizer S ↔ ∀ W : Subgroup G, ConjAct.toConjAct g • W ∈ S ↔ W ∈ S := Iff.rfl

/-- **`H` は `𝒦(H)` を保つ** (書籍 p.291 「`H` acts by conjugation on `𝒦(H)`」)。 -/
theorem le_setwiseStabilizer_kappaSet (X H : Subgroup G) :
    H ≤ setwiseStabilizer (kappaSet X H) := by
  intro h hh W
  constructor
  · intro hW
    have := mem_kappaSet_smul_of_mem (X := X) (H := H) (h := h⁻¹) (H.inv_mem hh) hW
    rwa [map_inv, inv_smul_smul] at this
  · exact mem_kappaSet_smul_of_mem hh

/-- `𝒦(G)` は `G` の 1 つの軌道 (書籍 p.291 「`G` acts transitively on `𝒦(G)`」)。 -/
theorem mem_kappaSet_top_iff {X W : Subgroup G} :
    W ∈ kappaSet X ⊤ ↔ ∃ c : ConjAct G, c • strongClosure X = W := by
  constructor
  · rintro ⟨Y, -, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (strongClosure_conjAct_smul c X).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • X, le_top, ⟨c, rfl⟩, ?_⟩
    exact strongClosure_conjAct_smul c X

/-- **Step 4 第 1 分岐の入口**: `G` 全体が `𝒦(H)` を保つなら `𝒦(H) = 𝒦(G)`.

`𝒦(G)` は `X^{(G)}` の `G`-軌道なので, `X^{(G)} ∈ 𝒦(H)` かつ `𝒦(H)` が `G`-安定なら
軌道全体を含む。(`X ≤ H` でなく `X^{(G)} ∈ 𝒦(H)` を仮定するのは, Step 4 後半で
`H = P` (Sylow) に対して使うため — そこでは `X ≤ P` は成り立たない。) -/
theorem kappaSet_eq_top_of_setwiseStabilizer_eq_top {X H : Subgroup G}
    (hmem : strongClosure X ∈ kappaSet X H)
    (hstab : setwiseStabilizer (kappaSet X H) = ⊤) : kappaSet X H = kappaSet X ⊤ := by
  refine Set.Subset.antisymm (kappaSet_mono le_top) ?_
  intro W hW
  obtain ⟨c, rfl⟩ := mem_kappaSet_top_iff.mp hW
  have hg : ConjAct.ofConjAct c ∈ setwiseStabilizer (kappaSet X H) := by
    rw [hstab]; exact Subgroup.mem_top _
  have := (hg (strongClosure X)).mpr hmem
  rwa [ConjAct.toConjAct_ofConjAct] at this


/-- **`N_G(P)` は `𝒦(P)` を保つ** (書籍 p.291 「this set is stabilized by `N_G(P)`」)。 -/
theorem normalizer_le_setwiseStabilizer_kappaSet (X P : Subgroup G) :
    Subgroup.normalizer P ≤ setwiseStabilizer (kappaSet X P) := by
  intro g hg W
  have hP : ConjAct.toConjAct g • P = P := Subgroup.conjAct_pointwise_smul_iff.mpr hg
  have hPinv : (ConjAct.toConjAct g)⁻¹ • P = P := by
    rw [inv_smul_eq_iff, hP]
  constructor
  · intro hW
    have := mem_kappaSet_conjAct_smul (c := (ConjAct.toConjAct g)⁻¹) hW
    rwa [inv_smul_smul, hPinv] at this
  · intro hW
    have := mem_kappaSet_conjAct_smul (c := ConjAct.toConjAct g) hW
    rwa [hP] at this

/-- **`C_G(P)` は `𝒦(P)` を各点固定する** (書籍 p.291 の `Z(P)` の部分)。 -/
theorem centralizer_le_pointwiseStabilizer_kappaSet (X P : Subgroup G) :
    Subgroup.centralizer (P : Set G) ≤ pointwiseStabilizer (kappaSet X P) :=
  fun _ hz _ hW => conjAct_smul_eq_self_of_mem_centralizer_of_mem_kappaSet hz hW

/-- **極大部分群の二分岐**: `M` が極大で `M ≤ K` なら `K = M` または `K = ⊤`. -/
theorem eq_or_eq_top_of_isCoatom {M K : Subgroup G} (hM : IsCoatom M) (hMK : M ≤ K) :
    K = M ∨ K = ⊤ := by
  rcases lt_or_eq_of_le hMK with hlt | heq
  · exact Or.inr (hM.2 K hlt)
  · exact Or.inl heq.symm

end

section /- 9D: Bartels Step 4 — `N_G(P) ≤ M` から `P ∈ Syl_p(G)` を出す道具 -/

/-- `R` が `p`-群で `P < R` なら `p ∣ |R : P|`. -/
theorem dvd_relIndex_of_lt_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {P R : Subgroup G}
    (hR : IsPGroup p ↥R) (hlt : P < R) : p ∣ P.relIndex R := by
  change p ∣ (P.subgroupOf R).index
  have hne : P.subgroupOf R ≠ ⊤ := fun h => by
    rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd (lt_of_lt_of_le hlt h) (lt_irrefl P)
  have hidx1 : (P.subgroupOf R).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hR
  have hdvd : (P.subgroupOf R).index ∣ p ^ n := hn ▸ Subgroup.index_dvd_card (P.subgroupOf R)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero] at hk; exact absurd hk hidx1
  · rw [hk]; exact dvd_pow_self p hkpos.ne'

end

/-- **正規化条件を ambient へ持ち上げる**: `S ≤ K` で `x ∈ K` が `↥K` の中で
`S.subgroupOf K` を正規化するなら `x` は `G` の中で `S` を正規化する。

`K` の外の `y` については `y ∉ S` かつ `x y x⁻¹ ∉ K ⊇ S` なので条件は両辺とも偽で自明。 -/
theorem mem_normalizer_of_mem_normalizer_subgroupOf {K S : Subgroup G} (hSK : S ≤ K)
    {x : ↥K} (hx : x ∈ Subgroup.normalizer (S.subgroupOf K)) :
    (x : G) ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hyK : y ∈ K := hSK hy
    have hmem : (⟨y, hyK⟩ : ↥K) ∈ S.subgroupOf K := hy
    have hres := (Subgroup.mem_normalizer_iff.mp hx ⟨y, hyK⟩).mp hmem
    simpa [Subgroup.mem_subgroupOf] using hres
  · intro hy
    have hyK : y ∈ K := by
      have h1 : (x : G) * y * (x : G)⁻¹ ∈ K := hSK hy
      have hrw : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) := by group
      rw [hrw]
      exact mul_mem (mul_mem (inv_mem x.2) h1) x.2
    have hres := (Subgroup.mem_normalizer_iff.mp hx ⟨y, hyK⟩).mpr
      (by simpa [Subgroup.mem_subgroupOf] using hy)
    simpa [Subgroup.mem_subgroupOf] using hres

/-- **`p`-群の中では真部分群の正規化群が真に大きい** (冪零群の normalizer condition):
`S < P` で `P` が `p`-群なら `S < P ⊓ N_G(S)`。

Step 4 の Sylow 結論部と Step 5 の「`R ⊓ P > S`」の両方で使う。 -/
theorem lt_inf_normalizer_of_lt_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {S P : Subgroup G}
    (hP : IsPGroup p ↥P) (hlt : S < P) : S < P ⊓ Subgroup.normalizer S := by
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hsub : S.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd (lt_of_lt_of_le hlt h) (lt_irrefl S)
  obtain ⟨x, hxN, hxS⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hsub)
  refine lt_of_le_of_ne (le_inf hlt.le Subgroup.le_normalizer) fun heq => hxS ?_
  have hxmem : (x : G) ∈ P ⊓ Subgroup.normalizer S :=
    ⟨x.2, mem_normalizer_of_mem_normalizer_subgroupOf hlt.le hxN⟩
  rw [← heq] at hxmem
  exact hxmem

/-- **Step 4 の Sylow 結論部**: `P` が `M` の Sylow `p`-部分群で `N_G(P) ≤ M` なら
`P` は `G` の Sylow `p`-部分群 (指数が `p` と互いに素)。

`P ≤ Q ∈ Syl_p(G)` を取る。`P < Q` なら `Q` は `p`-群 (ゆえ nilpotent) なので正規化条件から
`N_Q(P) > P`, その元は `N_G(P) ≤ M` に入るので `M` の中に `P` より真に大きい `p`-部分群
ができ, `dvd_relIndex_of_lt_of_isPGroup` で `p ∣ |M : P|` となって矛盾。 -/
theorem not_dvd_index_of_normalizer_le {p : ℕ} [Fact p.Prime] [Finite G]
    {M P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex M)
    (hN : Subgroup.normalizer P ≤ M) : ¬ p ∣ P.index := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hPQeq : P = (Q : Subgroup G) := by
    by_contra hne
    have hlt : P < (Q : Subgroup G) := lt_of_le_of_ne hPQ hne
    obtain ⟨x, ⟨hxQ, hxN⟩, hxP⟩ :=
      SetLike.exists_of_lt (lt_inf_normalizer_of_lt_of_isPGroup Q.isPGroup' hlt)
    -- `R = P ⊔ ⟨x⟩` は `M` の中の `P` より真に大きい `p`-部分群.
    have hxM : x ∈ M := hN hxN
    set R : Subgroup G := P ⊔ Subgroup.zpowers x with hRdef
    have hRQ : R ≤ (Q : Subgroup G) := sup_le hPQ ((Subgroup.zpowers_le).mpr hxQ)
    have hRM : R ≤ M := sup_le hPM ((Subgroup.zpowers_le).mpr hxM)
    have hPR : P < R := by
      refine lt_of_le_of_ne le_sup_left fun heq => hxP ?_
      have : x ∈ R := (le_sup_right : Subgroup.zpowers x ≤ R) (Subgroup.mem_zpowers _)
      rwa [← heq] at this
    have hRp : IsPGroup p ↥R := Q.isPGroup'.to_le hRQ
    have hdvd : p ∣ P.relIndex R := dvd_relIndex_of_lt_of_isPGroup hRp hPR
    have hchain : P.relIndex R * R.relIndex M = P.relIndex M :=
      Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hRM
    exact hPidx (hchain ▸ Dvd.dvd.mul_right hdvd _)
  rw [hPQeq]
  exact Q.not_dvd_index

/-- 非自明な有限 `p`-群 `P` の中心化群は非自明 (`Z(P) ≠ 1` から)。 -/
theorem centralizer_ne_bot_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {P : Subgroup G}
    (hP : IsPGroup p ↥P) (hPbot : P ≠ ⊥) : Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPbot
  haveI := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  refine fun hbot => hz ?_
  have hmem : ((z : ↥P) : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩
    exact congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at hmem
  ext
  simpa using hmem

/-- **Bartels Step 4 の核心** (書籍 pp. 292-293): 最小反例の下で `H` が極大部分群,
`P ∈ Syl_p(H)`, かつ `X^{(G)} ∈ 𝒦(P)` ならば **`𝒦(P)` の setwise stabilizer はちょうど
`H`**。

`H ≤ Stab(𝒦(H))` で `𝒦(H) = 𝒦(P)` (Step 3) なので, `H` の極大性から stabilizer は
`H` か `⊤` の二択。`⊤` の場合は `𝒦(P) = 𝒦(G)` となり, `Z(P) ≤ C_G(P) (≠ 1)` が
`𝒦(G)` への作用の核に入るので `X^{(G)}` が subnormal となり最小反例の仮定に矛盾。

書籍が Step 4 の前半 (`P ∈ Syl_p(G)`) と後半 (`M` の一意性) で 2 度使う議論なので,
`H` を動かせる形で切り出してある。 -/
theorem setwiseStabilizer_kappaSet_eq_of_isCoatom {G : Type u} [Group G] [Finite G]
    (hIH : BartelsIH G) {p : ℕ} [Fact p.Prime] {X H P : Subgroup G}
    (hH : IsCoatom H) (hXp : IsPGroup p ↥X)
    (hPH : P ≤ H) (hPp : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex H) (hPbot : P ≠ ⊥)
    (hmem : strongClosure X ∈ kappaSet X P)
    (hne : ∀ c : ConjAct G, strongClosure (c • X) ≠ ⊤)
    (hXsub : ¬ (strongClosure X).IsSubnormal) :
    setwiseStabilizer (kappaSet X P) = H := by
  have hKHP : kappaSet X H = kappaSet X P :=
    kappaSet_eq_of_sylow hIH hH.1 hPH hXp hPp hPidx hne
  have hle : H ≤ setwiseStabilizer (kappaSet X P) := by
    rw [← hKHP]; exact le_setwiseStabilizer_kappaSet X H
  rcases eq_or_eq_top_of_isCoatom hH hle with hst | hst
  · exact hst
  · -- stabilizer = `G`: 矛盾.
    exfalso
    refine hXsub (isSubnormal_strongClosure_of_kappaSetKernel_ne_bot hIH ?_)
    rw [← kappaSet_eq_top_of_setwiseStabilizer_eq_top hmem hst]
    intro hbot
    exact centralizer_ne_bot_of_isPGroup hPp hPbot
      (le_bot_iff.mp (hbot ▸ centralizer_le_pointwiseStabilizer_kappaSet X P))

/-- `X ≤ M` と `𝒦(M) = 𝒦(P)` (Step 3) から `X^{(G)} ∈ 𝒦(P)`。 -/
theorem mem_kappaSet_sylow_of_le {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {X M P : Subgroup G}
    (hM : M ≠ ⊤) (hXM : X ≤ M) (hXp : IsPGroup p ↥X)
    (hPM : P ≤ M) (hPp : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex M)
    (hne : ∀ c : ConjAct G, strongClosure (c • X) ≠ ⊤) :
    strongClosure X ∈ kappaSet X P := by
  rw [← kappaSet_eq_of_sylow hIH hM hPM hXp hPp hPidx hne]
  exact mem_kappaSet_self X hXM

/-- **Bartels (9.28) Step 4, 前半** (書籍 pp. 292-293): `M` が `X` を含む極大部分群,
`P` が `M` の Sylow `p`-部分群なら `P` は `G` の Sylow `p`-部分群。

核心補題で `Stab(𝒦(P)) = M`。`N_G(P)` は `𝒦(P)` を保つので `N_G(P) ≤ M`, ゆえ
`not_dvd_index_of_normalizer_le` で結論。 -/
theorem bartels_step_four {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {X M P : Subgroup G}
    (hM : IsCoatom M) (hXM : X ≤ M) (hXp : IsPGroup p ↥X)
    (hPM : P ≤ M) (hPp : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex M) (hPbot : P ≠ ⊥)
    (hne : ∀ c : ConjAct G, strongClosure (c • X) ≠ ⊤)
    (hXsub : ¬ (strongClosure X).IsSubnormal) :
    ¬ p ∣ P.index := by
  have hmem := mem_kappaSet_sylow_of_le hIH hM.1 hXM hXp hPM hPp hPidx hne
  have hst := setwiseStabilizer_kappaSet_eq_of_isCoatom hIH hM hXp hPM hPp hPidx hPbot
    hmem hne hXsub
  exact not_dvd_index_of_normalizer_le hPM hPp hPidx
    (hst ▸ normalizer_le_setwiseStabilizer_kappaSet X P)

/-- **Bartels (9.28) Step 4, 後半** (書籍 p. 293): `M` は `P` を含む**唯一の**極大部分群。

書籍「Also if `P ⊆ N`, where `N` is maximal in `G`, then `P ∈ Syl_p(N)`, and similar
reasoning shows that `N` is the full stabilizer of `𝒦(P)`. Thus `N = M`.」

前半で `P ∈ Syl_p(G)` なので `P ≤ N` から `P ∈ Syl_p(N)` (指数の連鎖)。よって核心補題が
`N` にも適用でき, `N = Stab(𝒦(P)) = M`。 -/
theorem bartels_step_four_unique {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {X M P N : Subgroup G}
    (hM : IsCoatom M) (hXM : X ≤ M) (hXp : IsPGroup p ↥X)
    (hPM : P ≤ M) (hPp : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex M) (hPbot : P ≠ ⊥)
    (hne : ∀ c : ConjAct G, strongClosure (c • X) ≠ ⊤)
    (hXsub : ¬ (strongClosure X).IsSubnormal)
    (hN : IsCoatom N) (hPN : P ≤ N) :
    N = M := by
  have hmem := mem_kappaSet_sylow_of_le hIH hM.1 hXM hXp hPM hPp hPidx hne
  have hstM := setwiseStabilizer_kappaSet_eq_of_isCoatom hIH hM hXp hPM hPp hPidx hPbot
    hmem hne hXsub
  -- `P ∈ Syl_p(G)` (前半) から `P ∈ Syl_p(N)`.
  have hidx : ¬ p ∣ P.index :=
    bartels_step_four hIH hM hXM hXp hPM hPp hPidx hPbot hne hXsub
  have hPidxN : ¬ p ∣ P.relIndex N := fun h => hidx <| by
    rw [← Subgroup.relIndex_mul_index hPN]; exact h.mul_right _
  have hstN := setwiseStabilizer_kappaSet_eq_of_isCoatom hIH hN hXp hPN hPp hPidxN hPbot
    hmem hne hXsub
  exact hstN.symm.trans hstM

section /- 9D: Bartels Step 5 — `X` を含む極大部分群の一意性 -/

/-- **Step 5 の候補**: `S` は `X` を含み, かつ相異なる 2 つの極大部分群 `A`, `B` の共通部分
`A ⊓ B` の Sylow `p`-部分群である。

書籍 p. 293 はこの条件を満たす `S` のうち `|S|` が最大のものを選ぶ。本形式化では
**部分群順序に関する極大元**を取る — 用途は「`S` より真に大きい候補は存在しない」だけ
なので, 位数比較を経由する必要がない。 -/
def IsBartelsPairSylow (p : ℕ) (X S : Subgroup G) : Prop :=
  ∃ A B : Subgroup G, IsCoatom A ∧ IsCoatom B ∧ A ≠ B ∧
    X ≤ S ∧ S ≤ A ⊓ B ∧ IsPGroup p ↥S ∧ ¬ p ∣ S.relIndex (A ⊓ B)

/-- **Bartels (9.28) Step 5** (書籍 p. 293): 最小反例の `X` を含む極大部分群は一意。

背理法。`X` を含む相異なる極大部分群の対 `(A,B)` に対する `S ∈ Syl_p(A ⊓ B)` (`X ≤ S`)
のうち極大なものを取る (`IsBartelsPairSylow`)。
* `S ∈ Syl_p(G)` なら Step 4 後半 (`P` を含む極大部分群の一意性) で `A = B` となり矛盾。
* `S ◁ G` なら `X ◁◁ S ◁ G` ゆえ `X ◁◁ G`, Lem 9.29(a) で `X^{(G)} = X` が subnormal と
  なって最小反例の仮定に矛盾。よって `N_G(S) ≠ ⊤` で, `N_G(S) ≤ R` なる極大 `R` が取れる。
* `S ≤ P ∈ Syl_p(A)` は Step 4 前半で `Syl_p(G)` の元。`S ∉ Syl_p(G)` ゆえ `S < P` で,
  `p`-群の normalizer condition から `S < P ⊓ N_G(S) ≤ P ⊓ R ≤ A ⊓ R`。よって `A ⊓ R` の
  Sylow `p` は `S` より真に大きく, `S` の極大性から `A = R`。同様に `B = R` で `A = B`,
  これが矛盾。 -/
theorem bartels_step_five {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hXp : IsPGroup p ↥X) (hXbot : X ≠ ⊥)
    (hne : ∀ c : ConjAct G, strongClosure (c • X) ≠ ⊤)
    (hXsub : ¬ (strongClosure X).IsSubnormal)
    {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N) (hXM : X ≤ M) (hXN : X ≤ N) :
    M = N := by
  by_contra hMN
  haveI : Finite (Subgroup G) := Finite.of_injective _ (SetLike.coe_injective (A := Subgroup G))
  haveI : WellFoundedGT (Subgroup G) := Finite.to_wellFoundedGT
  have hcand : ∃ S : Subgroup G, IsBartelsPairSylow p X S := by
    obtain ⟨S, hXS, hSMN, hSp, hSidx⟩ := exists_sylow_ge_of_isPGroup (le_inf hXM hXN) hXp
    exact ⟨S, M, N, hM, hN, hMN, hXS, hSMN, hSp, hSidx⟩
  obtain ⟨S, hS, hSmax⟩ := exists_maximal_of_wellFoundedGT (IsBartelsPairSylow p X) hcand
  obtain ⟨A, B, hA, hB, hAB, hXS, hSAB, hSp, hSidx⟩ := hS
  have hSA : S ≤ A := hSAB.trans inf_le_left
  have hSB : S ≤ B := hSAB.trans inf_le_right
  have hSbot : S ≠ ⊥ := fun h => hXbot (le_bot_iff.mp (h ▸ hXS))
  -- (1) `S ∉ Syl_p(G)`: さもなくば Step 4 後半で `A = B`.
  have hSidxG : p ∣ S.index := by
    by_contra hdvd
    have hSA' : ¬ p ∣ S.relIndex A := fun h => hdvd <| by
      rw [← Subgroup.relIndex_mul_index hSA]; exact h.mul_right _
    exact hAB (bartels_step_four_unique hIH hA (hXS.trans hSA) hXp hSA hSp hSA' hSbot
      hne hXsub hB hSB).symm
  -- (2) `S` は `G` に normal でない: さもなくば `X ◁◁ G` で `X^{(G)} = X` が subnormal.
  have hNStop : Subgroup.normalizer (S : Set G) ≠ ⊤ := by
    intro htop
    haveI : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    haveI : Group.IsNilpotent ↥S := hSp.isNilpotent
    have hXsn : X.IsSubnormal :=
      Subgroup.IsSubnormal.trans hXS
        (OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite (X.subgroupOf S))
        ‹S.Normal›.isSubnormal
    have heq : strongClosure X = X :=
      le_antisymm (strongClosure_le_of_isSubnormal hXsn X le_rfl) (le_strongClosure X)
    refine hXsub ?_
    rw [heq]
    exact hXsn
  -- (3) `N_G(S)` を含む極大部分群 `R`.
  obtain ⟨R, hR, hNSR⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (S : Set G))).resolve_left hNStop
  have hSR : S ≤ R := Subgroup.le_normalizer.trans hNSR
  -- (4) `S` を含む任意の極大部分群 `C` について `C = R`.
  have key : ∀ C : Subgroup G, IsCoatom C → S ≤ C → C = R := by
    intro C hC hSC
    obtain ⟨P, hSP, hPC, hPp, hPidx⟩ := exists_sylow_ge_of_isPGroup hSC hSp
    have hPbot : P ≠ ⊥ := fun h => hSbot (le_bot_iff.mp (h ▸ hSP))
    -- `P ∈ Syl_p(G)` (Step 4 前半) なので `S ≠ P`, すなわち `S < P`.
    have hPG : ¬ p ∣ P.index :=
      bartels_step_four hIH hC (hXS.trans hSC) hXp hPC hPp hPidx hPbot hne hXsub
    have hSPlt : S < P := lt_of_le_of_ne hSP fun h => hPG (h ▸ hSidxG)
    -- `p`-群の normalizer condition: `S < P ⊓ N_G(S) ≤ P ⊓ R`.
    have hlt : S < P ⊓ R :=
      lt_of_lt_of_le (lt_inf_normalizer_of_lt_of_isPGroup hPp hSPlt) (inf_le_inf le_rfl hNSR)
    by_contra hCR
    -- `C ⊓ R` の Sylow `p` は `S` より真に大きい候補 — 極大性に矛盾.
    obtain ⟨S', hPRS', hS'CR, hS'p, hS'idx⟩ :=
      exists_sylow_ge_of_isPGroup (inf_le_inf hPC le_rfl) (hPp.to_le (inf_le_left : P ⊓ R ≤ P))
    have hSS' : S < S' := lt_of_lt_of_le hlt hPRS'
    have hS'cand : IsBartelsPairSylow p X S' :=
      ⟨C, R, hC, hR, hCR, hXS.trans hSS'.le, hS'CR, hS'p, hS'idx⟩
    exact hSS'.ne (le_antisymm hSS'.le (hSmax hS'cand hSS'.le))
  exact hAB ((key A hA hSA).trans (key B hB hSB).symm)

end

end OddOrder.Isaacs.Ch09

