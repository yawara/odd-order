/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems3BSolvability

/-!
# Isaacs Chapter 3 — Problems §3B (Schur-Zassenhaus と可解群)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3 の章末演習 §3B (pp. 84-86)。
§3B は Schur-Zassenhaus 定理 (Thm 3.8) と可解群 (Thm 3.11 / 3.12) を扱う節の演習。

本ファイルは **3B.4-3B.15**。前半 3B.1-3B.3 は
[`Problems3BSolvability.lean`](Problems3BSolvability.lean) (本ファイルが import)、
超可解群 (3B.7 / 3B.9 / 3B.10) は
[`ProblemsSupersolvable.lean`](ProblemsSupersolvable.lean) にある。

方針は Ch.1/Ch.2/§3A の `Problems*.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch03

open scoped commutatorElement

universe u v

section /- Problems 3B: Schur-Zassenhaus and solvable groups (pp. 84-86) -/

/-! ### Problem 3B.4 — 補群は与えられた小部分群を含むように取れる

`N ⊴ G` で `|N|` と `|G : N|` が互いに素, `U ≤ G` の位数が `|G : N|` を割り, `N` か `U` の
一方が可解なら, `U` を含む `N` の補群が存在する。Schur-Zassenhaus の存在部で補群 `K` を 1 つ
取り, D-part (`exists_conj_le_of_isComplement'_of_coprime'`) で `U ≤ K^x` となる共役を選べば,
`K^x` も `N` の補群 (`isComplement'_conj`)。 -/

/-- 正規部分群 `N` の補群の共役もまた `N` の補群 (`N` は共役で不変)。 -/
theorem isComplement'_conj {G : Type*} [Group G] {N K : Subgroup G} [hN : N.Normal]
    (hK : N.IsComplement' K) (x : G) :
    N.IsComplement' (K.map (MulAut.conj x).toMonoidHom) := by
  have hNconj : N.map (MulAut.conj x).toMonoidHom = N := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨?_, fun hy => ⟨x⁻¹ * y * x, ?_, by group⟩⟩
    · rintro ⟨n, hn, rfl⟩
      exact hN.conj_mem n hn x
    · simpa using hN.conj_mem y hy x⁻¹
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro g hgN hgKx
    obtain ⟨k, hk, hkg⟩ := hgKx
    have h1 : x⁻¹ * g * x ∈ N := by simpa using hN.conj_mem g hgN x⁻¹
    have h2 : x⁻¹ * g * x ∈ K := by
      have : x⁻¹ * (x * k * x⁻¹) * x = k := by group
      rw [← hkg]
      simpa [this] using hk
    have := Subgroup.disjoint_def.mp hK.disjoint h1 h2
    have hx : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
    rw [hx, this]; group
  · have hsup : N ⊔ K.map (MulAut.conj x).toMonoidHom = ⊤ := by
      conv_lhs => rw [← hNconj]
      rw [← Subgroup.map_sup, hK.sup_eq_top,
        Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective]
    rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]

/-- **Isaacs Problem 3B.4** (書籍 p. 84): `N ⊴ G` で `|N|` と `|G : N|` が互いに素とする.
`U ≤ G` の位数が `|G : N|` を割り, `N` と `U` の少なくとも一方が可解なら, `U` はある
`N` の補群 `H` に含まれる.

Schur-Zassenhaus の存在部 (`Subgroup.exists_right_complement'_of_coprime`) で補群 `K` を取り,
D-part (`exists_conj_le_of_isComplement'_of_coprime'`; 「`N` か `U` の一方が可解」版に一般化済)
で `U ≤ K^x` を与える `x` を選ぶ. `N` は正規なので `K^x` も補群 (`isComplement'_conj`). -/
theorem exists_isComplement'_le_of_coprime {G : Type u} [Group G] [Finite G] {N U : Subgroup G}
    [N.Normal] (hcop : Nat.Coprime (Nat.card ↥N) N.index) (hU : Nat.card ↥U ∣ N.index)
    (hsolv : Group.IsSolvable ↥N ∨ Group.IsSolvable ↥U) :
    ∃ H : Subgroup G, N.IsComplement' H ∧ U ≤ H := by
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcopU : Nat.Coprime (Nat.card ↥U) (Nat.card ↥N) :=
    Nat.Coprime.coprime_dvd_left hU hcop.symm
  obtain ⟨x, -, hx⟩ := exists_conj_le_of_isComplement'_of_coprime' hsolv hK hcopU
  exact ⟨K.map (MulAut.conj x).toMonoidHom, isComplement'_conj hK x, hx⟩

/-! ### Problem 3B.5 — 中心に含まれる Sylow p-部分群と p-正則元

`P ∈ Syl_p(G)` が `P ≤ Z(G)` を満たすとき, 位数が `p` で割れない元全体 `X` は部分群で
`G = X × P` (内部直積)。`P` は中心にあるので正規で, `|P|` と `|G : P|` は互いに素だから
Schur-Zassenhaus で補群 `X` が取れる。`P` が中心にあることから `X` は `G` で正規になり,
`g = x·u` (`x ∈ X`, `u ∈ P`) の分解と `o(x·u) = o(x)·o(u)` (可換 + 互いに素) から
`X` はちょうど p-正則元の集合。 -/

/-- **Isaacs Problem 3B.5** (書籍 p. 84): `P ∈ Syl_p(G)` が `P ≤ Z(G)` なら, 位数が `p` で
割り切れない元の集合 `X` は `G` の部分群であり, `G = X × P` (`X ⊴ G` かつ `X` は `P` の補群).

`X` が正規かつ `P` の補群であることが「`G = X × P` が内部直積」の内容 (`P ≤ Z(G)` ゆえ `P` も
正規で, 2 つの正規部分群が自明交叉かつ積が `G`). -/
theorem exists_subgroup_orderOf_not_dvd_isComplement' {G : Type u} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (P : Sylow p G) (hPZ : (P : Subgroup G) ≤ Subgroup.center G) :
    ∃ X : Subgroup G, (↑X : Set G) = {g : G | ¬ p ∣ orderOf g} ∧ X.Normal ∧
      (P : Subgroup G).IsComplement' X := by
  -- `P ≤ Z(G)` なので `P ⊴ G`.
  have hPnormal : (P : Subgroup G).Normal := by
    constructor
    intro n hn g
    have hc : g * n = n * g := Subgroup.mem_center_iff.mp (hPZ hn) g
    have : g * n * g⁻¹ = n := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hn
  -- Schur-Zassenhaus で補群 `X` を取る (`|P|` と `|G : P|` は互いに素).
  obtain ⟨X, hX⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  have hcardX : Nat.card ↥X = (P : Subgroup G).index := hX.symm.index_eq_card.symm
  have hidx : ¬ p ∣ (P : Subgroup G).index := P.not_dvd_index
  -- `X` の元の位数は `|X| = |G : P|` を割るので `p` と素.
  have hXp' : ∀ x ∈ X, ¬ p ∣ orderOf x := by
    intro x hxX hdvd
    have h1 : orderOf (⟨x, hxX⟩ : ↥X) ∣ Nat.card ↥X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hidx (dvd_trans hdvd (hcardX ▸ h1))
  -- `P` の元の位数は `p`-冪.
  have hPp : ∀ u ∈ (P : Subgroup G), ∃ k : ℕ, orderOf u ∣ p ^ k := by
    intro u huP
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, huP⟩
    refine ⟨k, orderOf_dvd_of_pow_eq_one ?_⟩
    simpa [Subgroup.orderOf_mk] using congrArg Subtype.val hk
  -- `G = X ⊔ P` の分解 `g = x * u`.
  have hdecomp : ∀ g : G, ∃ x ∈ X, ∃ u ∈ (P : Subgroup G), x * u = g := by
    intro g
    have hg : g ∈ X ⊔ (P : Subgroup G) := by rw [hX.symm.sup_eq_top]; trivial
    exact Subgroup.mem_sup_of_normal_right.mp hg
  refine ⟨X, ?_, ⟨?_⟩, hX⟩
  · -- `↑X = { g | p ∤ o(g) }`
    ext g
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
    refine ⟨hXp' g, fun hnd => ?_⟩
    obtain ⟨x, hxX, u, huP, rfl⟩ := hdecomp g
    -- `x` と `u` は可換で位数が互いに素なので `o(x*u) = o(x)*o(u)`.
    have hcomm : Commute x u := (Subgroup.mem_center_iff.mp (hPZ huP) x)
    obtain ⟨k, hk⟩ := hPp u huP
    have hcop : (orderOf x).Coprime (orderOf u) :=
      Nat.Coprime.coprime_dvd_right hk
        (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (hXp' x hxX)).symm)
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop] at hnd
    -- `p ∤ o(x)o(u)` から `o(u) = 1`, 即ち `u = 1`.
    have hpu : ¬ p ∣ orderOf u := fun h => hnd (h.mul_left _)
    have hu1 : orderOf u = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpu).symm) hk
    rw [orderOf_eq_one_iff.mp hu1, mul_one]
    exact hxX
  · -- `X ⊴ G` (`P` が中心にあるので共役は `X` の元による共役に帰着).
    intro n hn g
    obtain ⟨x, hxX, u, huP, rfl⟩ := hdecomp g
    have h1 : u * n = n * u := (Subgroup.mem_center_iff.mp (hPZ huP) n).symm
    have hcalc : x * u * n * (x * u)⁻¹ = x * n * x⁻¹ := by
      rw [mul_inv_rev]
      calc x * u * n * (u⁻¹ * x⁻¹) = x * (u * n) * u⁻¹ * x⁻¹ := by group
        _ = x * (n * u) * u⁻¹ * x⁻¹ := by rw [h1]
        _ = x * n * x⁻¹ := by group
    rw [hcalc]
    exact X.mul_mem (X.mul_mem hxX hn) (X.inv_mem hxX)

/-! ### Problem 3B.6 — 剰余類 `Ng` の中の「π-元」代表

`N ⊴ G`, `g ∈ G` で `Ng ∈ G/N` の位数を `m` とする。
(a) `Ng` の中に「位数の素因数がすべて `m` を割る」元 `h` が取れる。
(b) さらに `m` と `|N|` が互いに素なら `o(h) = m` ちょうど。

教科書の hint は「`π` を `m` の素因数の集合として `NC = N⟨g⟩` なる巡回 π-部分群 `C` を取れ」。
ここでは `⟨g⟩` (可換ゆえ可解) に Hall E-定理 (`hall_E_exists`) を当てて `|⟨g⟩| = k · s`
(`k` は π-数, `s` は π'-数) の分解を得, 中国剰余定理で `t ≡ 1 (mod m)`, `t ≡ 0 (mod s)`
なる `t` を取って `h := g ^ t` とする。 -/

/-- **Isaacs Problem 3B.6(a)** (書籍 p. 84): `N ⊴ G` とし `Ng ∈ G ⧸ N` の位数を `m` とすると,
剰余類 `Ng` の中に「位数の素因数がすべて `m` を割る」元 `h` が存在する. -/
theorem exists_mem_coset_primeFactors_orderOf_dvd {G : Type u} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (g : G) :
    ∃ h : G, (↑h : G ⧸ N) = (↑g : G ⧸ N) ∧
      ∀ p ∈ (orderOf h).primeFactors, p ∣ orderOf (↑g : G ⧸ N) := by
  classical
  set m := orderOf (↑g : G ⧸ N) with hm_def
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  -- `⟨g⟩` は可換ゆえ可解. Hall E で π-Hall 部分群 `C` を取る (π = `m` の約数の集合).
  have : Group.IsSolvable ↥(Subgroup.zpowers g) :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M :=
      ↥(Subgroup.zpowers g))).comm a b
  obtain ⟨C, hC⟩ := hall_E_exists (G := ↥(Subgroup.zpowers g)) {q : ℕ | q ∣ m}
  have hks : Nat.card ↥C * C.index = orderOf g := by
    rw [Subgroup.card_mul_index, Nat.card_zpowers]
  have hk0 : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have hs0 : C.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hks
    exact hn0 hks.symm
  have hsn : C.index ∣ orderOf g := ⟨Nat.card ↥C, by rw [← hks, Nat.mul_comm]⟩
  -- `m` は π-数, `C.index` は π'-数なので互いに素.
  have hcop : Nat.Coprime m C.index := by
    rw [Nat.Coprime]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpm : p ∣ m := hpd.trans (Nat.gcd_dvd_left _ _)
    have hps : p ∣ C.index := hpd.trans (Nat.gcd_dvd_right _ _)
    exact hC.2 p (Nat.mem_primeFactors.mpr ⟨hp, hps, hs0⟩) hpm
  -- 中国剰余定理: `t ≡ 1 (mod m)`, `t ≡ 0 (mod C.index)`.
  obtain ⟨t, ht1, ht0⟩ := Nat.chineseRemainder hcop 1 0
  have hst : C.index ∣ t := (Nat.modEq_zero_iff_dvd).mp ht0
  obtain ⟨t', hts⟩ := hst
  refine ⟨g ^ t, ?_, ?_⟩
  · -- `t ≡ 1 (mod m)` なので `(↑g)^t = ↑g`.
    have h1 : (↑g : G ⧸ N) ^ t = (↑g : G ⧸ N) ^ 1 := pow_eq_pow_iff_modEq.mpr ht1
    rw [pow_one] at h1
    simpa using h1
  · -- `C.index ∣ t` なので `o(g^t) ∣ o(g^C.index) = |C|`, その素因数は π (= `m` の約数).
    intro p hp
    have hgs : orderOf (g ^ C.index) = Nat.card ↥C := by
      rw [orderOf_pow' _ hs0, Nat.gcd_eq_right hsn, ← hks,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)]
    have hdvd : orderOf (g ^ t) ∣ Nat.card ↥C := by
      rw [hts, pow_mul, ← hgs]
      exact orderOf_pow_dvd t'
    exact hC.1 p (Nat.primeFactors_mono hdvd hk0 hp)

/-- **Isaacs Problem 3B.6(b)** (書籍 p. 84): さらに `m = o(Ng)` と `|N|` が互いに素なら,
(a) の元 `h` の位数はちょうど `m`.

`m ∣ o(h)` は `Nh = Ng` から従い, 逆に `h^m ∈ N` なので `o(h)/m = o(h^m)` は `|N|` を割る.
`o(h)` の素因数はすべて `m` を割る (= `|N|` を割らない) から `o(h)/m = 1`. -/
theorem orderOf_eq_of_primeFactors_orderOf_dvd_of_coprime {G : Type u} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] {g h : G} (hcoset : (↑h : G ⧸ N) = (↑g : G ⧸ N))
    (hprimes : ∀ p ∈ (orderOf h).primeFactors, p ∣ orderOf (↑g : G ⧸ N))
    (hcop : Nat.Coprime (orderOf (↑g : G ⧸ N)) (Nat.card ↥N)) :
    orderOf h = orderOf (↑g : G ⧸ N) := by
  classical
  set m := orderOf (↑g : G ⧸ N) with hm_def
  have hh0 : orderOf h ≠ 0 := (orderOf_pos h).ne'
  -- `m = o(Nh) ∣ o(h)`.
  have hmdvd : m ∣ orderOf h := by
    rw [hm_def, ← hcoset]
    exact orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl)
  -- `h ^ m ∈ N` なので `o(h ^ m) ∣ |N|`.
  have hmemN : h ^ m ∈ N := by
    have : ((h ^ m : G) : G ⧸ N) = 1 := by
      rw [QuotientGroup.mk_pow, hcoset, hm_def, pow_orderOf_eq_one]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hdvdN : orderOf (h ^ m) ∣ Nat.card ↥N := by
    have := orderOf_dvd_natCard (⟨h ^ m, hmemN⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this
  -- `o(h ^ m) = o(h) / m`.
  have hm0 : m ≠ 0 := (orderOf_pos (↑g : G ⧸ N)).ne'
  have hquot : orderOf (h ^ m) = orderOf h / m := by
    rw [orderOf_pow' _ hm0, Nat.gcd_eq_right hmdvd]
  -- `o(h)/m` の素因数は `m` を割り, かつ `|N|` を割る ⟹ 互いに素より 1.
  have hdiv : orderOf h / m ∣ Nat.card ↥N := hquot ▸ hdvdN
  have hdivm : orderOf h / m ∣ orderOf h := Nat.div_dvd_of_dvd hmdvd
  have h1 : orderOf h / m = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpq : p ∣ orderOf h := hpd.trans hdivm
    have hpN : p ∣ Nat.card ↥N := hpd.trans hdiv
    have hpm : p ∣ m := hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hh0⟩)
    have hdvd1 : p ∣ 1 := by
      have hg := Nat.dvd_gcd hpm hpN
      rwa [Nat.Coprime.gcd_eq_one hcop] at hg
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd1)
  have := Nat.div_mul_cancel hmdvd
  rw [h1, one_mul] at this
  exact this.symm

/-- `N ⊴ G` と `K ≤ G` の位数が互いに素で `N ⊔ K = H` なら, `H` の中で `K` は `N` の補群. -/
theorem isComplement'_subgroupOf_of_coprime {G : Type*} [Group G] [Finite G] {N K H : Subgroup G}
    [N.Normal] (hsup : N ⊔ K = H) (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥K)) :
    (N.subgroupOf H).IsComplement' (K.subgroupOf H) := by
  have hNH : N ≤ H := hsup ▸ le_sup_left
  have hKH : K ≤ H := hsup ▸ le_sup_right
  have hinf : (N ⊓ K : Subgroup G) = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro y hyN hyK
    have hy : (y : G) ∈ (N ⊓ K : Subgroup G) :=
      ⟨Subgroup.mem_subgroupOf.mp hyN, Subgroup.mem_subgroupOf.mp hyK⟩
    rw [hinf, Subgroup.mem_bot] at hy
    exact Subtype.ext hy
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨y, hyH⟩
    have hy : y ∈ N ⊔ K := by rw [hsup]; exact hyH
    rw [Subgroup.mem_sup_of_normal_left] at hy
    obtain ⟨u, huN, k, hkK, heq⟩ := hy
    exact ⟨⟨u, hNH huN⟩, Subgroup.mem_subgroupOf.mpr huN, ⟨k, hKH hkK⟩,
      Subgroup.mem_subgroupOf.mpr hkK, Subtype.ext heq⟩

/-- **Isaacs Problem 3B.6(c)** (書籍 p. 84): `N ⊴ G` で `o(h)` と `|N|` が互いに素とする.
`Nh` が `G ⧸ N` の中で自身の逆元と共役なら, `h` は `G` の中で `h⁻¹` と共役.

教科書の hint どおり: `x` を `(Nh)^{Nx} = (Nh)⁻¹` なる元とすると `x` は `H := N⟨h⟩` を正規化し,
`⟨h⟩` と `⟨h^x⟩` はどちらも `H` の中で `N` の補群. Schur-Zassenhaus D-part
(`exists_conj_le_of_isComplement'_of_coprime'`; 商 `H/N ≅ ⟨h⟩` は巡回=可解なので `U` 可解枝で
使える) が `⟨h^x⟩ ≤ ⟨h⟩^y` (`y ∈ N`) を与え, `⟨h⟩ ⊓ N = 1` から像を比べて `h^{xy⁻¹} = h⁻¹`. -/
theorem isConj_inv_of_quotient_isConj_inv {G : Type u} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] {h : G} (hcop : Nat.Coprime (Nat.card ↥N) (orderOf h))
    (hconj : IsConj (↑h : G ⧸ N) (↑h : G ⧸ N)⁻¹) : IsConj h h⁻¹ := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  set K := Subgroup.zpowers h with hK_def
  set H := N ⊔ K with hH_def
  have hcop' : Nat.Coprime (Nat.card ↥N) (Nat.card ↥K) := by
    rw [hK_def, Nat.card_zpowers]; exact hcop
  -- `h₂ := x h x⁻¹` の `G ⧸ N` での像は `(↑h)⁻¹`.
  set h₂ := x * h * x⁻¹ with hh₂_def
  have himg : (↑h₂ : G ⧸ N) = (↑h : G ⧸ N)⁻¹ := by
    rw [hh₂_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hc
  have hh₂H : h₂ ∈ H := by
    have hmemN : h₂ * h ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, himg, inv_mul_cancel]
    have hrw : h₂ = h₂ * h * h⁻¹ := by group
    rw [hrw]
    exact Subgroup.mul_mem _ ((le_sup_left : N ≤ H) hmemN)
      ((le_sup_right : K ≤ H) (Subgroup.inv_mem _ (Subgroup.mem_zpowers h)))
  set K₂ := Subgroup.zpowers h₂ with hK₂_def
  have hK₂H : K₂ ≤ H := Subgroup.zpowers_le.mpr hh₂H
  have hKH : K ≤ H := le_sup_right
  have hNH : N ≤ H := le_sup_left
  -- `H` の中で `K` は `N` の補群.
  have : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf
  have hcompl : (N.subgroupOf H).IsComplement' (K.subgroupOf H) :=
    isComplement'_subgroupOf_of_coprime rfl hcop'
  -- `o(h₂) = o(h)` なので `U := K₂.subgroupOf H` の位数は `|N|` と互いに素.
  have hord₂ : orderOf h₂ = orderOf h := by
    have hinj := orderOf_injective (MulAut.conj x).toMonoidHom (MulEquiv.injective _) h
    simpa [hh₂_def, MulAut.conj_apply] using hinj
  have hcardU : Nat.card ↥(K₂.subgroupOf H) = orderOf h := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₂H).toEquiv, hK₂_def, Nat.card_zpowers,
      hord₂]
  have hcardM : Nat.card ↥(N.subgroupOf H) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hcopU : Nat.Coprime (Nat.card ↥(K₂.subgroupOf H)) (Nat.card ↥(N.subgroupOf H)) := by
    rw [hcardU, hcardM]; exact hcop.symm
  -- `U` は巡回群 `K₂` と同型ゆえ可解.
  have hsolvU : Group.IsSolvable ↥(K₂.subgroupOf H) := by
    have : Group.IsSolvable ↥K₂ :=
      Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := ↥K₂)).comm a b
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hK₂H).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK₂H).injective
  -- Schur-Zassenhaus D-part: `U ≤ (K.subgroupOf H)^y` なる `y ∈ N.subgroupOf H`.
  obtain ⟨y, hyN, hyle⟩ :=
    exists_conj_le_of_isComplement'_of_coprime' (Or.inr hsolvU) hcompl hcopU
  have hmem : (⟨h₂, hh₂H⟩ : ↥H) ∈ K₂.subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers h₂)
  obtain ⟨k, hkK, hkeq⟩ := Subgroup.mem_map.mp (hyle hmem)
  -- `G` の元として: `y k y⁻¹ = h₂`, `k ∈ K`, `y ∈ N`.
  have hkG : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
  have hyG : (y : G) ∈ N := Subgroup.mem_subgroupOf.mp hyN
  have hkeqG : (y : G) * (k : G) * (y : G)⁻¹ = h₂ := congrArg Subtype.val hkeq
  have hkval : (k : G) = (y : G)⁻¹ * h₂ * (y : G) := by
    rw [← hkeqG]; group
  -- `k` の像は `(↑h)⁻¹` なので `k * h ∈ N ⊓ K = ⊥`, つまり `k = h⁻¹`.
  have hkimg : ((k : G) : G ⧸ N) = (↑h : G ⧸ N)⁻¹ := by
    have hy1 : ((y : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hyG
    rw [hkval]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, himg, inv_one, one_mul, mul_one]
  have hkhN : (k : G) * h ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hkimg, inv_mul_cancel]
  have hkhK : (k : G) * h ∈ K := Subgroup.mul_mem _ hkG (Subgroup.mem_zpowers h)
  have hkh1 : (k : G) * h = 1 := by
    have hinf : (N ⊓ K : Subgroup G) = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop').eq_bot
    have : (k : G) * h ∈ (N ⊓ K : Subgroup G) := ⟨hkhN, hkhK⟩
    rwa [hinf, Subgroup.mem_bot] at this
  have hkinv : (k : G) = h⁻¹ := eq_inv_iff_mul_eq_one.mpr hkh1
  -- `h⁻¹ = (y⁻¹ x) h (y⁻¹ x)⁻¹`.
  refine isConj_iff.mpr ⟨(y : G)⁻¹ * x, ?_⟩
  rw [← hkinv, hkval, hh₂_def]
  group

/-- **Isaacs Problem 3B.6 (まとめ)** (書籍 p. 84): `m := o(Ng)` が `|N|` と互いに素で,
`Ng` が `G ⧸ N` の中で自身の逆元と共役なら, 剰余類 `Ng` の中に
「位数がちょうど `m`」かつ「`G` の中で自身の逆元と共役」な元 `h` が存在する.

(a) で `h` を取り, (b) で `o(h) = m`, (c) で `h ~ h⁻¹`. -/
theorem exists_mem_coset_orderOf_eq_and_isConj_inv {G : Type u} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] {g : G}
    (hcop : Nat.Coprime (orderOf (↑g : G ⧸ N)) (Nat.card ↥N))
    (hconj : IsConj (↑g : G ⧸ N) (↑g : G ⧸ N)⁻¹) :
    ∃ h : G, (↑h : G ⧸ N) = (↑g : G ⧸ N) ∧ orderOf h = orderOf (↑g : G ⧸ N) ∧ IsConj h h⁻¹ := by
  obtain ⟨h, hcoset, hprimes⟩ := exists_mem_coset_primeFactors_orderOf_dvd (N := N) g
  have hord : orderOf h = orderOf (↑g : G ⧸ N) :=
    orderOf_eq_of_primeFactors_orderOf_dvd_of_coprime (N := N) hcoset hprimes hcop
  refine ⟨h, hcoset, hord, isConj_inv_of_quotient_isConj_inv (N := N) ?_ ?_⟩
  · rw [hord]; exact hcop.symm
  · rw [hcoset]; exact hconj

/-! ### Problem 3B.8 — 極大部分群の指数がすべて素数な有限群

そのような群は可解で, 最大素因数 `p` の Sylow `p`-部分群が正規, 最小素因数 `q` の正規
`q`-補群を持つ (書籍の Note: 実際には超可解だが, それは Huppert の難しい定理). -/

/-- 極大部分群の指数がすべて素数なら, **最大**素因数 `p` の Sylow `p`-部分群は正規.

`P` が正規でないとすると `N_G(P)` を含む極大部分群 `M` が取れ, `[G:M] = r` は素数.
`P ∈ Syl_p(M)` かつ `N_M(P) = N_G(P)` なので Sylow の個数は `n_p(G) = n_p(M) · r`.
両者とも `≡ 1 (mod p)` なので `r ≡ 1 (mod p)`, つまり `r > p` となり `p` の最大性に反する. -/
theorem sylow_normal_of_forall_isCoatom_index_prime {G : Type u} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hmax : ∀ M : Subgroup G, IsCoatom M → M.index.Prime)
    (hlarge : ∀ r ∈ (Nat.card G).primeFactors, r ≤ p) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  by_contra hnn
  have hne : Subgroup.normalizer ((P : Subgroup G) : Set G) ≠ ⊤ := fun h =>
    hnn (Subgroup.normalizer_eq_top_iff.mp h)
  obtain ⟨M, hMcoatom, hle⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.normalizer ((P : Subgroup G) : Set G))).resolve_left hne
  have hPM : (P : Subgroup G) ≤ M := le_trans Subgroup.le_normalizer hle
  have hrprime : M.index.Prime := hmax M hMcoatom
  have hcountG : Nat.card (Sylow p G) = (Subgroup.normalizer ((P : Subgroup G) : Set G)).index :=
    P.card_eq_index_normalizer
  have hcountM : Nat.card (Sylow p ↥M)
      = ((Subgroup.normalizer ((P : Subgroup G) : Set G)).subgroupOf M).index := by
    rw [(P.subtype hPM).card_eq_index_normalizer]
    congr 1
    exact (Subgroup.subgroupOf_normalizer_eq hPM).symm
  have hmul : Nat.card (Sylow p ↥M) * M.index = Nat.card (Sylow p G) := by
    rw [hcountM, hcountG]
    exact Subgroup.relIndex_mul_index hle
  have h1 : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have h2 : Nat.card (Sylow p ↥M) ≡ 1 [MOD p] := card_sylow_modEq_one p ↥M
  have hr1 : M.index ≡ 1 [MOD p] := by
    have h3 : Nat.card (Sylow p ↥M) * M.index ≡ 1 * M.index [MOD p] := Nat.ModEq.mul_right _ h2
    rw [one_mul, hmul] at h3
    exact h3.symm.trans h1
  have htwo : 2 ≤ M.index := hrprime.two_le
  have hple : p ≤ M.index - 1 :=
    Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' hrprime.one_lt.le).mp hr1.symm)
  have hrle : M.index ≤ p :=
    hlarge M.index (Nat.mem_primeFactors.mpr ⟨hrprime, M.index_dvd_card, Nat.card_pos.ne'⟩)
  omega

/-- Sylow `p`-部分群が正規で `p ∣ |G|` なら `G` の位数は真に減る (商へ降りる帰納法の道具). -/
theorem sylow_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card G) (P : Sylow p G) : (P : Subgroup G) ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card ↥(P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [hbot, Subgroup.card_bot, one_mul] at hcard
  refine P.not_dvd_index ?_
  rw [hbot, hcard]
  exact hp

/-- 極大部分群の指数がすべて素数な有限群の商群も同じ仮説を満たす. -/
theorem forall_isCoatom_index_prime_quotient {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.index.Prime) :
    ∀ M : Subgroup (G ⧸ N), IsCoatom M → M.index.Prime := by
  intro M hM
  have hcoatom : IsCoatom (M.comap (QuotientGroup.mk' N)) :=
    Subgroup.isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective N) hM
  have hindex := Subgroup.index_comap_of_surjective (H := M) (QuotientGroup.mk'_surjective N)
  rw [← hindex]
  exact hmax _ hcoatom

/-- Problem 3B.8 前半の `|G|`-強帰納法本体. -/
theorem isSolvable_of_forall_isCoatom_index_prime_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [Finite G],
      (∀ M : Subgroup G, IsCoatom M → M.index.Prime) → Nat.card G ≤ n → Group.IsSolvable G := by
  induction n with
  | zero =>
    intro G _ _ _ hcard
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ hmax hcard
    rcases subsingleton_or_nontrivial G with hs | hnt
    · infer_instance
    · -- 最大素因数 `p` の Sylow 部分群は正規.
      have hcard1 : 1 < Nat.card G := Finite.one_lt_card
      have hne : (Nat.card G).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hcard1
      set p := (Nat.card G).primeFactors.max' hne with hp_def
      have hpmem : p ∈ (Nat.card G).primeFactors := Finset.max'_mem _ _
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpmem⟩
      have hpdvd : p ∣ Nat.card G := Nat.dvd_of_mem_primeFactors hpmem
      have hlarge : ∀ r ∈ (Nat.card G).primeFactors, r ≤ p := fun r hr => Finset.le_max' _ r hr
      obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
      have hPnormal : (P : Subgroup G).Normal :=
        sylow_normal_of_forall_isCoatom_index_prime hmax hlarge P
      have hPsolv : Group.IsSolvable ↥(P : Subgroup G) := by
        have := P.isPGroup'.isNilpotent
        infer_instance
      -- 商 `G ⧸ P` は真に小さく, 同じ仮説を満たす.
      have hPne : (P : Subgroup G) ≠ ⊥ := sylow_ne_bot hpdvd P
      have : Nontrivial ↥(P : Subgroup G) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
      have hPcard : 1 < Nat.card ↥(P : Subgroup G) := Finite.one_lt_card
      have hprod : Nat.card ↥(P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
        Subgroup.card_mul_index _
      have hquot : Nat.card (G ⧸ (P : Subgroup G)) ≤ n := by
        have h2 : 2 * (P : Subgroup G).index
            ≤ Nat.card ↥(P : Subgroup G) * (P : Subgroup G).index :=
          Nat.mul_le_mul_right _ hPcard
        rw [← Subgroup.index_eq_card]
        omega
      have : Group.IsSolvable (G ⧸ (P : Subgroup G)) :=
        ih (forall_isCoatom_index_prime_quotient hmax) hquot
      exact Group.isSolvable_of_ker_le_range ((P : Subgroup G).subtype)
        (QuotientGroup.mk' (P : Subgroup G))
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- **Isaacs Problem 3B.8 前半** (書籍 p. 85): 有限群 `G` の極大部分群の指数がすべて素数なら
`G` は可解.

最大素因数 `p` の Sylow `p`-部分群 `P` は正規 (`sylow_normal_of_forall_isCoatom_index_prime`)
で, 商 `G ⧸ P` も同じ仮説を満たすから帰納法で可解. `P` は `p`-群ゆえ冪零・可解なので `G` も可解. -/
theorem isSolvable_of_forall_isCoatom_index_prime {G : Type u} [Group G] [Finite G]
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.index.Prime) : Group.IsSolvable G :=
  isSolvable_of_forall_isCoatom_index_prime_aux (Nat.card G) hmax le_rfl

/-- Problem 3B.8 後半の `|G|`-強帰納法本体 (正規 `q`-補群の構成). -/
theorem exists_normal_qComplement_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [Finite G] {q : ℕ}, q.Prime →
      (∀ M : Subgroup G, IsCoatom M → M.index.Prime) →
      (∀ r ∈ (Nat.card G).primeFactors, q ≤ r) → Nat.card G ≤ n →
      ∃ H : Subgroup G, H.Normal ∧ ¬ q ∣ Nat.card ↥H ∧ ∃ k : ℕ, H.index = q ^ k := by
  induction n with
  | zero =>
    intro G _ _ q _ _ _ hcard
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ q hq hmax hsmall hcard
    have : Fact q.Prime := ⟨hq⟩
    by_cases hall : ∀ d : ℕ, d.Prime → d ∣ Nat.card G → d = q
    · -- `|G|` が `q`-冪: `H = ⊥` が正規 `q`-補群.
      refine ⟨⊥, inferInstance, ?_, ?_⟩
      · intro hdvd
        rw [Subgroup.card_bot] at hdvd
        exact hq.one_lt.ne' (Nat.dvd_one.mp hdvd)
      · refine ⟨(Nat.card G).primeFactorsList.length, ?_⟩
        rw [Subgroup.index_bot]
        exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
          fun {d} hd hdvd => hall d hd hdvd
    · -- `q` と異なる素因数がある ⟹ 最大素因数 `p ≠ q` の Sylow を割って帰納法.
      push Not at hall
      obtain ⟨d, hdprime, hddvd, hdne⟩ := hall
      have hcard1 : 1 < Nat.card G := by
        have h1 := Nat.le_of_dvd Nat.card_pos hddvd
        have h2 := hdprime.two_le
        omega
      have hne : (Nat.card G).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hcard1
      set p := (Nat.card G).primeFactors.max' hne with hp_def
      have hpmem : p ∈ (Nat.card G).primeFactors := Finset.max'_mem _ _
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpmem⟩
      have hpdvd : p ∣ Nat.card G := Nat.dvd_of_mem_primeFactors hpmem
      have hlarge : ∀ r ∈ (Nat.card G).primeFactors, r ≤ p := fun r hr => Finset.le_max' _ r hr
      have hdmem : d ∈ (Nat.card G).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hdprime, hddvd, Nat.card_pos.ne'⟩
      have hqd : q ≤ d := hsmall d hdmem
      have hdp : d ≤ p := Finset.le_max' _ d hdmem
      have hpq : p ≠ q := by omega
      obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
      have hPnormal : (P : Subgroup G).Normal :=
        sylow_normal_of_forall_isCoatom_index_prime hmax hlarge P
      have hPne : (P : Subgroup G) ≠ ⊥ := sylow_ne_bot hpdvd P
      have : Nontrivial ↥(P : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
      have hPcard : 1 < Nat.card ↥(P : Subgroup G) := Finite.one_lt_card
      have hprod : Nat.card ↥(P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
        Subgroup.card_mul_index _
      have hquot : Nat.card (G ⧸ (P : Subgroup G)) ≤ n := by
        have h2 : 2 * (P : Subgroup G).index
            ≤ Nat.card ↥(P : Subgroup G) * (P : Subgroup G).index :=
          Nat.mul_le_mul_right _ hPcard
        rw [← Subgroup.index_eq_card]
        omega
      have hsmall' : ∀ r ∈ (Nat.card (G ⧸ (P : Subgroup G))).primeFactors, q ≤ r := by
        intro r hr
        refine hsmall r (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hr, ?_, Nat.card_pos.ne'⟩)
        refine (Nat.dvd_of_mem_primeFactors hr).trans ?_
        rw [← Subgroup.index_eq_card]
        exact Subgroup.index_dvd_card _
      obtain ⟨Hbar, hHbarNormal, hHbarcard, hHbarP⟩ :=
        ih hq (forall_isCoatom_index_prime_quotient hmax) hsmall' hquot
      have := hHbarNormal
      refine ⟨Hbar.comap (QuotientGroup.mk' (P : Subgroup G)), hHbarNormal.comap _, ?_, ?_⟩
      · -- `q ∣ |H|` なら Cauchy で位数 `q` の元 `y` が取れ, その像で矛盾.
        intro hdvdH
        obtain ⟨x, hx⟩ :=
          exists_prime_orderOf_dvd_card' (G := ↥(Hbar.comap (QuotientGroup.mk' (P : Subgroup G))))
            q hdvdH
        have hyH : (x : G) ∈ Hbar.comap (QuotientGroup.mk' (P : Subgroup G)) := x.2
        have hordy : orderOf (x : G) = q := by rw [Subgroup.orderOf_coe]; exact hx
        have hzHbar : (QuotientGroup.mk' (P : Subgroup G)) (x : G) ∈ Hbar :=
          Subgroup.mem_comap.mp hyH
        have hordz : orderOf ((QuotientGroup.mk' (P : Subgroup G)) (x : G)) ∣ q := by
          rw [← hordy]
          exact orderOf_map_dvd _ _
        rcases (Nat.dvd_prime hq).mp hordz with h1 | hqq
        · -- 像が自明 ⟹ `y ∈ P` ⟹ `q ∣ p`-冪 ⟹ `q = p`, 矛盾.
          have hyP : (x : G) ∈ (P : Subgroup G) :=
            (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)
          obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp P.isPGroup'
          have hqdvd : q ∣ p ^ a := by
            rw [← ha, ← hordy, ← Subgroup.orderOf_mk (H := (P : Subgroup G)) (x : G) hyP]
            exact orderOf_dvd_natCard _
          exact hpq ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow hqdvd)).symm
        · -- 像の位数が `q` ⟹ `q ∣ |H̄|`, 矛盾.
          refine hHbarcard ?_
          have hd := orderOf_dvd_natCard
            (⟨(QuotientGroup.mk' (P : Subgroup G)) (x : G), hzHbar⟩ : ↥Hbar)
          rwa [Subgroup.orderOf_mk, hqq] at hd
      · -- 指数は商へ落としても不変なので `[G : H] = [G/P : H̄] = q^k`.
        obtain ⟨k, hk⟩ := hHbarP
        refine ⟨k, ?_⟩
        rw [Subgroup.index_comap_of_surjective (H := Hbar)
          (QuotientGroup.mk'_surjective (P : Subgroup G))]
        exact hk

/-- **Isaacs Problem 3B.8 後半** (書籍 p. 85): 有限群 `G` の極大部分群の指数がすべて素数なら,
最小素因数 `q` について `G` は**正規 `q`-補群**を持つ (位数が `q` で割れない正規部分群 `H` で
指数 `[G : H]` が `q`-冪 — 書籍の言う「指数が Sylow `q`-部分群の位数に等しい部分群」).

最大素因数 `p` の Sylow `p`-部分群 `P` は正規 (`sylow_normal_of_forall_isCoatom_index_prime`).
`|G|` が `q`-冪なら `H = ⊥`. そうでなければ `p ≠ q` で, `G ⧸ P` に帰納法を適用して得た `H̄` の
引き戻しが求めるもの (`|H|` が `q` で割れないことは Cauchy の定理で示し, 指数は
`[G : H] = [G/P : H̄]` で `q`-冪). -/
theorem exists_normal_qComplement {G : Type u} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.index.Prime)
    (hsmall : ∀ r ∈ (Nat.card G).primeFactors, q ≤ r) :
    ∃ H : Subgroup G, H.Normal ∧ ¬ q ∣ Nat.card ↥H ∧ ∃ k : ℕ, H.index = q ^ k :=
  exists_normal_qComplement_aux (Nat.card G) hq hmax hsmall le_rfl

/-! ### Problem 3B.11 — Frattini 部分群の素因数は指数も割る -/

/-- **Isaacs Problem 3B.11** (書籍 p. 85): 有限群 `G` の Frattini 部分群 `Φ(G)` の位数を割る
素数はすべて `|G : Φ(G)|` も割る.

`p ∤ |G : Φ(G)|` と仮定する. `Q ∈ Syl_p(Φ(G))` の `G` への像 `R` は Frattini 論法
(`Sylow.normalizer_sup_eq_top`) と `Φ` の非生成性 (`frattini_nongenerating`) から `G` で正規で,
`[G : R] = [Φ : Q] · [G : Φ]` はどちらの因子も `p` と素だから `|R|` (= `p`-冪) と互いに素.
Schur-Zassenhaus で補群 `H` を取ると `H ⊔ Φ(G) = ⊤` ゆえ `H = ⊤`, つまり `R = ⊥` となり
`p ∣ |Φ(G)|` に矛盾する. -/
theorem prime_dvd_index_frattini_of_dvd_card_frattini {G : Type u} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card ↥(frattini G)) : p ∣ (frattini G).index := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(frattini G)) := inferInstance
  set R : Subgroup G := (Q : Subgroup ↥(frattini G)).map (frattini G).subtype with hR_def
  -- Frattini 論法 + `Φ` の非生成性 ⟹ `R ⊴ G`.
  have htop : Subgroup.normalizer ((R : Subgroup G) : Set G) ⊔ frattini G = ⊤ :=
    Sylow.normalizer_sup_eq_top Q
  have hnormtop : Subgroup.normalizer ((R : Subgroup G) : Set G) = ⊤ :=
    frattini_nongenerating htop
  have hRnormal : R.Normal := Subgroup.normalizer_eq_top_iff.mp hnormtop
  have hRle : R ≤ frattini G := Subgroup.map_subtype_le _
  -- `[G : R] = [Φ : Q] · [G : Φ]` はどちらの因子も `p` と素.
  have hrel : R.subgroupOf (frattini G) = (Q : Subgroup ↥(frattini G)) := by
    rw [hR_def, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _
  have hindexeq : (Q : Subgroup ↥(frattini G)).index * (frattini G).index = R.index := by
    rw [← hrel]
    exact Subgroup.relIndex_mul_index hRle
  have hnpindex : ¬ p ∣ R.index := by
    rw [← hindexeq]
    intro hcontra
    rcases (Nat.Prime.dvd_mul hp).mp hcontra with h | h
    · exact Q.not_dvd_index h
    · exact hnd h
  -- `|R|` は `p`-冪なので `[G : R]` と互いに素 ⟹ Schur-Zassenhaus.
  have hRcard : Nat.card ↥R = Nat.card ↥(Q : Subgroup ↥(frattini G)) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ (frattini G).subtype
      Subtype.coe_injective).toEquiv).symm
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hcop : Nat.Coprime (Nat.card ↥R) R.index := by
    rw [hRcard, ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnpindex)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  -- `H ⊔ Φ = ⊤` ゆえ `H = ⊤`, すなわち `R = ⊥`.
  have hHtop : H = ⊤ := by
    refine frattini_nongenerating (K := H) ?_
    refine top_le_iff.mp ?_
    rw [← hH.sup_eq_top, sup_comm]
    exact sup_le_sup_left hRle H
  rw [hHtop] at hH
  have hRbot : R = ⊥ := disjoint_top.mp hH.disjoint
  rw [hR_def, Subgroup.map_eq_bot_iff_of_injective
    (H := (Q : Subgroup ↥(frattini G))) Subtype.coe_injective] at hRbot
  exact sylow_ne_bot hdvd Q hRbot

/-! ### Problem 3B.12 — 極大部分群の中の部分群と同じ指数をもつ部分群

⚠ **書籍の主張はそのままでは偽** (下の docstring の反例を参照)。成り立つのは「`M` に含まれない
極小正規部分群 `N` がある」場合で, そのとき `N ⊔ H` がちょうど指数 `|M : H|` を与える。 -/

/-- **Isaacs Problem 3B.12** (書籍 p. 85) の**訂正版**: `G` 可解, `M` 極大, `N` を `M` に
含まれない極小正規部分群, `H ≤ M` とすると, `N ⊔ H` の指数はちょうど `|M : H|`.

⚠ **書籍の主張 (「`Φ(G) = 1` で `M` 極大, `H ≤ M` なら `G` は指数 `|M : H|` の部分群を持つ」)
は偽**. 反例: `G = A₄` は可解で `Φ(A₄) = 1` (極大部分群は `V₄` と 4 個の `C₃` で共通部分は 1),
`M = V₄` は極大, `H = ⟨(12)(34)⟩ ≤ M` で `|M : H| = 2` だが `A₄` は指数 2 (位数 6) の部分群を
持たない. 書籍の議論が通るのは「`M` が極小正規部分群 `N` を含まない」場合だけで, `A₄` の
`M = V₄` は唯一の極小正規部分群 `V₄` 自身を含んでしまう.

証明: 極大性から `N ⊔ M = ⊤`. `N` は可解群の極小正規部分群ゆえ abelian で, `N ⊓ M` は `N` にも
`M` にも正規化されるから `G = NM` で正規, 極小性と `N ≰ M` より `N ⊓ M = ⊥`. よって
`|G| = |N||M|`, `|N ⊔ H| = |N||H|` となり `[G : N ⊔ H] = |M|/|H| = [M : H]`. -/
theorem index_sup_eq_relIndex_of_isMinimalNormal_of_not_le {G : Type u} [Group G] [Finite G]
    [Group.IsSolvable G] {M N H : Subgroup G} (hM : IsCoatom M) (hN : Ch02.IsMinimalNormal N)
    (hNM : ¬ N ≤ M) (hHM : H ≤ M) : (N ⊔ H).index = H.relIndex M := by
  have hNnormal : N.Normal := hN.1
  -- `N ⊔ M = ⊤` かつ `N ⊓ M = ⊥`.
  have hsup : N ⊔ M = ⊤ := by
    rw [sup_comm]
    refine hM.2 _ (lt_of_le_of_ne le_sup_left fun h => hNM ?_)
    exact h ▸ le_sup_right
  have habel : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := minimal_normal_isAbelian_of_isSolvable hN
  have hinf_normal : (N ⊓ M).Normal := by
    constructor
    intro x hx g
    have hg : g ∈ N ⊔ M := by rw [hsup]; trivial
    rw [Subgroup.mem_sup_of_normal_left] at hg
    obtain ⟨u, huN, m, hmM, rfl⟩ := hg
    have hy : m * x * m⁻¹ ∈ N ⊓ M :=
      ⟨hNnormal.conj_mem x hx.1 m, M.mul_mem (M.mul_mem hmM hx.2) (M.inv_mem hmM)⟩
    have hcomm : u * (m * x * m⁻¹) = (m * x * m⁻¹) * u := habel u huN _ hy.1
    have hrw : u * m * x * (u * m)⁻¹ = m * x * m⁻¹ := by
      calc u * m * x * (u * m)⁻¹ = u * (m * x * m⁻¹) * u⁻¹ := by group
        _ = (m * x * m⁻¹) * u * u⁻¹ := by rw [hcomm]
        _ = m * x * m⁻¹ := by group
    rw [hrw]
    exact hy
  have hNinfM : N ⊓ M = ⊥ := by
    rcases hN.2.2 (N ⊓ M) hinf_normal inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ (inf_le_right : N ⊓ M ≤ M)) hNM
  -- `|G| = |M| · |N|`.
  have hMindex : M.index = Nat.card ↥N := by
    have h := Ch02.index_mul_card_inf_eq_card_of_sup_eq_top (N := N) (A := M) hsup
    rwa [hNinfM, Subgroup.card_bot, mul_one] at h
  have hGcard : Nat.card ↥M * Nat.card ↥N = Nat.card G := by
    rw [← hMindex]; exact Subgroup.card_mul_index M
  -- `|N ⊔ H| = |N| · |H|`.
  have hNH : N ⊓ H = ⊥ := by
    have h : N ⊓ H ≤ N ⊓ M := inf_le_inf_left N hHM
    rw [hNinfM] at h
    exact le_bot_iff.mp h
  have hNHcard : Nat.card ↥(N ⊔ H) = Nat.card ↥N * Nat.card ↥H := by
    have h1 := Ch01.card_mul_card_inf N H
    rw [hNH, Subgroup.card_bot, mul_one] at h1
    rw [← h1, ← Subgroup.normal_mul, SetLike.coe_sort_coe]
  -- `[M : H] = |M| / |H|`.
  have hrel : Nat.card ↥H * H.relIndex M = Nat.card ↥M := by
    have h1 : Nat.card ↥(H.subgroupOf M) * (H.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv] at h1
  -- 3 つを組み合わせて指数を計算する.
  have hidx : (N ⊔ H).index * Nat.card ↥(N ⊔ H) = Nat.card G := by
    rw [mul_comm]; exact Subgroup.card_mul_index _
  rw [hNHcard] at hidx
  have hkey : (N ⊔ H).index * (Nat.card ↥N * Nat.card ↥H)
      = H.relIndex M * (Nat.card ↥N * Nat.card ↥H) := by
    rw [hidx, ← hGcard, ← hrel]
    ring
  refine Nat.eq_of_mul_eq_mul_right ?_ hkey
  exact Nat.mul_pos Nat.card_pos Nat.card_pos

/-! ### Problem 3B.13 — 可解根基 (最大の可解正規部分群) -/

/-- 正規かつ可解な 2 つの部分群の結びも可解 (第二同型定理 + 拡大の可解性). -/
theorem isSolvable_sup_of_normal {G : Type*} [Group G] [Finite G] (R N : Subgroup G) [R.Normal]
    [N.Normal] [Group.IsSolvable ↥R] [Group.IsSolvable ↥N] : Group.IsSolvable ↥(R ⊔ N) := by
  have : Group.IsSolvable (↥R ⧸ N.subgroupOf R) := inferInstance
  have : Group.IsSolvable (↥(R ⊔ N) ⧸ N.subgroupOf (R ⊔ N)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientInfEquivProdNormalQuotient R N).symm.toMonoidHom)
      (QuotientGroup.quotientInfEquivProdNormalQuotient R N).symm.injective
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf (R ⊔ N)).subtype
    (QuotientGroup.mk' (N.subgroupOf (R ⊔ N)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- **Isaacs Problem 3B.13** (書籍 p. 85): 有限群は**可解な正規部分群のうち最大のもの**
(可解根基) をただ一つ持つ.

位数最大の可解正規部分群 `R` を取る. 任意の可解正規部分群 `N` に対し `R ⊔ N` も可解正規
(`isSolvable_sup_of_normal`) なので位数の最大性から `R ⊔ N = R`, すなわち `N ≤ R`. -/
theorem exists_greatest_isSolvable_normal {G : Type u} [Group G] [Finite G] :
    ∃ R : Subgroup G, R.Normal ∧ Group.IsSolvable ↥R ∧
      ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N ≤ R := by
  classical
  obtain ⟨R, hRmem, hRmax⟩ :=
    Set.exists_max_image {K : Subgroup G | K.Normal ∧ Group.IsSolvable ↥K}
      (fun K : Subgroup G => Nat.card ↥K) (Set.toFinite _)
      ⟨⊥, inferInstance, inferInstance⟩
  obtain ⟨hRnorm, hRsolv⟩ := hRmem
  refine ⟨R, hRnorm, hRsolv, fun N hN hNsolv => ?_⟩
  have := hRnorm
  have := hN
  have := hRsolv
  have := hNsolv
  have hsolv : Group.IsSolvable ↥(R ⊔ N) := isSolvable_sup_of_normal R N
  have hle : Nat.card ↥(R ⊔ N) ≤ Nat.card ↥R := hRmax _ ⟨inferInstance, hsolv⟩
  have heq : R = R ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  exact heq ▸ le_sup_right

/-! ### Problem 3B.14 — `Z(F(G))` は `C_G(F(G))` の最大可解正規部分群 -/

/-- Problem 3B.14 の帰納本体: `C = C_G(F(G))` の可解正規部分群は `F(G) ⊓ C` に含まれる.
`|S|` に関する強帰納法で, `⁅S, S⁆ < S` (可解) に帰納法の仮定を当ててから Problem 1D.19
(`Ch01.le_fitting_subgroupOf_of_commutator_le`) を使う. -/
theorem isSolvable_normal_le_fitting_subgroupOf_aux {G : Type u} [Group G] [Finite G]
    {C : Subgroup G} (hC : C = Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G))
    (n : ℕ) : ∀ S : Subgroup ↥C, S.Normal → Group.IsSolvable ↥S → Nat.card ↥S ≤ n →
      S ≤ (Ch01.fitting G).subgroupOf C := by
  induction n with
  | zero =>
    intro S _ _ hcard
    have := Nat.card_pos (α := ↥S)
    omega
  | succ n ih =>
    intro S hSnorm hSsolv hcard
    have := hSnorm
    have := hSsolv
    rcases eq_or_ne S ⊥ with rfl | hSne
    · exact bot_le
    · have : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
      have hlt : ⁅S, S⁆ < S := by
        rw [← S.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
          Subgroup.map_subtype_lt_map_subtype]
        exact Group.IsSolvable.commutator_lt_top_of_nontrivial ↥S
      have hcomm_normal : (⁅S, S⁆ : Subgroup ↥C).Normal := Subgroup.commutator_normal S S
      have hcomm_solv : Group.IsSolvable ↥(⁅S, S⁆ : Subgroup ↥C) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hlt.le)
          (Subgroup.inclusion_injective hlt.le)
      have hcard' : Nat.card ↥(⁅S, S⁆ : Subgroup ↥C) ≤ n := by
        have hne : (⁅S, S⁆ : Subgroup ↥C).subgroupOf S ≠ ⊤ := by
          intro htop
          rw [Subgroup.subgroupOf_eq_top] at htop
          exact absurd htop hlt.not_ge
        have hlt' := Subgroup.card_lt_card_of_ne_top hne
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlt.le).toEquiv] at hlt'
        omega
      exact Ch01.le_fitting_subgroupOf_of_commutator_le hC (ih _ hcomm_normal hcomm_solv hcard')

/-- **Isaacs Problem 3B.14** (書籍 p. 86): `F = F(G)`, `C = C_G(F)` とすると `Z(F)` は `C` の
**最大の可解正規部分群**である.

`Z(F)` は `G` の部分群としては `F ⊓ C` に一致する
(`Ch01.center_fitting_map_eq_inf_centralizer`) ので, ここでは `↥C` の部分群
`F.subgroupOf C` として述べる. 主張は 3 つ: (i) `C` で正規, (ii) 可解 (実際 abelian —
`F ⊓ C ≤ Z(↥C)`), (iii) `C` の任意の可解正規部分群を含む.

(iii) は Problem 1D.19 (`C/(C ⊓ F)` は非自明な abelian 正規部分群を持たない) から
`|S|` の帰納法で従う (`isSolvable_normal_le_fitting_subgroupOf_aux`).

書籍の Note: `G` が可解なら `C` 自身が可解正規なので (iii) より `C = Z(F)`, すなわち
可解群では `C_G(F(G)) ≤ F(G)`. -/
theorem center_fitting_greatest_isSolvable_normal_centralizer {G : Type u} [Group G] [Finite G]
    {C : Subgroup G} (hC : C = Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G)) :
    ((Ch01.fitting G).subgroupOf C).Normal ∧
      Group.IsSolvable ↥((Ch01.fitting G).subgroupOf C) ∧
      ∀ S : Subgroup ↥C, S.Normal → Group.IsSolvable ↥S → S ≤ (Ch01.fitting G).subgroupOf C := by
  have hCnormal : C.Normal := hC ▸ Subgroup.normal_centralizer
  refine ⟨Subgroup.normal_subgroupOf, ?_, fun S hS hSsolv =>
    isSolvable_normal_le_fitting_subgroupOf_aux hC (Nat.card ↥S) S hS hSsolv le_rfl⟩
  -- `F ⊓ C ≤ Z(↥C)` なので abelian, 特に可解.
  have hle := Ch01.fitting_subgroupOf_le_center_of_eq_centralizer hC
  refine Group.isSolvable_of_comm fun a b => ?_
  have ha : (a : ↥C) ∈ Subgroup.center ↥C := hle a.2
  exact Subtype.ext (Subgroup.mem_center_iff.mp ha (b : ↥C)).symm

/-! ### Problem 3B.15 (Berkovich) — 最小指数の真部分群は正規 -/

/-- Problem 3B.15 の `|G|`-強帰納法本体. -/
theorem normal_of_index_minimal_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [Finite G] [Group.IsSolvable G] (H : Subgroup G),
      Nat.card G ≤ n → H ≠ ⊤ → (∀ K : Subgroup G, K ≠ ⊤ → H.index ≤ K.index) → H.Normal := by
  induction n with
  | zero =>
    intro G _ _ _ H hcard _ _
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ _ H hcard hHne hmin
    -- 最小指数の真部分群は極大.
    have hcoatom : IsCoatom H := by
      refine ⟨hHne, fun K hHK => ?_⟩
      by_contra hKne
      have hrel : H.relIndex K * K.index = H.index := Subgroup.relIndex_mul_index hHK.le
      have hne1 : H.relIndex K ≠ 1 := by
        intro h1
        have hKH : K ≤ H := by
          have htop : H.subgroupOf K = ⊤ := Subgroup.index_eq_one.mp h1
          rwa [Subgroup.subgroupOf_eq_top] at htop
        exact absurd (le_antisymm hHK.le hKH) hHK.ne
      have hne0 : H.relIndex K ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hrel
        exact Subgroup.index_ne_zero_of_finite hrel.symm
      have h2 : 2 * K.index ≤ H.relIndex K * K.index :=
        Nat.mul_le_mul_right _ (by omega)
      have hKpos : 0 < K.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
      have := hmin K hKne
      omega
    have hnt : Nontrivial G := by
      rcases subsingleton_or_nontrivial G with hs | h
      · exact absurd (by ext x; simp [Subsingleton.elim x (1 : G)] : H = ⊤) hHne
      · exact h
    obtain ⟨N, hNmin, -⟩ :=
      Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    have hNnormal : N.Normal := hNmin.1
    by_cases hNH : N ≤ H
    · -- `N ≤ H`: `G ⧸ N` に落として帰納法.
      have hHmap_ne : H.map (QuotientGroup.mk' N) ≠ ⊤ := by
        intro htop
        apply hHne
        have hcm := congrArg (Subgroup.comap (QuotientGroup.mk' N)) htop
        rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNH,
          Subgroup.comap_top] at hcm
      have hHmap_index : (H.map (QuotientGroup.mk' N)).index = H.index :=
        Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N)
          (by rw [QuotientGroup.ker_mk']; exact hNH)
      have hmin' : ∀ K : Subgroup (G ⧸ N), K ≠ ⊤ →
          (H.map (QuotientGroup.mk' N)).index ≤ K.index := by
        intro K hK
        rw [hHmap_index,
          ← Subgroup.index_comap_of_surjective (H := K) (QuotientGroup.mk'_surjective N)]
        refine hmin _ fun htop => hK ?_
        rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, htop,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNmin.2.1
      have hNcard : 1 < Nat.card ↥N := Finite.one_lt_card
      have hprod : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
      have hcardquot : Nat.card (G ⧸ N) ≤ n := by
        have h2 : 2 * N.index ≤ Nat.card ↥N * N.index := Nat.mul_le_mul_right _ hNcard
        rw [← Subgroup.index_eq_card]
        omega
      have hHmapnormal : (H.map (QuotientGroup.mk' N)).Normal :=
        ih _ hcardquot hHmap_ne hmin'
      have hHeq : H = (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNH]
      rw [hHeq]
      exact hHmapnormal.comap _
    · -- `N ≰ H`: `G = N ⋊ H` で `N` への `H` の作用を見る.
      have hsup : N ⊔ H = ⊤ := by
        rw [sup_comm]
        refine hcoatom.2 _ (lt_of_le_of_ne le_sup_left fun h => hNH ?_)
        exact h ▸ le_sup_right
      have habel : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := minimal_normal_isAbelian_of_isSolvable hNmin
      have hinf : N ⊓ H = ⊥ := by
        have hinf_normal : (N ⊓ H).Normal := by
          constructor
          intro x hx g
          have hg : g ∈ N ⊔ H := by rw [hsup]; trivial
          rw [Subgroup.mem_sup_of_normal_left] at hg
          obtain ⟨u, huN, m, hmH, rfl⟩ := hg
          have hy : m * x * m⁻¹ ∈ N ⊓ H :=
            ⟨hNnormal.conj_mem x hx.1 m, H.mul_mem (H.mul_mem hmH hx.2) (H.inv_mem hmH)⟩
          have hcomm : u * (m * x * m⁻¹) = (m * x * m⁻¹) * u := habel u huN _ hy.1
          have hrw : u * m * x * (u * m)⁻¹ = m * x * m⁻¹ := by
            calc u * m * x * (u * m)⁻¹ = u * (m * x * m⁻¹) * u⁻¹ := by group
              _ = (m * x * m⁻¹) * u * u⁻¹ := by rw [hcomm]
              _ = m * x * m⁻¹ := by group
          rw [hrw]
          exact hy
        rcases hNmin.2.2 (N ⊓ H) hinf_normal inf_le_left with h | h
        · exact h
        · exact absurd (h ▸ (inf_le_right : N ⊓ H ≤ H)) hNH
      -- `Z := N ⊓ C_G(H)` は `G` で正規.
      have hZnormal : (N ⊓ Subgroup.centralizer (H : Set G)).Normal := by
        constructor
        intro x hx g
        have hg : g ∈ N ⊔ H := by rw [hsup]; trivial
        rw [Subgroup.mem_sup_of_normal_left] at hg
        obtain ⟨u, huN, m, hmH, rfl⟩ := hg
        have hxH : m * x * m⁻¹ = x := by
          have hc := (Subgroup.mem_centralizer_iff.mp hx.2) m hmH
          rw [hc]
          group
        have hxu : u * x * u⁻¹ = x := by
          have hc := habel u huN x hx.1
          rw [hc]
          group
        have hrw : u * m * x * (u * m)⁻¹ = x := by
          calc u * m * x * (u * m)⁻¹ = u * (m * x * m⁻¹) * u⁻¹ := by group
            _ = u * x * u⁻¹ := by rw [hxH]
            _ = x := hxu
        rw [hrw]
        exact hx
      rcases hNmin.2.2 _ hZnormal inf_le_left with hZbot | hZeq
      · -- `C_N(H) = 1`: 極小指数に矛盾する部分群を作る.
        exfalso
        obtain ⟨v, hvN, hv1⟩ : ∃ v ∈ N, v ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hNmin.2.1 (le_bot_iff.mp fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
        have hvC : v ∉ Subgroup.centralizer (H : Set G) := by
          intro hc
          have hmem : v ∈ N ⊓ Subgroup.centralizer (H : Set G) := ⟨hvN, hc⟩
          rw [hZbot, Subgroup.mem_bot] at hmem
          exact hv1 hmem
        let : MulAction ↥H G :=
          MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp H.subtype)
        have hsmul : ∀ (h : ↥H) (x : G), h • x = (h : G) * x * (h : G)⁻¹ := fun _ _ => rfl
        -- 安定化群は真の部分群.
        have hstab_ne : MulAction.stabilizer ↥H v ≠ ⊤ := by
          intro htop
          refine hvC (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
          have hmem : (⟨g, hg⟩ : ↥H) ∈ MulAction.stabilizer ↥H v := by rw [htop]; trivial
          have hfix : g * v * g⁻¹ = v := by
            have := MulAction.mem_stabilizer_iff.mp hmem
            rwa [hsmul] at this
          calc g * v = (g * v * g⁻¹) * g := by group
            _ = v * g := by rw [hfix]
        -- 軌道は `N \ {1}` に含まれる.
        have horbit_sub : MulAction.orbit ↥H v ⊆ (N : Set G) \ {1} := by
          rintro _ ⟨h, rfl⟩
          change (h : G) * v * (h : G)⁻¹ ∈ (N : Set G) \ {1}
          refine ⟨hNnormal.conj_mem v hvN (h : G), ?_⟩
          simp only [Set.mem_singleton_iff]
          intro hone
          apply hv1
          have : v = (h : G)⁻¹ * ((h : G) * v * (h : G)⁻¹) * (h : G) := by group
          rw [this, hone]
          group
        have hncard : (MulAction.orbit ↥H v).ncard ≤ Nat.card ↥N - 1 := by
          have hsub := Set.ncard_le_ncard horbit_sub (Set.toFinite _)
          have hdiff : ((N : Set G) \ {1}).ncard = (N : Set G).ncard - 1 :=
            Set.ncard_sdiff_singleton_of_mem N.one_mem
          rw [hdiff, ← Nat.card_coe_set_eq] at hsub
          exact hsub
        -- `K := N ⊔ (stabilizer の像)` は真部分群で指数が `|N|` 未満.
        set Hv : Subgroup G := (MulAction.stabilizer ↥H v).map H.subtype with hHv
        have hHvH : Hv ≤ H := Subgroup.map_subtype_le _
        have hHvcard : Nat.card ↥Hv = Nat.card ↥(MulAction.stabilizer ↥H v) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ H.subtype
            H.subtype_injective).toEquiv).symm
        have hindexH : H.index = Nat.card ↥N := by
          have h := Ch02.index_mul_card_inf_eq_card_of_sup_eq_top (N := N) (A := H) hsup
          rwa [hinf, Subgroup.card_bot, mul_one] at h
        -- `|N ⊔ Hv| = |N| * |Hv|`
        have hNHvinf : N ⊓ Hv = ⊥ :=
          le_bot_iff.mp (hinf ▸ inf_le_inf_left N hHvH)
        have hcardK : Nat.card ↥(N ⊔ Hv) = Nat.card ↥N * Nat.card ↥Hv := by
          have h1 := Ch01.card_mul_card_inf N Hv
          rw [hNHvinf, Subgroup.card_bot, mul_one] at h1
          rw [← h1, ← Subgroup.normal_mul, SetLike.coe_sort_coe]
        have hcardG : Nat.card ↥N * Nat.card ↥H = Nat.card G := by
          have h1 := Ch01.card_mul_card_inf N H
          rw [hinf, Subgroup.card_bot, mul_one] at h1
          rw [← h1, ← Subgroup.normal_mul, SetLike.coe_sort_coe, hsup]
          simp
        have hstabcard : Nat.card ↥(MulAction.stabilizer ↥H v) *
            (MulAction.stabilizer ↥H v).index = Nat.card ↥H :=
          Subgroup.card_mul_index _
        have hKindex : (N ⊔ Hv).index = (MulAction.stabilizer ↥H v).index := by
          have hmul : (N ⊔ Hv).index * (Nat.card ↥N * Nat.card ↥Hv) = Nat.card G := by
            rw [← hcardK, mul_comm]
            exact Subgroup.card_mul_index _
          have hmul2 : (MulAction.stabilizer ↥H v).index * (Nat.card ↥N * Nat.card ↥Hv)
              = Nat.card G := by
            rw [hHvcard, ← hcardG, ← hstabcard]
            ring
          exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos)
            (hmul.trans hmul2.symm)
        have hKne : N ⊔ Hv ≠ ⊤ := by
          intro htop
          have hstabtop : MulAction.stabilizer ↥H v = ⊤ := by
            have h1 : (N ⊔ Hv).index = 1 := by rw [htop]; exact Subgroup.index_top
            rw [hKindex] at h1
            exact Subgroup.index_eq_one.mp h1
          exact hstab_ne hstabtop
        -- 極小性と軌道の評価が衝突する.
        have hle := hmin _ hKne
        rw [hindexH, hKindex, MulAction.index_stabilizer] at hle
        have hNpos : 1 ≤ Nat.card ↥N := Nat.card_pos
        omega
      · -- `C_N(H) = N`: `N` が `H` を中心化するので `H ⊴ G`.
        have hNC : N ≤ Subgroup.centralizer (H : Set G) := by
          rw [← hZeq]
          exact inf_le_right
        refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
        rw [← hsup]
        exact sup_le (hNC.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer

/-- **Isaacs Problem 3B.15** (Berkovich, 書籍 p. 86): 有限**可解**群 `G` の真部分群のうち
指数が最小のものは `G` で正規.

`|G|` の強帰納法. 最小指数の `H` は極大なので, 極小正規部分群 `N` について
`N ≤ H` なら `G ⧸ N` に落として帰納法, `N ≰ H` なら `G = N ⋊ H` で `N` への `H` の共役作用を見る.
`C_N(H) = N` なら `N` が `H` を正規化するので `H ⊴ G`. `C_N(H) = 1` の場合は
`v ∈ N \ {1}` の安定化群 `H_v < H` を取ると `N ⊔ H_v` は真部分群で,
その指数は軌道の大きさ `≤ |N| - 1 < |N| = [G : H]` となり `H` の最小性に矛盾する. -/
theorem normal_of_index_minimal {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    {H : Subgroup G} (hHne : H ≠ ⊤)
    (hmin : ∀ K : Subgroup G, K ≠ ⊤ → H.index ≤ K.index) : H.Normal :=
  normal_of_index_minimal_aux (Nat.card G) H le_rfl hHne hmin

end

end OddOrder.Isaacs.Ch03
