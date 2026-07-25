/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Problems2D
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems

/-!
# Isaacs Chapter 3 — Problems §3B (Schur-Zassenhaus と可解群)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3 の章末演習 §3B (pp. 84-86)。
§3B は Schur-Zassenhaus 定理 (Thm 3.8) と可解群 (Thm 3.11 / 3.12) を扱う節の演習。

方針は Ch.1/Ch.2/§3A の `Problems*.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch03

open scoped commutatorElement

universe u v

section /- Problems 3B: Schur-Zassenhaus and solvable groups (pp. 84-86) -/

/-! ### Problem 3B.1 — 有限可解群の極大部分群は素数冪指数

教科書の hint どおり minimal normal subgroup + `|G|` に関する帰納法。`N` を minimal normal
とすると Thm 3.11 より `N` は elementary abelian `p`-group。`N ≤ M` なら `G/N` に落として
帰納法 (`|G/N : M/N| = |G : M|`)、`N ≰ M` なら極大性から `M ⊔ N = ⊤` で
`|G : M| = |N : N ⊓ M|` が `|N| = p^k` を割る。 -/

/-- `N ≤ M` かつ `M` が極大なら, 商群 `G ⧸ N` の中で `M` の像も極大 (対応定理)。 -/
theorem isCoatom_map_mk'_of_isCoatom {G : Type*} [Group G] {N M : Subgroup G} [N.Normal]
    (hNM : N ≤ M) (hM : IsCoatom M) : IsCoatom (M.map (QuotientGroup.mk' N)) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  -- 対応定理の核: `N ≤ M` なので像を引き戻すと `M` に戻る.
  have hcm : (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = M := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr hNM
  constructor
  · intro htop
    rw [htop, Subgroup.comap_top] at hcm
    exact hM.1 hcm.symm
  · intro K hK
    have hlt : M < K.comap (QuotientGroup.mk' N) := by
      refine lt_of_le_of_ne (hcm ▸ Subgroup.comap_mono hK.le) fun h => ?_
      have : K = M.map (QuotientGroup.mk' N) := by
        rw [← Subgroup.map_comap_eq_self_of_surjective hsurj K, ← h]
      exact absurd this hK.ne'
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj K, hM.2 _ hlt,
      Subgroup.map_top_of_surjective _ hsurj]

/-- Problem 3B.1 の帰納本体 (`Nat.card G ≤ n` に関する強帰納法; 群の型自体が帰納で変わるので
`n` を外側に取って型を全称化する)。 -/
theorem index_isPrimePow_of_isCoatom_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [Finite G] [IsSolvable G] (M : Subgroup G),
      Nat.card G ≤ n → IsCoatom M → IsPrimePow M.index := by
  induction n with
  | zero =>
    intro G _ _ _ M hcard _
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ _ M hcard hM
    -- `M ≠ ⊤` から `G` は非自明.
    haveI hnt : Nontrivial G := by
      rcases subsingleton_or_nontrivial G with hs | hn
      · exact absurd (by ext x; simp [Subsingleton.elim x (1 : G)] : M = ⊤) hM.1
      · exact hn
    have hMone : M.index ≠ 1 := fun h => hM.1 (Subgroup.index_eq_one.mp h)
    -- minimal normal subgroup `N` を取る (Thm 3.11 で elementary abelian `p`-group).
    obtain ⟨N, hNmin, -⟩ :=
      Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    haveI hNnormal : N.Normal := hNmin.1
    obtain ⟨p, hp, hEA⟩ := solvable_minimal_normal_isElementaryAbelian hNmin
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEA.isPGroup
    by_cases hNM : N ≤ M
    · -- `N ≤ M`: 商 `G ⧸ N` に落とす. 指数は不変, 位数は真に小さい.
      have hindex : (M.map (QuotientGroup.mk' N)).index = M.index :=
        Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N)
          (by rw [QuotientGroup.ker_mk']; exact hNM)
      haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNmin.2.1
      have hNcard : 1 < Nat.card ↥N := Finite.one_lt_card
      have hprod : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
      have hquot : Nat.card (G ⧸ N) ≤ n := by
        have h2 : 2 * N.index ≤ Nat.card ↥N * N.index := Nat.mul_le_mul_right _ hNcard
        rw [← Subgroup.index_eq_card]
        omega
      rw [← hindex]
      exact ih _ hquot (isCoatom_map_mk'_of_isCoatom hNM hM)
    · -- `N ≰ M`: 極大性から `M ⊔ N = ⊤`, よって `|G : M|` は `|N| = p^k` を割る.
      have hsup : N ⊔ M = ⊤ := by
        rw [sup_comm]
        refine hM.2 _ (lt_of_le_of_ne le_sup_left fun h => hNM ?_)
        exact h ▸ le_sup_right
      have hdvd : M.index ∣ p ^ k := by
        rw [← hk]
        exact ⟨_, (Ch02.index_mul_card_inf_eq_card_of_sup_eq_top hsup).symm⟩
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      refine ⟨p, j, hp.prime, ?_, hjeq.symm⟩
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact absurd (by simpa using hjeq) hMone
      · exact hpos

/-- **Isaacs Problem 3B.1** (書籍 p. 84): 有限**可解**群の極大部分群の指数は**素数冪**.

証明は教科書の hint どおり `|G|` に関する帰納法 + minimal normal subgroup `N`
(Thm 3.11 = `solvable_minimal_normal_isElementaryAbelian` で `N` は elementary abelian
`p`-group). `N ≤ M` なら対応定理で `G ⧸ N` の極大部分群 `M/N` に落ち, 指数が保たれる
(`Subgroup.index_map_eq`) ので帰納法の仮定が使える. `N ≰ M` なら `M` の極大性から
`M ⊔ N = ⊤` で, `|G : M| · |N ⊓ M| = |N|` (Problem 2D の
`index_mul_card_inf_eq_card_of_sup_eq_top`) より `|G : M|` が `p^k` を割る.

⚠ 可解性は本質的 (例: `A₅` の極大部分群 `A₄` は指数 5 だが `A₅` は非可解 — この場合たまたま
素数冪だが, 一般の非可解群では指数 6 の極大部分群などが現れる). -/
theorem index_isPrimePow_of_isCoatom {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {M : Subgroup G} (hM : IsCoatom M) : IsPrimePow M.index :=
  index_isPrimePow_of_isCoatom_aux (Nat.card G) M le_rfl hM

/-! ### Problem 3B.2 — abelian 因子をもつ subnormal 列があれば可解

`1 = N₀ ⊲ N₁ ⊲ ⋯ ⊲ Nᵣ = G` で各因子 `Nᵢ / Nᵢ₋₁` が abelian なら `G` は可解 (各 `Nᵢ` が
`G` で正規である必要は**ない**)。導来列 `G⁽ᵏ⁾` が `N_{r-k}` 以下であることを `k` の帰納法で
示せばよい。

Lean では「`Nᵢ ⊴ Nᵢ₊₁` かつ商 abelian」を交換子の形 `⁅Nᵢ₊₁, Nᵢ₊₁⁆ ≤ Nᵢ` で表す
(下の 2 補題が教科書形との往復を与える)。この形なら包含 `Nᵢ ≤ Nᵢ₊₁` も正規性も
仮定に要らない (どちらも自動的に従う) ので, 主張は教科書より真に一般。 -/

/-- 商 `H / K` (`K ⊴ H` を `K.subgroupOf H` で表す) が abelian なら `⁅H, H⁆ ≤ K`。 -/
theorem commutator_le_of_quotient_isMulCommutative {G : Type*} [Group G] {H K : Subgroup G}
    [hn : (K.subgroupOf H).Normal] (hab : IsMulCommutative (↥H ⧸ K.subgroupOf H)) :
    ⁅H, H⁆ ≤ K := by
  have hcomm : _root_.commutator ↥H ≤ K.subgroupOf H :=
    hn.quotient_commutative_iff_commutator_le.mp hab
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hmem : ⁅(⟨x, hx⟩ : ↥H), (⟨y, hy⟩ : ↥H)⁆ ∈ K.subgroupOf H :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using hmem

/-- 逆向き: `⁅H, H⁆ ≤ K` なら `K ⊴ H` (`K ≤ H` は不要 — `K.subgroupOf H = (K ⊓ H).subgroupOf H`)。 -/
theorem normal_subgroupOf_of_commutator_le {G : Type*} [Group G] {H K : Subgroup G}
    (h : ⁅H, H⁆ ≤ K) : (K.subgroupOf H).Normal := by
  apply Subgroup.Normal.of_commutator_le
  intro z hz
  refine Subgroup.commutator_le.mpr (fun a _ b _ => ?_) hz
  have : (⁅(a : G), (b : G)⁆) ∈ K :=
    h (Subgroup.commutator_mem_commutator a.2 b.2)
  simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using this

/-- `⁅H, H⁆ ≤ K` なら商 `H / K` は abelian。 -/
theorem quotient_isMulCommutative_of_commutator_le {G : Type*} [Group G] {H K : Subgroup G}
    (h : ⁅H, H⁆ ≤ K) :
    letI := normal_subgroupOf_of_commutator_le h
    IsMulCommutative (↥H ⧸ K.subgroupOf H) := by
  letI := normal_subgroupOf_of_commutator_le h
  refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
  intro z hz
  refine Subgroup.commutator_le.mpr (fun a _ b _ => ?_) hz
  have : (⁅(a : G), (b : G)⁆) ∈ K := h (Subgroup.commutator_mem_commutator a.2 b.2)
  simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using this

/-- **Isaacs Problem 3B.2** (書籍 p. 84): `1 = N₀ ⊲ N₁ ⊲ ⋯ ⊲ Nᵣ = G` で各因子
`Nᵢ₊₁ / Nᵢ` が abelian (`⁅Nᵢ₊₁, Nᵢ₊₁⁆ ≤ Nᵢ` で表す) なら `G` は可解.

⚠ 教科書が注意するとおり **`Nᵢ` が `G` で正規である必要はない** (subnormal 列でよい).
証明は導来列 `G⁽ᵏ⁾ ≤ N_{r-k}` を `k` の帰納法で示すだけ: `G⁽⁰⁾ = ⊤ = Nᵣ` で,
`G⁽ᵏ⁺¹⁾ = ⁅G⁽ᵏ⁾, G⁽ᵏ⁾⁆ ≤ ⁅N_{r-k}, N_{r-k}⁆ ≤ N_{r-k-1}`. `k = r` で `G⁽ʳ⁾ ≤ N₀ = ⊥`.

有限性は不要 (mathlib の `IsSolvable` は導来列が有限段で `⊥` になること). -/
theorem isSolvable_of_commutator_series {G : Type*} [Group G] {r : ℕ} (N : ℕ → Subgroup G)
    (h0 : N 0 = ⊥) (hr : N r = ⊤) (hstep : ∀ i < r, ⁅N (i + 1), N (i + 1)⁆ ≤ N i) :
    IsSolvable G := by
  have key : ∀ k ≤ r, derivedSeries G k ≤ N (r - k) := by
    intro k
    induction k with
    | zero => intro _; simp [hr]
    | succ k ihk =>
      intro hk
      have hidx : r - k = (r - (k + 1)) + 1 := by omega
      calc derivedSeries G (k + 1) = ⁅derivedSeries G k, derivedSeries G k⁆ :=
            derivedSeries_succ G k
        _ ≤ ⁅N (r - k), N (r - k)⁆ :=
            Subgroup.commutator_mono (ihk (by omega)) (ihk (by omega))
        _ ≤ N (r - (k + 1)) := by rw [hidx]; exact hstep _ (by omega)
  exact ⟨⟨r, le_bot_iff.mp (by simpa [h0] using key r le_rfl)⟩⟩

/-! ### Problem 3B.3 — 合成因子が全て素数位数 ⟺ 可解

`1 = N₀ ⊲ N₁ ⊲ ⋯ ⊲ Nᵣ = G` で各因子が**単純**なとき (= 合成列), `G` が可解であることと
全ての因子が素数位数であることは同値。

因子の商群は「抽象的な `Qᵢ` + 全射 `Nᵢ₊₁ ↠ Qᵢ` (核 = `Nᵢ`)」として与える。こうすると
`Nᵢ ⊴ Nᵢ₊₁` の instance を仮説の中で捏ねる必要がなく (核は自動で正規), 主張は
`Qᵢ ≅ Nᵢ₊₁ / Nᵢ` を通じて教科書と同値。 -/

/-- **Isaacs Problem 3B.3** (書籍 p. 84): 合成列 `1 = N₀ ⊲ ⋯ ⊲ Nᵣ = G` (因子 `Qᵢ` が単純)
について, `G` が可解 ⟺ 全ての合成因子 `Qᵢ` が素数位数.

(⟸) 素数位数 ⟹ 巡回 ⟹ abelian なので `⁅Nᵢ₊₁, Nᵢ₊₁⁆ ≤ ker(fᵢ) = Nᵢ`, Problem 3B.2 で可解.
(⟹) `G` 可解 ⟹ 部分群 `Nᵢ₊₁` 可解 ⟹ その全射像 `Qᵢ` 可解. 単純かつ可解な群は abelian
(`IsSimpleGroup.comm_iff_isSolvable`) で, abelian 単純群の位数は素数 (`IsSimpleGroup.prime_card`).

⚠ 教科書の Note にあるとおり, 有限群には合成列が必ず存在し (Jordan-Hölder で因子は一意),
本問は「有限可解群 = 合成因子が全て素数位数の群」を意味する. -/
theorem isSolvable_iff_forall_prime_card_of_simple_factors {G : Type u} [Group G] {r : ℕ}
    (N : ℕ → Subgroup G) (Q : ℕ → Type v) [∀ i, Group (Q i)] [∀ i, Finite (Q i)]
    (f : ∀ i, ↥(N (i + 1)) →* Q i) (hsurj : ∀ i < r, Function.Surjective (f i))
    (hker : ∀ i < r, (f i).ker = (N i).subgroupOf (N (i + 1)))
    (hsimple : ∀ i < r, IsSimpleGroup (Q i)) (h0 : N 0 = ⊥) (hr : N r = ⊤) :
    IsSolvable G ↔ ∀ i < r, (Nat.card (Q i)).Prime := by
  constructor
  · intro hsol i hi
    haveI := hsimple i hi
    haveI : IsSolvable (Q i) := solvable_of_surjective (hsurj i hi)
    have hcomm : ∀ a b : Q i, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
    letI : CommGroup (Q i) := { (inferInstance : Group (Q i)) with mul_comm := hcomm }
    exact IsSimpleGroup.prime_card
  · intro hprime
    refine isSolvable_of_commutator_series N h0 hr fun i hi => ?_
    haveI : Fact (Nat.card (Q i)).Prime := ⟨hprime i hi⟩
    haveI : IsCyclic (Q i) := isCyclic_of_prime_card (p := Nat.card (Q i)) rfl
    have hcomm : ∀ a b : Q i, a * b = b * a := (IsCyclic.commGroup (α := Q i)).mul_comm
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hmemker : ⁅(⟨x, hx⟩ : ↥(N (i + 1))), (⟨y, hy⟩ : ↥(N (i + 1)))⁆ ∈ (f i).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    rw [hker i hi] at hmemker
    simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using hmemker

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
    (hsolv : IsSolvable ↥N ∨ IsSolvable ↥U) :
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
  haveI hPnormal : (P : Subgroup G).Normal := by
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
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
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
  haveI : IsSolvable ↥(Subgroup.zpowers g) :=
    isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := ↥(Subgroup.zpowers g))).comm a b
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
  haveI : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf
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
  have hsolvU : IsSolvable ↥(K₂.subgroupOf H) := by
    haveI : IsSolvable ↥K₂ :=
      isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := ↥K₂)).comm a b
    exact solvable_of_solvable_injective
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
      (∀ M : Subgroup G, IsCoatom M → M.index.Prime) → Nat.card G ≤ n → IsSolvable G := by
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
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpmem⟩
      have hpdvd : p ∣ Nat.card G := Nat.dvd_of_mem_primeFactors hpmem
      have hlarge : ∀ r ∈ (Nat.card G).primeFactors, r ≤ p := fun r hr => Finset.le_max' _ r hr
      obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
      haveI hPnormal : (P : Subgroup G).Normal :=
        sylow_normal_of_forall_isCoatom_index_prime hmax hlarge P
      haveI hPsolv : IsSolvable ↥(P : Subgroup G) := by
        haveI := P.isPGroup'.isNilpotent
        infer_instance
      -- 商 `G ⧸ P` は真に小さく, 同じ仮説を満たす.
      have hPne : (P : Subgroup G) ≠ ⊥ := sylow_ne_bot hpdvd P
      haveI : Nontrivial ↥(P : Subgroup G) :=
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
      haveI : IsSolvable (G ⧸ (P : Subgroup G)) :=
        ih (forall_isCoatom_index_prime_quotient hmax) hquot
      exact solvable_of_ker_le_range ((P : Subgroup G).subtype)
        (QuotientGroup.mk' (P : Subgroup G))
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- **Isaacs Problem 3B.8 前半** (書籍 p. 85): 有限群 `G` の極大部分群の指数がすべて素数なら
`G` は可解.

最大素因数 `p` の Sylow `p`-部分群 `P` は正規 (`sylow_normal_of_forall_isCoatom_index_prime`)
で, 商 `G ⧸ P` も同じ仮説を満たすから帰納法で可解. `P` は `p`-群ゆえ冪零・可解なので `G` も可解. -/
theorem isSolvable_of_forall_isCoatom_index_prime {G : Type u} [Group G] [Finite G]
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.index.Prime) : IsSolvable G :=
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
    haveI : Fact q.Prime := ⟨hq⟩
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
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpmem⟩
      have hpdvd : p ∣ Nat.card G := Nat.dvd_of_mem_primeFactors hpmem
      have hlarge : ∀ r ∈ (Nat.card G).primeFactors, r ≤ p := fun r hr => Finset.le_max' _ r hr
      have hdmem : d ∈ (Nat.card G).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hdprime, hddvd, Nat.card_pos.ne'⟩
      have hqd : q ≤ d := hsmall d hdmem
      have hdp : d ≤ p := Finset.le_max' _ d hdmem
      have hpq : p ≠ q := by omega
      obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
      haveI hPnormal : (P : Subgroup G).Normal :=
        sylow_normal_of_forall_isCoatom_index_prime hmax hlarge P
      have hPne : (P : Subgroup G) ≠ ⊥ := sylow_ne_bot hpdvd P
      haveI : Nontrivial ↥(P : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
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
      haveI := hHbarNormal
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
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(frattini G)) := inferInstance
  set R : Subgroup G := (Q : Subgroup ↥(frattini G)).map (frattini G).subtype with hR_def
  -- Frattini 論法 + `Φ` の非生成性 ⟹ `R ⊴ G`.
  have htop : Subgroup.normalizer ((R : Subgroup G) : Set G) ⊔ frattini G = ⊤ :=
    Sylow.normalizer_sup_eq_top Q
  have hnormtop : Subgroup.normalizer ((R : Subgroup G) : Set G) = ⊤ :=
    frattini_nongenerating htop
  haveI hRnormal : R.Normal := Subgroup.normalizer_eq_top_iff.mp hnormtop
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

end

end OddOrder.Isaacs.Ch03
