/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Problems2D
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems

/-!
# Isaacs Chapter 3 — Problems §3B (前半: 可解性の判定)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3 の章末演習 §3B (pp. 84-86) のうち
**3B.1-3B.3** (極大部分群の素数冪指数 / abelian 因子の subnormal 列 / 合成因子と可解性)。
残り (3B.4-3B.15) は [`Problems3B.lean`](Problems3B.lean) にある (本ファイルを import)。
-/

namespace OddOrder.Isaacs.Ch03

open scoped commutatorElement

universe u v

section /- Problems 3B: solvability criteria (pp. 84-86) -/


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
    ∀ {G : Type u} [Group G] [Finite G] [Group.IsSolvable G] (M : Subgroup G),
      Nat.card G ≤ n → IsCoatom M → IsPrimePow M.index := by
  induction n with
  | zero =>
    intro G _ _ _ M hcard _
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ _ M hcard hM
    -- `M ≠ ⊤` から `G` は非自明.
    have hnt : Nontrivial G := by
      rcases subsingleton_or_nontrivial G with hs | hn
      · exact absurd (by ext x; simp [Subsingleton.elim x (1 : G)] : M = ⊤) hM.1
      · exact hn
    have hMone : M.index ≠ 1 := fun h => hM.1 (Subgroup.index_eq_one.mp h)
    -- minimal normal subgroup `N` を取る (Thm 3.11 で elementary abelian `p`-group).
    obtain ⟨N, hNmin, -⟩ :=
      Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    have hNnormal : N.Normal := hNmin.1
    obtain ⟨p, hp, hEA⟩ := minimal_normal_isElementaryAbelian_of_isSolvable hNmin
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEA.isPGroup
    by_cases hNM : N ≤ M
    · -- `N ≤ M`: 商 `G ⧸ N` に落とす. 指数は不変, 位数は真に小さい.
      have hindex : (M.map (QuotientGroup.mk' N)).index = M.index :=
        Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N)
          (by rw [QuotientGroup.ker_mk']; exact hNM)
      have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNmin.2.1
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
(Thm 3.11 = `minimal_normal_isElementaryAbelian_of_isSolvable` で `N` は elementary abelian
`p`-group). `N ≤ M` なら対応定理で `G ⧸ N` の極大部分群 `M/N` に落ち, 指数が保たれる
(`Subgroup.index_map_eq`) ので帰納法の仮定が使える. `N ≰ M` なら `M` の極大性から
`M ⊔ N = ⊤` で, `|G : M| · |N ⊓ M| = |N|` (Problem 2D の
`index_mul_card_inf_eq_card_of_sup_eq_top`) より `|G : M|` が `p^k` を割る.

⚠ 可解性は本質的 (例: `A₅` の極大部分群 `A₄` は指数 5 だが `A₅` は非可解 — この場合たまたま
素数冪だが, 一般の非可解群では指数 6 の極大部分群などが現れる). -/
theorem index_isPrimePow_of_isCoatom {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
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
  let := normal_subgroupOf_of_commutator_le h
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

有限性は不要 (mathlib の `Group.IsSolvable` は導来列が有限段で `⊥` になること). -/
theorem isSolvable_of_commutator_series {G : Type*} [Group G] {r : ℕ} (N : ℕ → Subgroup G)
    (h0 : N 0 = ⊥) (hr : N r = ⊤) (hstep : ∀ i < r, ⁅N (i + 1), N (i + 1)⁆ ≤ N i) :
    Group.IsSolvable G := by
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
    Group.IsSolvable G ↔ ∀ i < r, (Nat.card (Q i)).Prime := by
  constructor
  · intro hsol i hi
    have := hsimple i hi
    have : Group.IsSolvable (Q i) := Group.isSolvable_of_surjective (hsurj i hi)
    have hcomm : ∀ a b : Q i, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
    let : CommGroup (Q i) := { (inferInstance : Group (Q i)) with mul_comm := hcomm }
    exact IsSimpleGroup.prime_card
  · intro hprime
    refine isSolvable_of_commutator_series N h0 hr fun i hi => ?_
    have : Fact (Nat.card (Q i)).Prime := ⟨hprime i hi⟩
    have : IsCyclic (Q i) := isCyclic_of_prime_card (p := Nat.card (Q i)) rfl
    have hcomm : ∀ a b : Q i, a * b = b * a := (IsCyclic.commGroup (α := Q i)).mul_comm
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hmemker : ⁅(⟨x, hx⟩ : ↥(N (i + 1))), (⟨y, hy⟩ : ↥(N (i + 1)))⁆ ∈ (f i).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    rw [hker i hi] at hmemker
    simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using hmemker

end

end OddOrder.Isaacs.Ch03
