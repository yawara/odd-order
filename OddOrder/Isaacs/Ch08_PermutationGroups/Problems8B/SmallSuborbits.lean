/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Primitive
import OddOrder.GroupTheory.CyclicSylowBurnside
import OddOrder.GroupTheory.FixedPointFreeConjugation
import OddOrder.Isaacs.Ch08_PermutationGroups.RegularNormal
import OddOrder.Isaacs.Ch08_PermutationGroups.Subdegrees

/-!
# Isaacs Problems 8B (pp. 248–249) — 点安定化群の小さい suborbit

**Problems 8B.5–8B.7**。原始置換群の点安定化群 `G_α` が `Ω ∖ {α}` 上に小さい軌道
(長さ 1 / 2 / 3) をもつとき, `G_α` の構造が強く制限される。

## Main results

- `prime_card_of_isCoatom_bot`, `stabilizer_eq_bot_and_prime_card_of_fixed_point` —
  **8B.5**: 固定点をもてば `G_α = 1` で `|G|` は素数。
- `eq_bot_of_normal_le_stabilizer`, `card_stabilizer_eq_two_of_suborbit_ncard_eq_two` —
  **8B.6 前半**: 長さ 2 の軌道なら `|G_α| = 2`。
- `odd_card_of_card_stabilizer_eq_two`, `exists_regular_normal_of_card_stabilizer_eq_two`,
  `prime_card_of_card_stabilizer_eq_two` — **8B.6 の次数部分**: `|Ω|` は奇素数。
  ⚠ `G ≅ D₂ₚ` の同型そのものは未形式化。
- `oddCore`, `isPGroup_two_of_oddCore_eq_bot`, `smul_eq_self_of_odd_of_ncard_le_two`,
  `stabilizer_le_normalizer_oddCore`,
  `card_stabilizer_eq_three_mul_two_pow_of_suborbit_ncard_eq_three` —
  **8B.7**: 長さ 3 の軌道なら `|G_α| = 3 · 2^e`。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8B (pp. 248-249) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8B.5 — 点安定化群が他の点を固定すれば自明で `|G|` は素数 -/

/-- 部分群が `⊥` と `⊤` しかない有限群は**素数位数**。

`Nat.card G` の素因数 `p` を取り Cauchy で位数 `p` の元 `y` を作ると
`⊥ < ⟨y⟩` なので `⟨y⟩ = ⊤`, すなわち `|G| = orderOf y = p`。 -/
lemma prime_card_of_isCoatom_bot [Finite G] (h : IsCoatom (⊥ : Subgroup G)) :
    (Nat.card G).Prime := by
  classical
  haveI := Fintype.ofFinite G
  have hnt : Nontrivial G := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact h.1 (le_antisymm bot_le fun x _ =>
      Subgroup.mem_bot.mpr (Subsingleton.elim x 1))
  have hcard1 : Nat.card G ≠ 1 := fun hc =>
    (not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp hc).1) hnt
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := G) p
    (by rwa [← Nat.card_eq_fintype_card])
  have hy1 : y ≠ 1 := fun hc => hp.ne_one (by rw [hc, orderOf_one] at hy; exact hy.symm)
  have htop : Subgroup.zpowers y = ⊤ :=
    h.2 _ (bot_lt_iff_ne_bot.mpr (Subgroup.zpowers_ne_bot.mpr hy1))
  have hcard : Nat.card G = p := by
    rw [← hy, ← Nat.card_zpowers y, htop]
    simp
  rw [hcard]
  exact hp

/-- **Isaacs Problem 8B.5** (p. 249) 🎉: 原始置換群 `G` の点安定化群 `H = G_α` が
`Ω ∖ {α}` に固定点をもてば, **`H = 1` かつ `|G|` は素数**。

原始性より `H` は極大部分群 (`IsCoatom`)。`H ≤ G_β` で `G_β ≠ G` (推移性 + `|Ω| ≥ 2`)
だから `H = G_β`。`g • α = β` なる `g` は `g ∉ H` かつ `g ∈ N_G(H)` なので
`H < N_G(H)`, 極大性から `N_G(H) = G`, すなわち **`H ⊴ G`**。正規かつ `H ≤ G_α` なら
`H` はすべての点を固定するので, 忠実性から `H = 1`。すると `⊥` が極大部分群になり
`|G|` は素数。 -/
theorem stabilizer_eq_bot_and_prime_card_of_fixed_point [Finite G] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α β : Ω} (hαβ : α ≠ β)
    (hfix : ∀ h ∈ stabilizer G α, h • β = β) :
    stabilizer G α = ⊥ ∧ (Nat.card G).Prime := by
  have hcoatom : IsCoatom (stabilizer G α) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  -- `G_β ≠ G` (さもなくば推移性から `Ω` が 1 点)。
  have hβtop : stabilizer G β ≠ ⊤ := by
    intro hc
    obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
    have hall : ∀ γ : Ω, γ = β := fun γ => by
      obtain ⟨g, hg⟩ := exists_smul_eq G β γ
      rw [← hg]
      exact mem_stabilizer_iff.mp (hc ▸ Subgroup.mem_top g)
    exact hxy ((hall x).trans (hall y).symm)
  -- 極大性から `G_α = G_β`。
  have hle : stabilizer G α ≤ stabilizer G β := fun h hh => mem_stabilizer_iff.mpr (hfix h hh)
  have heq : stabilizer G α = stabilizer G β :=
    (lt_or_eq_of_le hle).resolve_left fun hlt => hβtop (hcoatom.2 _ hlt)
  -- `g • α = β` なる `g` は `N_G(G_α)` に入るが `G_α` には入らない。
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  have hgnot : g ∉ stabilizer G α := fun hc => hαβ (by rw [← hg, mem_stabilizer_iff.mp hc])
  have hconj : ∀ h : G, h ∈ stabilizer G α ↔ g⁻¹ * h * g ∈ stabilizer G α := by
    intro h
    refine (Iff.of_eq (by rw [heq])).trans ?_
    rw [← hg]
    simp only [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  have hgnorm : g ∈ Subgroup.normalizer (stabilizer G α) :=
    Subgroup.mem_normalizer_iff''.mpr hconj
  haveI hnormal : (stabilizer G α).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact hcoatom.2 _ (lt_of_le_of_ne Subgroup.le_normalizer fun hc => hgnot (hc ▸ hgnorm))
  -- 正規な点安定化群はすべての点を固定 ⟹ 忠実性から自明。
  have htriv : ∀ h ∈ stabilizer G α, ∀ γ : Ω, h • γ = γ := by
    intro h hh γ
    obtain ⟨k, hk⟩ := exists_smul_eq G α γ
    have hmem : k⁻¹ * h * k ∈ stabilizer G α := by
      simpa using hnormal.conj_mem h hh k⁻¹
    rw [← hk, ← mul_smul, show h * k = k * (k⁻¹ * h * k) by group, mul_smul,
      mem_stabilizer_iff.mp hmem]
  have hbot : stabilizer G α = ⊥ :=
    le_antisymm (fun h hh => Subgroup.mem_bot.mpr
      (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun γ => by rw [htriv h hh γ, one_smul])) bot_le
  exact ⟨hbot, prime_card_of_isCoatom_bot (hbot ▸ hcoatom)⟩

/-! ### Problem 8B.6 — 点安定化群が長さ 2 の軌道をもつ場合 -/

/-- 推移的な忠実作用では, 点安定化群に含まれる**正規**部分群は自明。 -/
lemma eq_bot_of_normal_le_stabilizer [FaithfulSMul G Ω] [IsPretransitive G Ω]
    {D : Subgroup G} [hD : D.Normal] {α : Ω} (hle : D ≤ stabilizer G α) : D = ⊥ := by
  refine le_antisymm (fun h hh => Subgroup.mem_bot.mpr ?_) bot_le
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun γ => ?_
  obtain ⟨k, hk⟩ := exists_smul_eq G α γ
  have hmem : k⁻¹ * h * k ∈ D := by simpa using hD.conj_mem h hh k⁻¹
  rw [one_smul, ← hk, ← mul_smul, show h * k = k * (k⁻¹ * h * k) by group, mul_smul,
    mem_stabilizer_iff.mp (hle hmem)]

/-- **Isaacs Problem 8B.6** (p. 249) 前半 🎉: 原始置換群 `G` の点安定化群 `G_α` が
`Ω ∖ {α}` 上に**長さ 2 の軌道**をもてば `|G_α| = 2`。

`D := G_α ⊓ G_β` (`β` はその軌道の点) は `G_α` の中で指数 2 なので `G_α ≤ N(D)`;
推移性から `|G_α| = |G_β|` なので `D` は `G_β` の中でも指数 2 で `G_β ≤ N(D)`。
`G_β ≰ G_α` (指数の勘定) と `G_α` の極大性から `G_α ⊔ G_β = G`, したがって
`N(D) = G` すなわち `D ⊴ G`。点安定化群に含まれる正規部分群は自明なので `D = 1`,
よって `|G_α| = 2 · |D| = 2`。 -/
theorem card_stabilizer_eq_two_of_suborbit_ncard_eq_two [Finite G] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α β : Ω}
    (hsub : Set.ncard (orbit ↥(stabilizer G α) β) = 2) :
    Nat.card ↥(stabilizer G α) = 2 := by
  have hcoatom : IsCoatom (stabilizer G α) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  have hDα : stabilizer G β ⊓ stabilizer G α ≤ stabilizer G α := inf_le_right
  have hDβ : stabilizer G β ⊓ stabilizer G α ≤ stabilizer G β := inf_le_left
  have hDpos : 0 < Nat.card ↥(stabilizer G β ⊓ stabilizer G α) := Nat.card_pos
  -- `D` は `G_α` の中で指数 2。
  have hidxα : ((stabilizer G β ⊓ stabilizer G α).subgroupOf (stabilizer G α)).index = 2 := by
    rw [Subgroup.inf_subgroupOf_right, ← Subgroup.relIndex, ← ncard_suborbit_eq_relIndex]
    exact hsub
  have hcardD : ∀ K : Subgroup G, (h : stabilizer G β ⊓ stabilizer G α ≤ K) →
      ((stabilizer G β ⊓ stabilizer G α).subgroupOf K).index *
        Nat.card ↥(stabilizer G β ⊓ stabilizer G α) = Nat.card ↥K := by
    intro K h
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
    exact Subgroup.index_mul_card _
  have hcardα : 2 * Nat.card ↥(stabilizer G β ⊓ stabilizer G α) = Nat.card ↥(stabilizer G α) := by
    rw [← hidxα]; exact hcardD _ hDα
  have hcardeq : Nat.card ↥(stabilizer G α) = Nat.card ↥(stabilizer G β) :=
    card_stabilizer_eq α β
  -- `D` は `G_β` の中でも指数 2。
  have hidxβ : ((stabilizer G β ⊓ stabilizer G α).subgroupOf (stabilizer G β)).index = 2 := by
    refine Nat.eq_of_mul_eq_mul_right hDpos ?_
    rw [hcardD _ hDβ, ← hcardeq, ← hcardα]
  -- 両方の点安定化群が `N(D)` に含まれる。
  have hlenα : stabilizer G α ≤ Subgroup.normalizer
      ((stabilizer G β ⊓ stabilizer G α : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDα).mp
      (Subgroup.normal_of_index_eq_two hidxα)
  have hlenβ : stabilizer G β ≤ Subgroup.normalizer
      ((stabilizer G β ⊓ stabilizer G α : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDβ).mp
      (Subgroup.normal_of_index_eq_two hidxβ)
  -- `G_β ≰ G_α` (さもなくば `D = G_β` で位数の勘定が破綻)。
  have hnotle : ¬ stabilizer G β ≤ stabilizer G α := by
    intro hle
    have hDeq : stabilizer G β ⊓ stabilizer G α = stabilizer G β := inf_eq_left.mpr hle
    have hpos : 0 < Nat.card ↥(stabilizer G β) := Nat.card_pos
    rw [hDeq, hcardeq] at hcardα
    omega
  -- 極大性 ⟹ `G_α ⊔ G_β = ⊤` ⟹ `D ⊴ G`。
  haveI : (stabilizer G β ⊓ stabilizer G α).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine eq_top_iff.mpr ?_
    have hjoin : stabilizer G α ⊔ stabilizer G β = ⊤ :=
      hcoatom.2 _ (lt_of_le_of_ne le_sup_left fun hc => hnotle (hc ▸ le_sup_right))
    exact hjoin ▸ sup_le hlenα hlenβ
  have hDbot : stabilizer G β ⊓ stabilizer G α = ⊥ := eq_bot_of_normal_le_stabilizer hDα
  rw [← hcardα, hDbot]
  simp

/-! ### Problem 8B.6 後半への準備 — 正則正規部分群の存在 -/

/-- `|G_α| = 2` の原始置換群では, 相異なる 2 点の安定化群は自明にしか交わらない。 -/
lemma inf_stabilizer_eq_bot_of_card_stabilizer_eq_two [Finite G] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α β : Ω} (hαβ : α ≠ β)
    (hcard : Nat.card ↥(stabilizer G α) = 2) :
    stabilizer G α ⊓ stabilizer G β = ⊥ := by
  have hnotle : ¬ stabilizer G α ≤ stabilizer G β := by
    intro hle
    have hbot := (stabilizer_eq_bot_and_prime_card_of_fixed_point hαβ
      fun h hh => mem_stabilizer_iff.mp (hle hh)).1
    rw [hbot] at hcard
    simp at hcard
  obtain ⟨t, htα, htβ⟩ := SetLike.not_le_iff_exists.mp hnotle
  have ht1 : t ≠ 1 := fun hc => htβ (hc ▸ Subgroup.one_mem _)
  refine le_antisymm (fun s hs => Subgroup.mem_bot.mpr ?_) bot_le
  obtain ⟨hsα, hsβ⟩ := Subgroup.mem_inf.mp hs
  by_contra hs1
  refine htβ ?_
  have huniq := (Nat.card_eq_two_iff' (1 : ↥(stabilizer G α))).mp hcard
  have hst : s = t := congrArg Subtype.val
    (huniq.unique (y₁ := ⟨s, hsα⟩) (y₂ := ⟨t, htα⟩)
      (fun hc => hs1 (congrArg Subtype.val hc)) fun hc => ht1 (congrArg Subtype.val hc))
  exact hst ▸ hsβ

/-- `|G_α| = 2` の原始置換群では **`|Ω|` は奇数**。

`G_α` の非自明元は `α` しか固定しないので `Fix(G_α) = {α}`, したがって `2`-群 `G_α` の
固定点公式 `|Ω| ≡ |Fix(G_α)| = 1 (mod 2)` から従う。 -/
lemma odd_card_of_card_stabilizer_eq_two [Finite G] [Finite Ω] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) : Odd (Nat.card Ω) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥(stabilizer G α) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hfix : MulAction.fixedPoints ↥(stabilizer G α) Ω = {α} := by
    ext γ
    simp only [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro hγ
      by_contra hne
      have hbot := (stabilizer_eq_bot_and_prime_card_of_fixed_point (Ne.symm hne)
        fun h hh => hγ ⟨h, hh⟩).1
      rw [hbot] at hcard
      simp at hcard
    · rintro rfl
      exact fun s => mem_stabilizer_iff.mp s.2
  have hmod := hpg.card_modEq_card_fixedPoints (α := Ω)
  rw [hfix] at hmod
  simp only [Nat.card_eq_fintype_card, Set.card_singleton] at hmod
  rcases Nat.even_or_odd (Nat.card Ω) with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := he
    have : Nat.card Ω % 2 = 1 % 2 := hmod
    omega
  · exact ho

/-- **8B.6 の構造定理**: `|G_α| = 2` の原始置換群には `Ω` に**正則**に作用する正規部分群
`K` (位数 `|Ω|`) がある。

`|Ω|` が奇数 (`odd_card_of_card_stabilizer_eq_two`) なので `G_α` (位数 2) は巡回 Sylow
2-部分群で, Burnside の正規 `p`-補元定理
(`exists_normal_complement_of_isCyclic_sylow`) が位数 `|Ω|` の正規補元 `K` を与える。
`|K|` は奇数なので `K ⊓ G_α = 1` で半正則, 位数が `|Ω|` に一致するので正則。 -/
theorem exists_regular_normal_of_card_stabilizer_eq_two [Finite G] [Finite Ω]
    [FaithfulSMul G Ω] [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.card ↥K = Nat.card Ω ∧
      K ⊓ stabilizer G α = ⊥ ∧ Function.Bijective (smulBase K α) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card Ω) := odd_card_of_card_stabilizer_eq_two hcard
  have hΩ2 : ¬ (2 ∣ Nat.card Ω) := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hG : Nat.card Ω * 2 = Nat.card G := by
    rw [← hcard, ← index_stabilizer_of_transitive G α]
    exact Subgroup.index_mul_card _
  -- `G_α` は Sylow 2-部分群。
  have hfact : Nat.card ↥(stabilizer G α) = 2 ^ (Nat.card G).factorization 2 := by
    have hΩpos : Nat.card Ω ≠ 0 := Nat.card_pos.ne'
    have hf1 : (Nat.card G).factorization 2 = 1 := by
      rw [← hG, Nat.factorization_mul hΩpos two_ne_zero, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hΩ2, zero_add,
        Nat.Prime.factorization_self Nat.prime_two]
    rw [hcard, hf1, pow_one]
  set P : Sylow 2 G := Sylow.ofCard (stabilizer G α) hfact with hPdef
  have hPcoe : (P : Subgroup G) = stabilizer G α := Sylow.coe_ofCard _ hfact
  have hPcyc : IsCyclic ↥(P : Subgroup G) := by
    rw [hPcoe]
    exact isCyclic_of_prime_card (p := 2) hcard
  obtain ⟨K, hKnormal, hKcard, hKodd⟩ :=
    OddOrder.GroupTheory.exists_normal_complement_of_isCyclic_sylow P hPcyc
      (by rw [hPcoe, hcard, Nat.totient_two]; exact Nat.coprime_one_right _)
  rw [hPcoe, hcard] at hKcard
  haveI := hKnormal
  have hKΩ : Nat.card ↥K = Nat.card Ω := by omega
  -- `|K|` は奇数なので `K ⊓ G_α = 1`。
  have hinf : K ⊓ stabilizer G α = ⊥ := by
    refine le_antisymm (fun x hx => Subgroup.mem_bot.mpr ?_) bot_le
    obtain ⟨hxK, hxα⟩ := Subgroup.mem_inf.mp hx
    by_contra hx1
    have hdvd2 : orderOf x ∣ 2 := by
      rw [← hcard, ← Subgroup.orderOf_mk x hxα]
      exact orderOf_dvd_natCard _
    have hdvdK : orderOf x ∣ Nat.card ↥K := by
      rw [← Subgroup.orderOf_mk x hxK]
      exact orderOf_dvd_natCard _
    have h2 : orderOf x = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    exact hKodd (h2 ▸ hdvdK)
  refine ⟨K, hKnormal, hKΩ, hinf, ?_⟩
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, hKΩ⟩
  exact (injective_smulBase_iff_disjoint_stabilizer K α).mpr hinf

/-- **Isaacs Problem 8B.6 の構造データ** 🎉: `|G_α| = 2` の原始置換群では, `Ω` に正則に
作用する正規部分群 `K` (位数 `|Ω|`) と `G_α` の生成元 `t` (対合) が取れ, `t` は `K` を
**反転**する (`t k t⁻¹ = k⁻¹`)。

`G_α = {1, t}` の非自明元 `t` は `α` しか固定しない
(`inf_stabilizer_eq_bot_of_card_stabilizer_eq_two`) ので, `K` が半正則であることから `t` は
`K` に共役で**固定点なく**作用する。あとは `conj_eq_inv_of_orderTwo_of_fixedPointFree` が
反転を与える。`K ⊔ G_α = ⊤` は `G_α` の極大性 (原始性) と `K ≠ ⊥` から。 -/
theorem exists_inverting_involution_of_card_stabilizer_eq_two [Finite G] [Finite Ω]
    [FaithfulSMul G Ω] [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) :
    ∃ (K : Subgroup G) (t : G), K.Normal ∧ Nat.card ↥K = Nat.card Ω ∧
      K ⊓ stabilizer G α = ⊥ ∧ K ⊔ stabilizer G α = ⊤ ∧
      stabilizer G α = Subgroup.zpowers t ∧ orderOf t = 2 ∧
      ∀ k ∈ K, t * k * t⁻¹ = k⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKnormal, hKΩ, hKinf, -⟩ :=
    exists_regular_normal_of_card_stabilizer_eq_two hcard
  haveI := hKnormal
  have hΩ2 : 2 ≤ Nat.card Ω := by
    have h0 : Nat.card Ω ≠ 0 := Nat.card_pos.ne'
    have h1 : Nat.card Ω ≠ 1 := fun hc =>
      absurd (Nat.card_eq_one_iff_unique.mp hc).1 (not_subsingleton Ω)
    omega
  -- `G_α = {1, t}` と `t² = 1`。
  obtain ⟨⟨t, htα⟩, ht1, htuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(stabilizer G α))).mp hcard
  have ht1' : t ≠ 1 := fun hc => ht1 (Subtype.ext hc)
  have htt : t * t = 1 := by
    have hinvmem : (⟨t, htα⟩ : ↥(stabilizer G α))⁻¹ = ⟨t, htα⟩ := by
      refine htuniq _ fun hc => ht1' ?_
      have hv : t⁻¹ = 1 := congrArg Subtype.val hc
      simpa using hv
    have hinv : t⁻¹ = t := congrArg Subtype.val hinvmem
    nth_rewrite 1 [← hinv]
    rw [inv_mul_cancel]
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1'
  have hzt : stabilizer G α = Subgroup.zpowers t :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htα)
      (by rw [Nat.card_zpowers, htord, hcard])).symm
  have htα' : t • α = α := mem_stabilizer_iff.mp htα
  -- `t` は `α` しか固定しない。
  have htfix : ∀ γ : Ω, t • γ = γ → γ = α := by
    intro γ hγ
    by_contra hne
    have hbot := inf_stabilizer_eq_bot_of_card_stabilizer_eq_two (Ne.symm hne) hcard
    exact ht1' (Subgroup.mem_bot.mp
      (hbot ▸ Subgroup.mem_inf.mpr ⟨htα, mem_stabilizer_iff.mpr hγ⟩))
  -- `t` は `K` に固定点なく作用するので `K` を反転する。
  have hfpf : ∀ k ∈ K, t * k * t⁻¹ = k → k = 1 := by
    intro k hk hconj
    have hcm : t * k = k * t := by
      conv_rhs => rw [← hconj]
      group
    have hfix : t • (k • α) = k • α := by
      rw [← mul_smul, hcm, mul_smul, htα']
    have hkα : k • α = α := htfix _ hfix
    exact Subgroup.mem_bot.mp
      (hKinf ▸ Subgroup.mem_inf.mpr ⟨hk, mem_stabilizer_iff.mpr hkα⟩)
  have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk => hKnormal.conj_mem k hk t
  have hinvK : ∀ k ∈ K, t * k * t⁻¹ = k⁻¹ := fun k hk =>
    OddOrder.GroupTheory.conj_eq_inv_of_orderTwo_of_fixedPointFree htt htK hfpf hk
  -- `K ⊔ G_α = ⊤` (`G_α` の極大性)。
  have hcoatom : IsCoatom (stabilizer G α) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  have hsup : K ⊔ stabilizer G α = ⊤ := by
    refine hcoatom.2 _ (lt_of_le_of_ne le_sup_right fun hc => ?_)
    have hKle : K ≤ stabilizer G α := hc ▸ le_sup_left
    have hKbot : K = ⊥ := le_bot_iff.mp (hKinf ▸ le_inf le_rfl hKle)
    rw [hKbot] at hKΩ
    simp only [Subgroup.card_bot] at hKΩ
    omega
  exact ⟨K, t, hKnormal, hKΩ, hKinf, hsup, hzt, htord, hinvK⟩

/-- **Isaacs Problem 8B.6** (p. 249) の次数部分 🎉: `|G_α| = 2` の原始置換群の次数
`|Ω|` は**素数** (`odd_card_of_card_stabilizer_eq_two` と合わせて奇素数)。

構造データ (`exists_inverting_involution_of_card_stabilizer_eq_two`) の `K` は反転する対合
`t` をもつので可換で, `K` の任意の部分群 `L` は `K` からも `t` からも正規化される。
`K ⊔ G_α = G` なので `L ⊴ G`, すると `L`-軌道は block になり原始性から `L = 1` または
`L = K`。よって `K` は真の非自明部分群をもたず `|K| = |Ω|` は素数。 -/
theorem prime_card_of_card_stabilizer_eq_two [Finite G] [Finite Ω] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) : (Nat.card Ω).Prime := by
  classical
  obtain ⟨K, t, hKnormal, hKΩ, hKinf, hsup, hzt, -, hinvK⟩ :=
    exists_inverting_involution_of_card_stabilizer_eq_two hcard
  haveI := hKnormal
  have hΩ2 : 2 ≤ Nat.card Ω := by
    have h0 : Nat.card Ω ≠ 0 := Nat.card_pos.ne'
    have h1 : Nat.card Ω ≠ 1 := fun hc =>
      absurd (Nat.card_eq_one_iff_unique.mp hc).1 (not_subsingleton Ω)
    omega
  -- 反転する対合をもつので `K` は可換。
  have hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have h1 : t * (x * y) * t⁻¹ = (x * y)⁻¹ := hinvK _ (K.mul_mem hx hy)
    have h2 : t * (x * y) * t⁻¹ = x⁻¹ * y⁻¹ := by
      rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) from by group,
        hinvK x hx, hinvK y hy]
    rw [h1, mul_inv_rev] at h2
    have h3 : (y⁻¹ * x⁻¹)⁻¹ = (x⁻¹ * y⁻¹)⁻¹ := congrArg (fun z : G => z⁻¹) h2
    simp only [mul_inv_rev, inv_inv] at h3
    exact h3
  -- `K` の部分群は `⊥` か `K` のみ。
  have hsubgroup : ∀ L : Subgroup G, L ≤ K → L = ⊥ ∨ L = K := by
    intro L hLK
    haveI : L.Normal := by
      have hKnorm : K ≤ Subgroup.normalizer (L : Set G) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          rwa [show x * h * x⁻¹ = h from by rw [hcomm x hx h (hLK hh)]; group]
        · intro hh
          have hhK : h ∈ K := by
            rw [show h = x⁻¹ * (x * h * x⁻¹) * x from by group]
            exact K.mul_mem (K.mul_mem (K.inv_mem hx) (hLK hh)) hx
          rwa [show x * h * x⁻¹ = h from by rw [hcomm x hx h hhK]; group] at hh
      have htnorm : t ∈ Subgroup.normalizer (L : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          rw [hinvK h (hLK hh)]
          exact L.inv_mem hh
        · intro hh
          have hhK : h ∈ K := by
            have hx : t * h * t⁻¹ ∈ K := hLK hh
            have hc := hKnormal.conj_mem _ hx t⁻¹
            rwa [show t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h from by group] at hc
          rw [hinvK h hhK] at hh
          exact (L.inv_mem_iff).mp hh
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
      exact sup_le hKnorm (by rw [hzt]; exact Subgroup.zpowers_le.mpr htnorm)
    rcases IsPreprimitive.isTrivialBlock_of_isBlock (IsBlock.orbit_of_normal (N := L) α) with
      hsubs | huniv
    · left
      refine le_bot_iff.mp (hKinf ▸ le_inf hLK fun x hx => mem_stabilizer_iff.mpr ?_)
      exact hsubs (mem_orbit α (⟨x, hx⟩ : ↥L)) (mem_orbit_self α)
    · right
      have hLinf : L ⊓ stabilizer G α = ⊥ :=
        le_bot_iff.mp (hKinf ▸ inf_le_inf_right _ hLK)
      have hLinj : Function.Injective (smulBase L α) :=
        (injective_smulBase_iff_disjoint_stabilizer L α).mpr hLinf
      have hLsurj : Function.Surjective (smulBase L α) := by
        intro γ
        have : γ ∈ orbit ↥L α := huniv ▸ Set.mem_univ γ
        obtain ⟨l, hl⟩ := this
        exact ⟨l, hl⟩
      have hLcard : Nat.card ↥L = Nat.card Ω :=
        Nat.card_eq_of_bijective _ ⟨hLinj, hLsurj⟩
      refine SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hLK ?_ (Set.toFinite _))
      have h1 : ((K : Set G)).ncard = Nat.card Ω := by
        rw [← Nat.card_coe_set_eq]; exact hKΩ
      have h2 : ((L : Set G)).ncard = Nat.card Ω := by
        rw [← Nat.card_coe_set_eq]; exact hLcard
      omega
  -- 素因数を取り Cauchy。
  have hKne1 : Nat.card ↥K ≠ 1 := by rw [hKΩ]; omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hKne1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite ↥K
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥K) p
    (by rwa [← Nat.card_eq_fintype_card])
  have hyord : orderOf (y : G) = p := by rw [← hy, Subgroup.orderOf_coe]
  have hy1 : (y : G) ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hyord
    exact hp.ne_one hyord.symm
  have hzple : Subgroup.zpowers (y : G) ≤ K := (Subgroup.zpowers_le).mpr y.2
  rcases hsubgroup _ hzple with h | h
  · exact absurd (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (y : G))) hy1
  · rw [← hKΩ, ← h, Nat.card_zpowers, hyord]
    exact hp

/-! ### Problem 8B.7 — 点安定化群が長さ 3 の軌道をもつ場合 -/

/-- 部分群 `D` の**奇位数元が生成する部分群**。有限群では Isaacs の `O²(D)`
(2-剰余部分群 = `D / N` が 2-群となる最小の正規部分群 `N`) と一致する。 -/
def oddCore (D : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ D ∧ Odd (orderOf x)}

lemma oddCore_le (D : Subgroup G) : oddCore D ≤ D :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

lemma mem_oddCore {D : Subgroup G} {x : G} (hx : x ∈ D) (hodd : Odd (orderOf x)) :
    x ∈ oddCore D :=
  Subgroup.subset_closure ⟨hx, hodd⟩

/-- `D` の奇位数元がすべて自明なら `D` は 2-群。

`g` の位数を `2^a · m` (`m` 奇) と分解すると `g^(2^a)` は奇位数なので
`oddCore D = ⊥` から `1`, したがって `g` の位数は `2` 冪。 -/
lemma isPGroup_two_of_oddCore_eq_bot [Finite G] {D : Subgroup G} (h : oddCore D = ⊥) :
    IsPGroup 2 ↥D := by
  intro g
  have hgne : orderOf (g : G) ≠ 0 := (orderOf_pos (g : G)).ne'
  refine ⟨(orderOf (g : G)).factorization 2, ?_⟩
  have hdvd : 2 ^ (orderOf (g : G)).factorization 2 ∣ orderOf (g : G) :=
    Nat.ordProj_dvd _ 2
  have hord : orderOf ((g : G) ^ (2 ^ (orderOf (g : G)).factorization 2))
      = orderOf (g : G) / 2 ^ (orderOf (g : G)).factorization 2 := by
    rw [orderOf_pow, Nat.gcd_eq_right hdvd]
  have hodd : Odd (orderOf ((g : G) ^ (2 ^ (orderOf (g : G)).factorization 2))) := by
    rw [hord]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hgne))
  have hmem : ((g : G) ^ (2 ^ (orderOf (g : G)).factorization 2)) ∈ oddCore D :=
    mem_oddCore (D.pow_mem g.2 _) hodd
  rw [h, Subgroup.mem_bot] at hmem
  exact Subtype.ext (by push_cast; exact hmem)

/-- 奇位数の元が `γ` を `x²` で固定するなら `x` 自身でも固定する
(`x` は `⟨x²⟩` に属するから)。 -/
lemma smul_eq_self_of_odd_of_sq_smul_eq {x : G} (hodd : Odd (orderOf x)) {γ : Ω}
    (h2 : (x * x) • γ = γ) : x • γ = γ := by
  obtain ⟨m, hm⟩ := hodd
  have hpow : ∀ k : ℕ, ((x * x) ^ k) • γ = γ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, h2, ih]
  have hx : (x * x) ^ (m + 1) = x := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  calc x • γ = ((x * x) ^ (m + 1)) • γ := by rw [hx]
    _ = γ := hpow _

/-- **8B.7 の鍵**: 奇位数の元 `x` が高々 2 点の集合 `S` を保つなら `S` を各点固定する。

`x • γ ≠ γ` なら `S = {γ, x • γ}` (2 点) で `x² • γ ∈ S` は `γ` でしかありえず,
奇位数から `x • γ = γ` (`smul_eq_self_of_odd_of_sq_smul_eq`) となって矛盾。 -/
lemma smul_eq_self_of_odd_of_ncard_le_two [Finite Ω] {x : G} (hodd : Odd (orderOf x))
    {S : Set Ω}
    (hS : ∀ δ ∈ S, x • δ ∈ S) (hcard : S.ncard ≤ 2) {γ : Ω} (hγ : γ ∈ S) :
    x • γ = γ := by
  classical
  by_contra hne
  have hxγ : x • γ ∈ S := hS γ hγ
  have hsq : (x * x) • γ ∈ S := by rw [mul_smul]; exact hS _ hxγ
  -- `{γ, x • γ} ⊆ S` は 2 点なので `S = {γ, x • γ}`。
  have hsub : ({γ, x • γ} : Set Ω) ⊆ S := by
    intro z hz
    rcases hz with rfl | hz
    · exact hγ
    · rw [Set.mem_singleton_iff] at hz; exact hz ▸ hxγ
  have hpair : ({γ, x • γ} : Set Ω).ncard = 2 := by
    rw [Set.ncard_pair (Ne.symm hne)]
  have hSeq : S = {γ, x • γ} :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hpair]; exact hcard) (Set.toFinite _)).symm
  -- `x² • γ` は `γ` か `x • γ`; 後者なら `x • γ = γ`。
  rw [hSeq] at hsq
  rcases hsq with h | h
  · exact hne (smul_eq_self_of_odd_of_sq_smul_eq hodd h)
  · rw [Set.mem_singleton_iff, mul_smul] at h
    exact hne (MulAction.injective x h)

/-- **8B.7 の鍵**: `G_α` の長さ 3 の軌道 `Δ ∋ β` について, `D = G_α ⊓ G_β` の奇位数元は
`Δ` を各点固定する。ゆえに `G_α` は `oddCore D` を正規化する
(`g x g⁻¹` は `g • Δ = Δ` を各点固定するので特に `β` を固定し, `D` に入る)。

Isaacs の Hint は `K = core_H(D)` を経由するが, 「奇位数元は 2 点集合を各点固定する」
を直接使えば core を作らずに済む。 -/
lemma stabilizer_le_normalizer_oddCore [Finite Ω] {α β : Ω}
    (h3 : Set.ncard (MulAction.orbit ↥(stabilizer G α) β) = 3) :
    stabilizer G α ≤ Subgroup.normalizer
      ((oddCore (stabilizer G α ⊓ stabilizer G β) : Subgroup G) : Set G) := by
  classical
  -- 奇位数元は軌道を各点固定する。
  have hfix : ∀ x ∈ stabilizer G α ⊓ stabilizer G β, Odd (orderOf x) →
      ∀ γ ∈ MulAction.orbit ↥(stabilizer G α) β, x • γ = γ := by
    intro x hx hodd γ hγ
    obtain ⟨hxα, hxβ'⟩ := Subgroup.mem_inf.mp hx
    have hxβ : x • β = β := mem_stabilizer_iff.mp hxβ'
    have hpres : ∀ δ ∈ MulAction.orbit ↥(stabilizer G α) β,
        x • δ ∈ MulAction.orbit ↥(stabilizer G α) β := by
      rintro δ ⟨k, rfl⟩
      exact ⟨⟨x, hxα⟩ * k, mul_smul _ _ _⟩
    rcases eq_or_ne γ β with rfl | hγβ
    · exact hxβ
    · have hβΔ : β ∈ MulAction.orbit ↥(stabilizer G α) β := MulAction.mem_orbit_self β
      have hScard : (MulAction.orbit ↥(stabilizer G α) β \ {β}).ncard = 2 := by
        rw [Set.ncard_sdiff_singleton_of_mem hβΔ, h3]
      have hSpres : ∀ δ ∈ MulAction.orbit ↥(stabilizer G α) β \ {β},
          x • δ ∈ MulAction.orbit ↥(stabilizer G α) β \ {β} := by
        intro δ hδ
        refine ⟨hpres δ hδ.1, ?_⟩
        intro hc
        rw [Set.mem_singleton_iff] at hc
        exact hδ.2 (Set.mem_singleton_iff.mpr (MulAction.injective x (hc.trans hxβ.symm)))
      exact smul_eq_self_of_odd_of_ncard_le_two hodd hSpres (le_of_eq hScard)
        ⟨hγ, fun hc => hγβ (Set.mem_singleton_iff.mp hc)⟩
  -- 生成元の共役はふたたび生成元。
  have hgen : ∀ g ∈ stabilizer G α, ∀ x : G,
      (x ∈ stabilizer G α ⊓ stabilizer G β ∧ Odd (orderOf x)) →
      (g * x * g⁻¹ ∈ stabilizer G α ⊓ stabilizer G β ∧ Odd (orderOf (g * x * g⁻¹))) := by
    intro g hg x hx
    refine ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (stabilizer G α).mul_mem
        ((stabilizer G α).mul_mem hg (Subgroup.mem_inf.mp hx.1).1) ((stabilizer G α).inv_mem hg)
    · refine mem_stabilizer_iff.mpr ?_
      have hginv : (g⁻¹ : G) • β ∈ MulAction.orbit ↥(stabilizer G α) β :=
        ⟨⟨g⁻¹, (stabilizer G α).inv_mem hg⟩, rfl⟩
      rw [mul_smul, mul_smul, hfix x hx.1 hx.2 _ hginv, ← mul_smul, mul_inv_cancel, one_smul]
    · have hsc : SemiconjBy g x (g * x * g⁻¹) := by
        unfold SemiconjBy
        group
      rw [← SemiconjBy.orderOf_eq g hsc]
      exact hx.2
  have hmapping : ∀ g ∈ stabilizer G α, ∀ y ∈ oddCore (stabilizer G α ⊓ stabilizer G β),
      g * y * g⁻¹ ∈ oddCore (stabilizer G α ⊓ stabilizer G β) := by
    intro g hg y hy
    have hmap : (oddCore (stabilizer G α ⊓ stabilizer G β)).map (MulAut.conj g).toMonoidHom
        ≤ oddCore (stabilizer G α ⊓ stabilizer G β) := by
      rw [oddCore, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.subset_closure (hgen g hg x hx)
    exact hmap ⟨y, hy, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hmapping g hg h hh, fun hh => ?_⟩
  have hc := hmapping g⁻¹ ((stabilizer G α).inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h from by group] at hc

/-- `D ≤ K` のとき `[K : D] · |D| = |K|`。 -/
lemma index_subgroupOf_mul_card [Finite G] {D K : Subgroup G} (h : D ≤ K) :
    (D.subgroupOf K).index * Nat.card ↥D = Nat.card ↥K := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.index_mul_card _

/-- 推移作用では対をなす suborbit の相対指数は等しい (`|G_α| = |G_β|` から)。 -/
lemma relIndex_stabilizer_comm [Finite G] [IsPretransitive G Ω] (α β : Ω) :
    (stabilizer G β).relIndex (stabilizer G α) = (stabilizer G α).relIndex (stabilizer G β) := by
  have hcomm : stabilizer G β ⊓ stabilizer G α = stabilizer G α ⊓ stabilizer G β := inf_comm _ _
  have e1 : (stabilizer G β).relIndex (stabilizer G α) *
      Nat.card ↥(stabilizer G α ⊓ stabilizer G β) = Nat.card ↥(stabilizer G α) := by
    rw [Subgroup.relIndex, ← Subgroup.inf_subgroupOf_right, hcomm]
    exact index_subgroupOf_mul_card inf_le_left
  have e2 : (stabilizer G α).relIndex (stabilizer G β) *
      Nat.card ↥(stabilizer G α ⊓ stabilizer G β) = Nat.card ↥(stabilizer G β) := by
    rw [Subgroup.relIndex, ← Subgroup.inf_subgroupOf_right]
    exact index_subgroupOf_mul_card inf_le_right
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (by rw [e1, e2]; exact card_stabilizer_eq α β)

/-- **Isaacs Problem 8B.7** (p. 249) 🎉: 原始置換群 `G` の点安定化群 `G_α` が
`Ω ∖ {α}` 上に**長さ 3 の軌道**をもてば `|G_α| = 3 · 2^e` (`e ≥ 0`)。

`D = G_α ⊓ G_β` (`β` はその軌道の点) は `G_α` の中で指数 3。`D` の奇位数元は軌道
`Δ` を各点固定するので `G_α` は `oddCore D` (= `O²(D)`) を正規化し
(`stabilizer_le_normalizer_oddCore`), 対をなす suborbit も長さ 3 なので `G_β` も同様。
`G_α ⊔ G_β = G` (極大性) だから `oddCore D ⊴ G`, しかも `oddCore D ≤ G_α` なので
`oddCore D = 1`。したがって `D` は 2-群で `|G_α| = 3 · |D| = 3 · 2^e`。 -/
theorem card_stabilizer_eq_three_mul_two_pow_of_suborbit_ncard_eq_three [Finite G] [Finite Ω]
    [FaithfulSMul G Ω] [IsPreprimitive G Ω] [Nontrivial Ω] {α β : Ω}
    (h3 : Set.ncard (MulAction.orbit ↥(stabilizer G α) β) = 3) :
    ∃ e : ℕ, Nat.card ↥(stabilizer G α) = 3 * 2 ^ e := by
  classical
  have hcomm : stabilizer G β ⊓ stabilizer G α = stabilizer G α ⊓ stabilizer G β := inf_comm _ _
  have hrel : (stabilizer G β).relIndex (stabilizer G α) = 3 := by
    rw [← ncard_suborbit_eq_relIndex]; exact h3
  have hDcard : 3 * Nat.card ↥(stabilizer G α ⊓ stabilizer G β)
      = Nat.card ↥(stabilizer G α) := by
    rw [← hrel, Subgroup.relIndex, ← Subgroup.inf_subgroupOf_right, hcomm]
    exact index_subgroupOf_mul_card inf_le_left
  -- 対をなす suborbit も長さ 3。
  have h3' : Set.ncard (MulAction.orbit ↥(stabilizer G β) α) = 3 := by
    rw [ncard_suborbit_eq_relIndex, ← relIndex_stabilizer_comm, hrel]
  -- 両方の点安定化群が `oddCore D` を正規化する。
  have hNα := stabilizer_le_normalizer_oddCore (G := G) h3
  have hNβ := stabilizer_le_normalizer_oddCore (G := G) h3'
  rw [hcomm] at hNβ
  -- `G_β ≰ G_α` (指数 3 の勘定)。
  have hnotle : ¬ stabilizer G β ≤ stabilizer G α := by
    intro hle
    have hDeq : stabilizer G α ⊓ stabilizer G β = stabilizer G β := inf_eq_right.mpr hle
    rw [hDeq, card_stabilizer_eq (G := G) β α] at hDcard
    have hpos : 0 < Nat.card ↥(stabilizer G α) := Nat.card_pos
    omega
  -- `oddCore D ⊴ G` ⟹ `= ⊥`。
  haveI : (oddCore (stabilizer G α ⊓ stabilizer G β)).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    have hcoatom : IsCoatom (stabilizer G α) :=
      IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
    have hsup : stabilizer G α ⊔ stabilizer G β = ⊤ :=
      hcoatom.2 _ (lt_of_le_of_ne le_sup_left fun hc => hnotle (hc ▸ le_sup_right))
    exact eq_top_iff.mpr (hsup ▸ sup_le hNα hNβ)
  have hbot : oddCore (stabilizer G α ⊓ stabilizer G β) = ⊥ :=
    eq_bot_of_normal_le_stabilizer ((oddCore_le _).trans inf_le_left)
  -- `D` は 2-群。
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := (isPGroup_two_of_oddCore_eq_bot hbot).exists_card_eq
  exact ⟨e, by rw [← hDcard, he]⟩

end

end OddOrder.Isaacs.Ch08
