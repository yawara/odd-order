/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.Minimal
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# The `π`-residual `O^π(G)` (Isaacs Problem 1B.8(a))

`O^π(G)` = 商が **π-群**となる最小の正規部分群。Ch09 の `pResidual` (= `O^p`, 単一素数版) の
`π` 一般化で、Isaacs Ch.1 演習 1B.8(a) が要求する対象。`{N | N ◁ G ∧ G/N が π-群}` の交わり
(`sInf`) として定義し、有限群で以下を示す:

- `oPiResidual π G` (= `O^π(G)`): `sInf {N | N ◁ G ∧ IsPiGroup π (G/N)}`。
- `oPiResidual_mem_piQuotientNormals`: `O^π(G)` 自身が集合の元 (最小元) — 正規性と `G/O^π`
  が π-群であることを同時に与える (π-商正規の集合が `⊓` で閉じ有限ゆえ最小元をもつ)。
- `isPiGroup_quotient_oPiResidual` (**核心**): `G/O^π(G)` は π-群。
- `oPiResidual_le_of_isPiGroup_quotient`: `N ◁ G` で `G/N` が π-群 ⟹ `O^π(G) ≤ N` (普遍性)。
- `oPiResidual_eq_closure_piPrimeElements` (1B.8(b)): `O^π(G)` は位数がどの π-素数でも割れない
  元 (π'-元) 全体で生成される部分群に一致する。

## 実装ノート

`pResidual` (Ch09) と同じ骨格。単一素数 `p` を素数集合 `π` に、`IsPGroup p` を型レベル
`IsPiGroup π` に置換。`IsPiGroup` の同型不変性・積・部分群への遺伝は本ファイル冒頭で補う。
将来 `pResidual` を `oPiResidual {p}` にリファクタする余地あり (現状は両立)。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup QuotientGroup

variable {G : Type*} [Group G] {π : Set ℕ}

/-! ### 型レベル `IsPiGroup` の補助補題 -/

/-- 型レベル π-群は群同型で不変。 -/
theorem IsPiGroup.of_mulEquiv {K : Type*} [Group K] (e : G ≃* K) (h : IsPiGroup π G) :
    IsPiGroup π K := fun q hq => h q (by rwa [Nat.card_congr e.toEquiv])

/-- π-群の直積は π-群 (`primeFactors(|G|·|K|) = primeFactors|G| ∪ primeFactors|K|`)。 -/
theorem IsPiGroup.prod {K : Type*} [Group K] [Finite G] [Finite K]
    (hG : IsPiGroup π G) (hK : IsPiGroup π K) : IsPiGroup π (G × K) := fun q hq => by
  rw [Nat.card_prod, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne', Finset.mem_union] at hq
  exact hq.elim (hG q) (hK q)

/-- π-群の部分群は π-群 (`|H| ∣ |G|`)。 -/
theorem IsPiGroup.to_subgroup [Finite G] (hG : IsPiGroup π G) (H : Subgroup G) :
    IsPiGroup π (H : Subgroup G) := fun q hq =>
  hG q (Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card H) Nat.card_pos.ne' hq)

/-! ### `O^π(G)` の定義と基本 API -/

/-- `G/N` が π-群となる正規部分群 `N` の集合。 -/
def piQuotientNormals (π : Set ℕ) (G : Type*) [Group G] : Set (Subgroup G) :=
  {N : Subgroup G | ∃ _ : N.Normal, IsPiGroup π (G ⧸ N)}

/-- **`π`-residual** `O^π(G)`: 商が π-群となる最小の正規部分群。 -/
def oPiResidual (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  sInf (piQuotientNormals π G)

theorem normal_of_mem_piQuotientNormals {N : Subgroup G} (hN : N ∈ piQuotientNormals π G) :
    N.Normal := hN.choose

theorem isPiGroup_quotient_of_mem_piQuotientNormals {N : Subgroup G} [N.Normal]
    (hN : N ∈ piQuotientNormals π G) : IsPiGroup π (G ⧸ N) := hN.choose_spec

theorem top_mem_piQuotientNormals : (⊤ : Subgroup G) ∈ piQuotientNormals π G := by
  refine ⟨inferInstance, fun q hq => ?_⟩
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩, Nat.primeFactors_one] at hq
  exact absurd hq (Finset.notMem_empty q)

/-- π-商正規の集合は `⊓` で閉じている: `G/N₁`, `G/N₂` が π-群なら `G/(N₁⊓N₂)` も π-群
(`G/(N₁⊓N₂) ↪ (G/N₁)×(G/N₂)`)。 -/
theorem inf_mem_piQuotientNormals [Finite G] {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ∈ piQuotientNormals π G) (h₂ : N₂ ∈ piQuotientNormals π G) :
    N₁ ⊓ N₂ ∈ piQuotientNormals π G := by
  haveI := normal_of_mem_piQuotientNormals h₁
  haveI := normal_of_mem_piQuotientNormals h₂
  have hpg₁ := isPiGroup_quotient_of_mem_piQuotientNormals h₁
  have hpg₂ := isPiGroup_quotient_of_mem_piQuotientNormals h₂
  refine ⟨inferInstance, ?_⟩
  set φ := (QuotientGroup.mk' N₁).prod (QuotientGroup.mk' N₂) with hφ
  have hker : φ.ker = N₁ ⊓ N₂ := by
    rw [hφ, MonoidHom.ker_prod, QuotientGroup.ker_mk', QuotientGroup.ker_mk']
  have e : (G ⧸ (N₁ ⊓ N₂)) ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
  exact ((hpg₁.prod hpg₂).to_subgroup φ.range).of_mulEquiv e.symm

/-- `O^π(G)` 自身が `piQuotientNormals` の (最小) 元: π-商正規の集合は `⊓` で閉じ有限ゆえ
最小元 `N₀` をもち, `sInf = N₀` となる。これから `O^π(G)` の正規性と `G/O^π` の π-群性が従う。 -/
theorem oPiResidual_mem_piQuotientNormals [Finite G] :
    oPiResidual π G ∈ piQuotientNormals π G := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ (SetLike.coe_injective (A := Subgroup G))
  haveI : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  obtain ⟨N₀, hN₀⟩ :=
    exists_minimal_of_wellFoundedLT (· ∈ piQuotientNormals π G) ⟨⊤, top_mem_piQuotientNormals⟩
  have hmin : ∀ M ∈ piQuotientNormals π G, N₀ ≤ M := fun M hM =>
    (hN₀.2 (inf_mem_piQuotientNormals hN₀.1 hM) inf_le_left).trans inf_le_right
  have hpr : oPiResidual π G = N₀ := le_antisymm (sInf_le hN₀.1) (le_sInf hmin)
  rw [hpr]; exact hN₀.1

instance oPiResidual.normal [Finite G] : (oPiResidual π G).Normal :=
  normal_of_mem_piQuotientNormals oPiResidual_mem_piQuotientNormals

/-- **核心**: `G/O^π(G)` は π-群。 -/
theorem isPiGroup_quotient_oPiResidual [Finite G] : IsPiGroup π (G ⧸ oPiResidual π G) :=
  isPiGroup_quotient_of_mem_piQuotientNormals oPiResidual_mem_piQuotientNormals

/-- **Isaacs Problem 1B.8(a)** (普遍性・易しい向き): `N ◁ G`, `G/N` が π-群 ⟹ `O^π(G) ≤ N`。 -/
theorem oPiResidual_le_of_isPiGroup_quotient {N : Subgroup G} [N.Normal]
    (hN : IsPiGroup π (G ⧸ N)) : oPiResidual π G ≤ N :=
  sInf_le ⟨inferInstance, hN⟩

/-- **Isaacs Problem 1B.8(a)** (一意性): `G/N` を π-群にする最小の正規部分群は `O^π(G)` に限る。 -/
theorem oPiResidual_eq_of_isPiGroup_quotient_of_minimal [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsPiGroup π (G ⧸ N))
    (hmin : ∀ (M : Subgroup G) [M.Normal], IsPiGroup π (G ⧸ M) → N ≤ M) :
    oPiResidual π G = N :=
  le_antisymm (oPiResidual_le_of_isPiGroup_quotient hN)
    (hmin (oPiResidual π G) isPiGroup_quotient_oPiResidual)

/-! ### 1B.8(b): `O^π(G)` は π'-元 (位数が π-数でない元) で生成される -/

/-- 共役は位数を保つ。 -/
private theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

/-- **Isaacs Problem 1B.8(b)**. `O^π(G)` は位数がどの π-素数でも割れない元 (= π'-元) 全体で
生成される部分群に一致する。

`W := ⟨π'-元⟩`。`W ≤ O^π`: π'-元 `g` の `G/O^π` (π-群) での像の位数は `|orderOf g|` (π'-数) を割り
かつ π-数ゆえ `1`、よって `g ∈ O^π`。`O^π ≤ W`: `W ◁ G` (π'-元集合は共役不変) で `G/W` は π-群
(素数 `q ∉ π` が `|G/W|` を割れば Cauchy で位数 `q` の `x̄`、持ち上げ `x` の `q`-部分冪 `x^m`
(`Nat.exists_eq_pow_mul_and_not_dvd`) は位数 `q^k` の π'-元 ∈ W ゆえ `x̄^m = 1`、だが `q ∤ m` で
`x̄^m` は位数 `q ≠ 1` — 矛盾)、普遍性 `oPiResidual_le_of_isPiGroup_quotient` で `O^π ≤ W`。 -/
theorem oPiResidual_eq_closure_piPrimeElements [Finite G] :
    oPiResidual π G = Subgroup.closure {g : G | ∀ q ∈ (orderOf g).primeFactors, q ∉ π} := by
  set S : Set G := {g : G | ∀ q ∈ (orderOf g).primeFactors, q ∉ π} with hS
  -- W = closure S は正規 (S は共役不変)
  haveI hWnorm : (Subgroup.closure S).Normal := by
    refine ⟨fun a ha g => ?_⟩
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ?_
      rw [hS, Set.mem_setOf_eq, orderOf_conj_eq]; exact hx
    | one => simp
    | mul x y _ _ hgx hgy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hgx hgy
    | inv x _ hgx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]; exact inv_mem hgx
  refine le_antisymm ?_ ?_
  · -- O^π ≤ W: G/W は π-群
    refine oPiResidual_le_of_isPiGroup_quotient (fun q hq => ?_)
    by_contra hqπ
    haveI : Fact q.Prime := ⟨(Nat.mem_primeFactors.mp hq).1⟩
    obtain ⟨xbar, hxbar⟩ := exists_prime_orderOf_dvd_card' q (Nat.mem_primeFactors.mp hq).2.1
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
    have hqn : q ∣ orderOf x :=
      hxbar ▸ orderOf_map_dvd (QuotientGroup.mk' (Subgroup.closure S)) x
    obtain ⟨k, m, hm, hn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' q (Fact.out : q.Prime).ne_one
    have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos ⟨q ^ k, by rw [hn]; ring⟩ (orderOf_pos x)
    have hk1 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hn
      exact hm (hn ▸ hqn)
    -- x^m は位数 q^k の π'-元
    have hox : orderOf (x ^ m) = q ^ k := by
      rw [orderOf_pow, hn, Nat.gcd_eq_right ⟨q ^ k, by ring⟩, Nat.mul_div_cancel _ hm_pos]
    have hxmW : x ^ m ∈ Subgroup.closure S := Subgroup.subset_closure (by
      rw [hS, Set.mem_setOf_eq]
      intro r hr
      rw [hox] at hr
      have hrp := Nat.prime_of_mem_primeFactors hr
      have : r = q := (Nat.prime_dvd_prime_iff_eq hrp (Fact.out : q.Prime)).mp
        (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
      rw [this]; exact hqπ)
    -- x̄^m = 1 (∈ W) だが位数 q ≠ 1
    have h1 : (QuotientGroup.mk' (Subgroup.closure S) x) ^ m = 1 := by
      rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hxmW
    exact hm (hxbar ▸ orderOf_dvd_of_pow_eq_one h1)
  · -- W ≤ O^π: 各 π'-元 g は O^π に属す
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, ← orderOf_eq_one_iff]
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have hqπ : q ∈ π := isPiGroup_quotient_oPiResidual q (Nat.mem_primeFactors.mpr
      ⟨hq, hqdvd.trans (orderOf_dvd_natCard _), Nat.card_pos.ne'⟩)
    exact hg q (Nat.mem_primeFactors.mpr ⟨hq,
      hqdvd.trans (orderOf_map_dvd (QuotientGroup.mk' (oPiResidual π G)) g),
      (orderOf_pos g).ne'⟩) hqπ

/-! ### `O^π` の関手性 -/

/-- **`O^π` は群準同型で押し出せる**: 任意の `f : A →* B` について `O^π(A)^f ≤ O^π(B)`。

1B.8(b) で `O^π = ⟨π'-元⟩` ゆえ生成元に帰着し、`orderOf (f a) ∣ orderOf a` (`orderOf_map_dvd`)
から π'-元の像は π'-元。`f` に全射性も単射性も要らない。 -/
theorem oPiResidual_map_le {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (π : Set ℕ) (f : A →* B) : (oPiResidual π A).map f ≤ oPiResidual π B := by
  rw [oPiResidual_eq_closure_piPrimeElements, oPiResidual_eq_closure_piPrimeElements,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  exact Subgroup.subset_closure fun q hq =>
    ha q (Nat.primeFactors_mono (orderOf_map_dvd f a) (orderOf_pos a).ne' hq)

/-- `H ≤ K` のとき `O^π(H)` は `↥K` の中で `O^π(K)` に入る (`oPiResidual_map_le` の
`Subgroup.inclusion` 版)。特に `H` が π-perfect (`O^π(H) = ⊤`) なら
`H.subgroupOf K ≤ O^π(K)`。 -/
theorem subgroupOf_le_oPiResidual_of_eq_top [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    (hH : oPiResidual π ↥H = ⊤) : H.subgroupOf K ≤ oPiResidual π ↥K := by
  have hmap := oPiResidual_map_le π (Subgroup.inclusion hHK)
  rwa [hH, ← MonoidHom.range_eq_map, Subgroup.inclusion_range] at hmap

end OddOrder.Isaacs.Ch03
