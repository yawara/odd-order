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

Isaacs 1B.8(b) (`O^π(G)` は位数が π-数でない元で生成される) は別途。

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

end OddOrder.Isaacs.Ch03
