/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import Mathlib.RepresentationTheory.Basic

/-!
# BG §3B: Lemma 3.3 (Wielandt's fixed-point lemma for Frobenius groups)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §3B, mmd `references/bg/local-analysis.mmd` L845-861.

**BG Lemma 3.3** (Wielandt): `G = KR` を Frobenius 群 (kernel `K`, complement `R`)、`V` を体
`F` (`char F ∤ |K|`) 上の `G`-表現とする。`K` が `V` に非自明に作用するなら `C_V(R) ≠ 0`。

これは BG Thm 3.7 (Frobenius kernel nilpotency) の coprime chief factor 場合の核 (mmd L1217)。
plan = `notes/bg/s03_thm37_plan.md`。

## 証明 (Wielandt, mmd L847-861)

表現を群環 `F[G]` の作用へ拡張 (`Representation.asAlgebraHom`)。有限部分群 `H` に対し
`σ_H = ∑_{h∈H} h ∈ F[G]` は任意の `v` を `H`-不動点へ送る (`groupSum_mem_fixedPoints`)。
`C_V(R)=0` を仮定すると `ρ(σ_{R^x}) = 0` (全 `x`) と `ρ(σ_G)=0`。Frobenius 分割
`σ_G = σ_K + ∑_{x∈K} σ_{R^x} − |K|·1` から `0 = ρ(σ_K)v − |K|v`、ゆえ `|K|v ∈ C_V(K)`。
`|K| ≠ 0 in F` より `V = C_V(K)`、すなわち `K` は自明に作用 (対偶)。
-/

namespace OddOrder.BG.Ch1.S03b

open OddOrder.Isaacs.Ch06
open scoped Pointwise

variable {F : Type*} [Field F] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The averaging endomorphism `∑_{h ∈ H} ρ h` of a finite subgroup `H` under a representation. -/
noncomputable def groupSumMap (ρ : Representation F G V) (H : Subgroup G) [Fintype H] :
    V →ₗ[F] V :=
  ∑ h : H, ρ (h : G)

/-- **Averaging into fixed points**: `(∑_{h∈H} ρ h) v` is fixed by every `h₀ ∈ H`, because
left multiplication by `h₀` permutes `H`. -/
theorem fixed_apply_groupSumMap (ρ : Representation F G V) (H : Subgroup G) [Fintype H]
    {h₀ : G} (hh₀ : h₀ ∈ H) (v : V) :
    ρ h₀ (groupSumMap ρ H v) = groupSumMap ρ H v := by
  simp only [groupSumMap, LinearMap.coeFn_sum, Finset.sum_apply, map_sum]
  -- `ρ h₀ (ρ ↑h v) = ρ (↑(⟨h₀,hh₀⟩ * h)) v`; reindex by `Equiv.mulLeft ⟨h₀,hh₀⟩`.
  have hreindex : ∀ h : H, ρ h₀ (ρ (h : G) v)
      = ρ ((⟨h₀, hh₀⟩ * h : H) : G) v := by
    intro h
    rw [Subgroup.coe_mul, map_mul]
    rfl
  rw [Finset.sum_congr rfl (fun h _ => hreindex h)]
  exact Equiv.sum_comp (Equiv.mulLeft (⟨h₀, hh₀⟩ : H)) (fun h => ρ ((h : H) : G) v)

/-- **BG Lemma 3.3** (Wielandt, mmd L845): if `G = KR` is a Frobenius group and `K` acts
nontrivially on a representation `V` over a field `F` of characteristic not dividing `|K|`,
then `C_V(R) ≠ 0` (some nonzero vector is fixed by all of `R`). -/
theorem centralizer_ne_bot_of_nontrivial_kernel [Finite G] {K R : Subgroup G}
    (hFrob : IsFrobeniusGroup G K R) (ρ : Representation F G V)
    (hchar : (Nat.card K : F) ≠ 0)
    (hKnt : ∃ k : K, ρ (k : G) ≠ 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ r : R, ρ (r : G) v = v := by
  sorry

end OddOrder.BG.Ch1.S03b
