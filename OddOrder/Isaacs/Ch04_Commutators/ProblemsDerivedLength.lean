/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# Isaacs Chapter 4 — Problem 4D.5 (半直積の導来長)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4D.5 (書籍 p. 146)。

`A` を導来長 `n` の可解群とし, `A` が可換群 `B` に忠実に自己同型で作用して
`(|B|, |A^{(n-1)}|) = 1` とすると, `G = B ⋊ A` の導来長は `n + 1`。

## 現状

* **上界** `derivedSeries_semidirectProduct_eq_bot` — `A^{(n)} = 1` かつ `B` 可換なら
  `(B ⋊ A)^{(n+1)} = 1`。`rightHom : B ⋊ A ↠ A` の核が `inl(B)` であることと,
  可換群 `B` の交換子が自明であることから。**coprime も faithful も不要**。
* **下界** (`(B ⋊ A)^{(n)} ≠ 1`) は coprime 作用の Lemma 4.29 (`⁅B, V, V⁆ = ⁅B, V⁆`,
  `V := A^{(n-1)}`) を使う: `⁅inl B, inr V⁆ ≤ (B ⋊ A)^{(k)}` を `k` について押し上げ,
  faithful から `⁅B, V⁆ ≠ 1`。後続 iteration で実装 (issue 1055 参照)。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4D.5 (p. 146) -/

variable {A B : Type*} [Group A] [CommGroup B] (φ : A →* MulAut B)

/-- 半直積の導来列は `inl(B)` の中に落ちる: `A^{(n)} = 1` なら `(B ⋊ A)^{(n)} ≤ inl(B)`。

`rightHom : B ⋊ A ↠ A` は `(B ⋊ A)^{(n)}` を `A^{(n)} = 1` へ写すので, 核
`= inl(B)` (`SemidirectProduct.range_inl_eq_ker_rightHom`) に含まれる。 -/
theorem derivedSeries_le_range_inl {n : ℕ} (hA : derivedSeries A n = ⊥) :
    derivedSeries (B ⋊[φ] A) n ≤ (SemidirectProduct.inl : B →* B ⋊[φ] A).range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  intro x hx
  rw [MonoidHom.mem_ker]
  have hmap : (derivedSeries (B ⋊[φ] A) n).map (SemidirectProduct.rightHom) ≤ derivedSeries A n :=
    map_derivedSeries_le_derivedSeries _ n
  rw [hA, le_bot_iff] at hmap
  have : SemidirectProduct.rightHom x ∈
      (derivedSeries (B ⋊[φ] A) n).map (SemidirectProduct.rightHom) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hmap, Subgroup.mem_bot] at this
  exact this

/-- **Isaacs Problem 4D.5** (上界): `B` が可換で `A` の導来長が `n` 以下なら,
`B ⋊ A` の導来長は `n + 1` 以下。

`(B ⋊ A)^{(n)} ≤ inl(B)` (`derivedSeries_le_range_inl`) と `inl(B)` の可換性から
`(B ⋊ A)^{(n+1)} = ⁅(B ⋊ A)^{(n)}, (B ⋊ A)^{(n)}⁆ ≤ ⁅inl(B), inl(B)⁆ = 1`。
coprime 性も忠実性も使わない。 -/
theorem derivedSeries_semidirectProduct_eq_bot {n : ℕ} (hA : derivedSeries A n = ⊥) :
    derivedSeries (B ⋊[φ] A) (n + 1) = ⊥ := by
  have hle := derivedSeries_le_range_inl φ hA
  have hab : ⁅(SemidirectProduct.inl : B →* B ⋊[φ] A).range,
      (SemidirectProduct.inl : B →* B ⋊[φ] A).range⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  rw [derivedSeries_succ, ← le_bot_iff, ← hab]
  exact Subgroup.commutator_mono hle hle

end

end OddOrder.Isaacs.Ch04
