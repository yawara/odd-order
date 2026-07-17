/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Isaacs Ch. 9 — §9B: inner automorphisms と Lemma 9.11 (pp. 276-278)

Wielandt automorphism tower theorem (Thm 9.10) に向けた §9B の土台:

- `innAut G` = **inner automorphism group** `Inn(G) ≤ Aut(G)`
  (`MulAut.conj` の range; mathlib に named subgroup が無いので新設).
- **Lemma 9.11**:
  - (a) `conj_ker` / `innAutEquivQuotientCenter`: `g ↦ τ_g` は `G → Inn(G)` 全射準同型で
    核は `Z(G)`, よって `G/Z(G) ≅ Inn(G)`.
  - (b) `innAut.normal`: `Inn(G) ◁ Aut(G)` (計算核 `mulAut_conj_conj`: `α τ_g α⁻¹ = τ_{α g}`).
  - (c) `centralizer_innAut_eq_bot`: `Z(G) = 1` なら `C_{Aut(G)}(Inn(G)) = 1`.
  - (d) `center_mulAut_eq_bot`: `Z(G) = 1` なら `Z(Aut(G)) = 1`.
- tower 埋め込みの土台: `conj_injective` / `innAutEquivOfCenterEqBot`
  (`Z(G) = 1` なら `G ≅ Inn(G) ◁ Aut(G)`).

9.12 (centralizer chain) 以降の tower 本体は後続 leaf.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

section /- 9B: Inn(G) と Lemma 9.11 (pp. 276-278) -/

variable (G : Type*) [Group G]

/-- **Inner automorphism group** `Inn(G)` (Isaacs p. 276): 共役 `τ_g = MulAut.conj g`
全体のなす `Aut(G)` の部分群 (`MulAut.conj : G →* MulAut G` の range). -/
def innAut : Subgroup (MulAut G) :=
  (MulAut.conj (G := G)).range

variable {G}

/-- `τ_g ∈ Inn(G)`. -/
theorem conj_mem_innAut (g : G) : MulAut.conj g ∈ innAut G :=
  ⟨g, rfl⟩

/-- **Isaacs Lemma 9.11(a)** (核の同定): `g ↦ τ_g` の核は `Z(G)`. -/
theorem conj_ker : (MulAut.conj (G := G)).ker = center G := by
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx := congrArg (fun α : MulAut G => α x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = (g * x * g⁻¹) * g := by rw [hx]
      _ = g * x := inv_mul_cancel_right _ _
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x, mul_assoc, mul_inv_cancel, mul_one]

/-- **Isaacs Lemma 9.11(a)** (第一同型): `G/Z(G) ≅ Inn(G)`. -/
noncomputable def innAutEquivQuotientCenter : (G ⧸ center G) ≃* ↥(innAut G) :=
  (QuotientGroup.quotientMulEquivOfEq conj_ker.symm).trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj (G := G)))

/-- **共役 automorphism の `Aut(G)`-共役**: `α τ_g α⁻¹ = τ_{α g}` (Isaacs p. 277 の計算;
Lemma 9.11(b)(c) の核). -/
theorem mulAut_conj_conj (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_def,
    MulEquiv.apply_symm_apply]

/-- **Isaacs Lemma 9.11(b)**: `Inn(G) ◁ Aut(G)`. -/
instance innAut.normal : (innAut G).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    rw [mulAut_conj_conj]
    exact conj_mem_innAut _

/-- **Isaacs Lemma 9.11(c)**: `Z(G) = 1` なら `C_{Aut(G)}(Inn(G)) = 1`. -/
theorem centralizer_innAut_eq_bot (h : center G = ⊥) :
    Subgroup.centralizer (innAut G : Set (MulAut G)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  ext g
  rw [MulAut.one_apply]
  have hcomm := Subgroup.mem_centralizer_iff.mp hα _ (conj_mem_innAut g)
  have heq : MulAut.conj (α g) = MulAut.conj g := by
    rw [← mulAut_conj_conj α g, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hker : α g * g⁻¹ ∈ (MulAut.conj (G := G)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
  rw [conj_ker, h, Subgroup.mem_bot] at hker
  exact mul_inv_eq_one.mp hker

/-- **Isaacs Lemma 9.11(d)**: `Z(G) = 1` なら `Z(Aut(G)) = 1`. -/
theorem center_mulAut_eq_bot (h : center G = ⊥) : center (MulAut G) = ⊥ := by
  rw [eq_bot_iff, ← centralizer_innAut_eq_bot h]
  exact Subgroup.center_le_centralizer _

/-- `Z(G) = 1` なら `g ↦ τ_g` は単射 (Isaacs p. 276: `G` を `Inn(G)` と同一視する根拠). -/
theorem conj_injective (h : center G = ⊥) :
    Function.Injective (MulAut.conj (G := G)) := by
  rw [← MonoidHom.ker_eq_bot_iff, conj_ker]
  exact h

/-- `Z(G) = 1` のとき `G ≅ Inn(G)` (automorphism tower の自然な埋め込みの土台). -/
noncomputable def innAutEquivOfCenterEqBot (h : center G = ⊥) : G ≃* ↥(innAut G) :=
  MonoidHom.ofInjective (conj_injective h)

end

end OddOrder.Isaacs.Ch09
