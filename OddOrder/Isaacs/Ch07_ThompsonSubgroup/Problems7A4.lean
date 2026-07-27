/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.RootGroupSylow

/-!
# Isaacs Problem 7A.4 — `SL(2,q)` と `PSL(2,q)` の Sylow `p`-部分群はちょうど `q+1` 個

**主張** (書籍 p. 209): `q` が素数 `p` の冪のとき, `SL(2,q)` と `PSL(2,q)` はいずれも
ちょうど `q + 1` 個の Sylow `p`-部分群をもつ。

証明は `n_p = [G : N_G(P)]` (`Sylow.card_eq_index_normalizer`) を

* `P = U` = 上三角冪単部分群 `{[[1,b],[0,1]]}` (位数 `q`),
* `N_{SL}(U) = B` = 上三角部分群 `{[[a,b],[0,a⁻¹]]}` (位数 `q(q-1)`),
* `|SL(2,q)| = q(q-1)(q+1)` (`natCard_specialLinearGroup_fin_two`)

に適用して得る。

本ファイルはまず `U`, `B` を定義して位数を計算する。
-/

namespace OddOrder.Isaacs.Ch07

open Matrix

open OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear

open scoped MatrixGroups

section /- 7A.4: `SL(2,q)` の上三角冪単部分群と Borel 部分群 (p. 209) -/

variable {F : Type*} [Field F]

/-! ### 上三角冪単部分群 `U` -/

/-- `b ↦ [[1,b],[0,1]]` を群準同型 `Multiplicative F →* SL(2,F)` として。 -/
noncomputable def transvectionHom : Multiplicative F →* SL(2, F) where
  toFun b := Matrix.SpecialLinearGroup.transvection
    (zero_ne_one : (0 : Fin 2) ≠ 1) b.toAdd
  map_one' := Subtype.ext (by
    simp [Matrix.SpecialLinearGroup.transvection_coe])
  map_mul' x y := Matrix.SpecialLinearGroup.transvection_add _ _ _

@[simp]
theorem transvectionHom_apply (b : Multiplicative F) :
    (transvectionHom b : SL(2, F)) =
      Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) b.toAdd := rfl

theorem transvectionHom_injective :
    Function.Injective (transvectionHom (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have h := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hb
  simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply] using h

/-- **`SL(2,q)` の上三角冪単部分群** `U = {[[1,b],[0,1]] : b ∈ F}`。 -/
noncomputable def unipotentSL : Subgroup (SL(2, F)) :=
  (transvectionHom (F := F)).range

theorem natCard_unipotentSL [Finite F] :
    Nat.card (unipotentSL (F := F)) = Nat.card F := by
  have hequiv : Multiplicative F ≃* unipotentSL (F := F) :=
    MulEquiv.ofBijective (transvectionHom (F := F)).rangeRestrict
      ⟨fun _ _ h => transvectionHom_injective (congrArg Subtype.val h),
        (transvectionHom (F := F)).rangeRestrict_surjective⟩
  rw [← Nat.card_congr hequiv.toEquiv]
  exact Nat.card_congr (Equiv.refl _)

/-! ### Borel 部分群 `B` -/

/-- **`SL(2,q)` の Borel 部分群** `B = {[[a,b],[0,a⁻¹]]}` (左下成分が `0`)。 -/
def borelSL : Subgroup (SL(2, F)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    change ((a * b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Set.mem_setOf_eq] at ha hb
    rw [ha, hb, zero_mul, mul_zero, add_zero]
  one_mem' := by
    change ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [ha]

@[simp]
theorem mem_borelSL {g : SL(2, F)} :
    g ∈ (borelSL : Subgroup (SL(2, F))) ↔ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

/-- `B` の元は `g 0 0 * g 1 1 = 1` を満たす (行列式が `1` で左下が `0`)。 -/
theorem borelSL_diag_mul {g : SL(2, F)} (hg : g ∈ (borelSL : Subgroup (SL(2, F)))) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two, mem_borelSL.mp hg, mul_zero, sub_zero] at hdet
  exact hdet

theorem borelSL_diag_ne_zero {g : SL(2, F)} (hg : g ∈ (borelSL : Subgroup (SL(2, F)))) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
  left_ne_zero_of_mul_eq_one (borelSL_diag_mul hg)

/-- `[[a,b],[0,a⁻¹]]` (`a ≠ 0`) を `B` の元として。 -/
def borelElt (a : Fˣ) (b : F) : SL(2, F) :=
  ⟨!![(a : F), b; 0, (a : F)⁻¹], by
    rw [Matrix.det_fin_two_of, mul_inv_cancel₀ a.ne_zero, mul_zero, sub_zero]⟩

@[simp]
theorem borelElt_coe (a : Fˣ) (b : F) :
    ((borelElt a b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), b; 0, (a : F)⁻¹] := rfl

theorem borelElt_mem (a : Fˣ) (b : F) :
    borelElt a b ∈ (borelSL : Subgroup (SL(2, F))) := by
  simp [mem_borelSL]

/-- **`B ≃ Fˣ × F`** — `[[a,b],[0,a⁻¹]] ↔ (a, b)`。 -/
def borelEquiv : (Fˣ × F) ≃ (borelSL : Subgroup (SL(2, F))) where
  toFun p := ⟨borelElt p.1 p.2, borelElt_mem p.1 p.2⟩
  invFun g :=
    (Units.mk0 (((g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0)
        (borelSL_diag_ne_zero g.2),
      ((g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1)
  left_inv p := by
    ext
    · simp
    · simp
  right_inv g := by
    have hg := mem_borelSL.mp g.2
    have h11 : ((g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        (((g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
      (inv_eq_of_mul_eq_one_right (borelSL_diag_mul g.2)).symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hg, h11]

theorem natCard_borelSL [Finite F] :
    Nat.card (borelSL : Subgroup (SL(2, F))) = (Nat.card F - 1) * Nat.card F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [← Nat.card_congr borelEquiv, Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_units, Fintype.card_eq_nat_card]

/-! ### `N_{SL}(U) = B` -/

theorem unipotentSL_lower_left {u : SL(2, F)}
    (hu : u ∈ (unipotentSL : Subgroup (SL(2, F)))) :
    (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨b, rfl⟩ := hu
  simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem unipotentSL_le_borelSL :
    (unipotentSL : Subgroup (SL(2, F))) ≤ borelSL :=
  fun _ hu => unipotentSL_lower_left hu

theorem exists_borelElt {g : SL(2, F)} (hg : g ∈ (borelSL : Subgroup (SL(2, F)))) :
    ∃ (a : Fˣ) (b : F), g = borelElt a b := by
  obtain ⟨⟨a, b⟩, hab⟩ := borelEquiv.surjective ⟨g, hg⟩
  exact ⟨a, b, (congrArg Subtype.val hab).symm⟩

/-- `borelElt` の積 (Borel は `Fˣ ⋉ F` の形)。 -/
theorem borelElt_mul (a₁ a₂ : Fˣ) (b₁ b₂ : F) :
    borelElt a₁ b₁ * borelElt a₂ b₂ =
      borelElt (a₁ * a₂) ((a₁ : F) * b₂ + b₁ * (a₂ : F)⁻¹) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [borelElt, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[simp]
theorem borelElt_one : borelElt (1 : Fˣ) (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [borelElt]

theorem borelElt_inv (a : Fˣ) (b : F) : (borelElt a b)⁻¹ = borelElt a⁻¹ (-b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  have hsnd : (a : F) * (-b) + b * ((a⁻¹ : Fˣ) : F)⁻¹ = 0 := by
    simp only [Units.val_inv_eq_inv_val, inv_inv]
    ring
  rw [borelElt_mul, mul_inv_cancel, hsnd, borelElt_one]

/-- `[[1,b],[0,1]] = borelElt 1 b`。 -/
theorem transvection_eq_borelElt (b : F) :
    Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) b =
      borelElt 1 b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [borelElt]

/-- `[[a,c],[0,a⁻¹]] · [[1,b],[0,1]] · [[a,c],[0,a⁻¹]]⁻¹ = [[1, a²b],[0,1]]`。 -/
theorem borelElt_conj_transvection (a : Fˣ) (c b : F) :
    borelElt a c * Matrix.SpecialLinearGroup.transvection
        (zero_ne_one : (0 : Fin 2) ≠ 1) b * (borelElt a c)⁻¹ =
      Matrix.SpecialLinearGroup.transvection
        (zero_ne_one : (0 : Fin 2) ≠ 1) ((a : F) ^ 2 * b) := by
  have hfst : a * 1 * a⁻¹ = (1 : Fˣ) := by group
  have hsnd : ((a * 1 : Fˣ) : F) * (-c) +
      ((a : F) * b + c * ((1 : Fˣ) : F)⁻¹) * ((a⁻¹ : Fˣ) : F)⁻¹ = (a : F) ^ 2 * b := by
    simp only [Units.val_one, mul_one, Units.val_inv_eq_inv_val, inv_inv]
    ring
  rw [transvection_eq_borelElt, transvection_eq_borelElt, borelElt_inv, borelElt_mul,
    borelElt_mul, hfst, hsnd]

theorem conj_mem_unipotentSL {g u : SL(2, F)}
    (hg : g ∈ (borelSL : Subgroup (SL(2, F))))
    (hu : u ∈ (unipotentSL : Subgroup (SL(2, F)))) :
    g * u * g⁻¹ ∈ (unipotentSL : Subgroup (SL(2, F))) := by
  obtain ⟨a, c, rfl⟩ := exists_borelElt hg
  obtain ⟨b, rfl⟩ := hu
  refine ⟨Multiplicative.ofAdd ((a : F) ^ 2 * b.toAdd), ?_⟩
  rw [transvectionHom_apply, transvectionHom_apply]
  exact (borelElt_conj_transvection a c b.toAdd).symm

theorem borelSL_le_normalizer :
    (borelSL : Subgroup (SL(2, F))) ≤
      Subgroup.normalizer ((unipotentSL : Subgroup (SL(2, F))) : Set (SL(2, F))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  refine fun u => ⟨fun hu => conj_mem_unipotentSL hg hu, fun hu => ?_⟩
  have h := conj_mem_unipotentSL (inv_mem hg) hu
  have heq : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
  rwa [heq] at h

theorem normalizer_le_borelSL :
    Subgroup.normalizer ((unipotentSL : Subgroup (SL(2, F))) : Set (SL(2, F))) ≤ borelSL := by
  intro g hg
  have hT : Matrix.SpecialLinearGroup.transvection
      (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : F) ∈ (unipotentSL : Subgroup (SL(2, F))) :=
    ⟨Multiplicative.ofAdd (1 : F), rfl⟩
  obtain ⟨t, ht⟩ := (Subgroup.mem_normalizer_iff.mp hg _).mp hT
  rw [transvectionHom_apply] at ht
  -- `T' * g = g * T` の `(1,1)` 成分を比べると `g 1 0 = 0`
  have hmul : borelElt (1 : Fˣ) t.toAdd * g = g * borelElt (1 : Fˣ) (1 : F) := by
    rw [← transvection_eq_borelElt, ← transvection_eq_borelElt, ht]
    group
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 1) hmul
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      borelElt] using h
  exact mem_borelSL.mpr h11

/-- **`N_{SL(2,q)}(U) = B`** — Sylow `p`-部分群 `U` の正規化群は Borel 部分群。 -/
theorem normalizer_unipotentSL_eq :
    Subgroup.normalizer ((unipotentSL : Subgroup (SL(2, F))) : Set (SL(2, F))) = borelSL :=
  le_antisymm normalizer_le_borelSL borelSL_le_normalizer

/-! ### Sylow `p`-部分群の個数 -/

theorem index_borelSL [Finite F] :
    (borelSL : Subgroup (SL(2, F))).index = Nat.card F + 1 := by
  have hcard := (borelSL : Subgroup (SL(2, F))).card_mul_index
  rw [natCard_borelSL, natCard_specialLinearGroup_fin_two] at hcard
  have hq : 1 < Nat.card F := Finite.one_lt_card (α := F)
  have hpos : 0 < (Nat.card F - 1) * Nat.card F :=
    Nat.mul_pos (Nat.sub_pos_of_lt hq) (Nat.card_pos (α := F))
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [hcard]
  ring

theorem index_unipotentSL [Finite F] :
    (unipotentSL : Subgroup (SL(2, F))).index = (Nat.card F - 1) * (Nat.card F + 1) := by
  have hcard := (unipotentSL : Subgroup (SL(2, F))).card_mul_index
  rw [natCard_unipotentSL, natCard_specialLinearGroup_fin_two] at hcard
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F)) ?_
  rw [hcard]
  ring

/-! ### Sylow `p`-部分群の個数 (`SL` 側) -/

section SylowCount

variable [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] in
theorem exists_card_eq_prime_pow : ∃ n : ℕ, 0 < n ∧ Nat.card F = p ^ n := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  exact ⟨(n : ℕ), n.2, by rw [Nat.card_eq_fintype_card, hn]⟩

omit [Fact p.Prime] in
theorem isPGroup_unipotentSL : IsPGroup p (unipotentSL : Subgroup (SL(2, F))) := by
  obtain ⟨n, -, hn⟩ := exists_card_eq_prime_pow (F := F) (p := p)
  exact IsPGroup.of_card (by rw [natCard_unipotentSL, hn])

theorem not_dvd_index_unipotentSL :
    ¬ p ∣ (unipotentSL : Subgroup (SL(2, F))).index := by
  obtain ⟨n, hn0, hn⟩ := exists_card_eq_prime_pow (F := F) (p := p)
  have hp := Fact.out (p := p.Prime)
  have hq : 1 < Nat.card F := Finite.one_lt_card (α := F)
  have hpq : p ∣ Nat.card F := hn ▸ dvd_pow_self p hn0.ne'
  rw [index_unipotentSL]
  intro hdvd
  have hone : p ∣ 1 := by
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have hsub := Nat.dvd_sub hpq h
      rwa [Nat.sub_sub_self (le_of_lt hq)] at hsub
    · have hsub := Nat.dvd_sub h hpq
      simpa using hsub
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

/-- **Isaacs 7A.4** (`SL` 側) — `SL(2,q)` の Sylow `p`-部分群はちょうど `q + 1` 個。 -/
theorem card_sylow_specialLinearGroup :
    Nat.card (Sylow p (SL(2, F))) = Nat.card F + 1 := by
  set P : Sylow p (SL(2, F)) := (isPGroup_unipotentSL (F := F) (p := p)).toSylow
    (not_dvd_index_unipotentSL (F := F) (p := p)) with hPdef
  have hcard := Sylow.card_eq_index_normalizer P
  have hnorm : Subgroup.normalizer ((P : Set (SL(2, F)))) = borelSL :=
    normalizer_unipotentSL_eq
  rw [hcard, hnorm, index_borelSL]

end SylowCount

end

end OddOrder.Isaacs.Ch07
