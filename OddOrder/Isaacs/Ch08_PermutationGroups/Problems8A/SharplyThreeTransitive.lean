/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Isaacs Problems 8A (pp. 235–236) — `SL(2, q)` は射影直線に sharply 3-transitive

**Problem 8A.17**: `q` を 2 の冪とし, `SL(2, q)` を位数 `q` の体上の 2 次元ベクトル空間の
`q + 1` 個の 1 次元部分空間 (= 射影直線 `ℙ K V`) に作用させると, この作用は
**sharply 3-transitive** である。

数学的には char 2 が **2 箇所**で効く: 存在側では「`K` のすべての元が平方」
(有限体 char 2 では Frobenius が全単射) が `det` の正規化に要り, 一意性側では
「`a² = 1 ⟹ a = 1`」がスカラー行列を潰すのに要る。標数が奇なら後者が破れ,
実際 `SL(2,q)` (`q` 奇) は sharply 3-transitive でない (`-I` が全点を固定する)。

## Main results

- `exists_projective_frame` — `dim V = 2` の相異なる 3 点は `[u], [v], [u+v]` の形に
  正規化できる (**射影 frame**)。
- `exists_linearEquiv_frame`, `exists_specialLinearGroup_frame` — 2 つの frame の間の
  基底変換と, `K` のすべての元が平方のときのその `det = 1` への正規化。
- `exists_smul_eq_of_smul_mk_eq`, `eq_one_of_fixes_three` — `char K = 2` なら相異なる
  3 点を固定する `SL(V)` の元は単位元 (**sharp 性**)。
- `existsUnique_specialLinearGroup_of_three_distinct` — **Problem 8A.17** (抽象版):
  `dim V = 2`, `char K = 2`, `K` のすべての元が平方 ⟹ `SL(V)` は `ℙ K V` に
  sharply 3-transitive。
- `exists_sq_of_charTwo`, `card_projectivization_fin_two`,
  `existsUnique_matrixSpecialLinearGroup_of_three_distinct` — **Problem 8A.17**
  (教科書の形): `q` が 2 の冪なら `SL(2, q)` は `q + 1` 個の 1 次元部分空間に
  sharply 3-transitive。
-/

namespace OddOrder.Isaacs.Ch08

open Module Projectivization

open scoped LinearAlgebra.Projectivization

section SharplyThreeTransitive

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- 0 でないスカラー倍は射影点を変えない。 -/
lemma mk_smul_eq_mk {c : K} (hc : c ≠ 0) {v : V} (hv : v ≠ 0)
    (hcv : c • v ≠ 0) : mk K (c • v) hcv = mk K v hv :=
  (mk_eq_mk_iff K _ _ hcv hv).mpr ⟨Units.mk0 c hc, rfl⟩

/-- **射影 frame の正規化**: `dim V = 2` の相異なる 3 点 `P₁, P₂, P₃` に対し,
`P₁ = [u]`, `P₂ = [v]`, `P₃ = [u + v]` となる 1 次独立な `u, v` が取れる。

`P₃.rep = a • P₁.rep + b • P₂.rep` と展開すると `P₃ ≠ P₂` から `a ≠ 0`,
`P₃ ≠ P₁` から `b ≠ 0` なので, `u := a • P₁.rep`, `v := b • P₂.rep` とすればよい。 -/
theorem exists_projective_frame (hdim : finrank K V = 2)
    {P₁ P₂ P₃ : ℙ K V} (h12 : P₁ ≠ P₂) (h13 : P₁ ≠ P₃) (h23 : P₂ ≠ P₃) :
    ∃ (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0),
      LinearIndependent K ![u, v] ∧
        mk K u hu = P₁ ∧ mk K v hv = P₂ ∧ mk K (u + v) huv = P₃ := by
  classical
  haveI : FiniteDimensional K V := .of_finrank_eq_succ hdim
  have hli : LinearIndependent K ![P₁.rep, P₂.rep] := linearIndependent_pair_iff_ne.mpr h12
  have hcard : Fintype.card (Fin 2) = finrank K V := by simp [hdim]
  set B : Basis (Fin 2) K V := basisOfLinearIndependentOfCardEqFinrank hli hcard with hBdef
  have hB : ⇑B = ![P₁.rep, P₂.rep] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB0 : B 0 = P₁.rep := by rw [hB]; rfl
  have hB1 : B 1 = P₂.rep := by rw [hB]; rfl
  set a : K := B.repr P₃.rep 0 with hadef
  set b : K := B.repr P₃.rep 1 with hbdef
  have hsum : a • P₁.rep + b • P₂.rep = P₃.rep := by
    have h := B.sum_repr P₃.rep
    rw [Fin.sum_univ_two, hB0, hB1] at h
    exact h
  -- `a = 0` なら `P₃ = P₂`, `b = 0` なら `P₃ = P₁`。
  have ha : a ≠ 0 := by
    intro h0
    have hb : b ≠ 0 := by
      intro h1
      exact P₃.rep_nonzero (by rw [← hsum, h0, h1, zero_smul, zero_smul, add_zero])
    refine h23 ?_
    rw [← mk_rep P₂, ← mk_rep P₃]
    refine ((mk_eq_mk_iff K _ _ P₂.rep_nonzero P₃.rep_nonzero).mpr
      ⟨(Units.mk0 b hb)⁻¹, ?_⟩)
    rw [← hsum, h0, zero_smul, zero_add]
    simp [smul_smul, Units.smul_def, inv_mul_cancel₀ hb]
  have hb : b ≠ 0 := by
    intro h1
    refine h13 ?_
    rw [← mk_rep P₁, ← mk_rep P₃]
    refine ((mk_eq_mk_iff K _ _ P₁.rep_nonzero P₃.rep_nonzero).mpr
      ⟨(Units.mk0 a ha)⁻¹, ?_⟩)
    rw [← hsum, h1, zero_smul, add_zero]
    simp [smul_smul, Units.smul_def, inv_mul_cancel₀ ha]
  -- 正規化した frame。
  have hliuv : LinearIndependent K ![a • P₁.rep, b • P₂.rep] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t hst
    have h := hli (s * a) (t * b) (by rw [mul_smul, mul_smul]; exact hst)
    exact ⟨by simpa [ha] using h.1, by simpa [hb] using h.2⟩
  refine ⟨a • P₁.rep, b • P₂.rep, smul_ne_zero ha P₁.rep_nonzero,
    smul_ne_zero hb P₂.rep_nonzero, by rw [hsum]; exact P₃.rep_nonzero, hliuv, ?_, ?_, ?_⟩
  · rw [mk_smul_eq_mk ha P₁.rep_nonzero, mk_rep]
  · rw [mk_smul_eq_mk hb P₂.rep_nonzero, mk_rep]
  · simp only [hsum]
    exact mk_rep P₃

/-- 2 つの frame の間には基底変換 `T : V ≃ₗ[K] V` がある (`T u = u'`, `T v = v'`)。 -/
theorem exists_linearEquiv_frame (hdim : finrank K V = 2)
    {u v u' v' : V} (h : LinearIndependent K ![u, v]) (h' : LinearIndependent K ![u', v']) :
    ∃ T : V ≃ₗ[K] V, T u = u' ∧ T v = v' := by
  haveI : FiniteDimensional K V := .of_finrank_eq_succ hdim
  have hcard : Fintype.card (Fin 2) = finrank K V := by simp [hdim]
  have hB : ⇑(basisOfLinearIndependentOfCardEqFinrank h hcard) = ![u, v] :=
    coe_basisOfLinearIndependentOfCardEqFinrank h hcard
  have hB' : ⇑(basisOfLinearIndependentOfCardEqFinrank h' hcard) = ![u', v'] :=
    coe_basisOfLinearIndependentOfCardEqFinrank h' hcard
  refine ⟨(basisOfLinearIndependentOfCardEqFinrank h hcard).equiv
    (basisOfLinearIndependentOfCardEqFinrank h' hcard) (Equiv.refl (Fin 2)), ?_, ?_⟩
  · have h0 : (basisOfLinearIndependentOfCardEqFinrank h hcard) 0 = u := by rw [hB]; rfl
    have hap := Basis.equiv_apply (basisOfLinearIndependentOfCardEqFinrank h hcard) 0
      (basisOfLinearIndependentOfCardEqFinrank h' hcard) (Equiv.refl (Fin 2))
    rw [h0] at hap
    rw [hap]
    simp [hB']
  · have h1 : (basisOfLinearIndependentOfCardEqFinrank h hcard) 1 = v := by rw [hB]; rfl
    have hap := Basis.equiv_apply (basisOfLinearIndependentOfCardEqFinrank h hcard) 1
      (basisOfLinearIndependentOfCardEqFinrank h' hcard) (Equiv.refl (Fin 2))
    rw [h1] at hap
    rw [hap]
    simp [hB']

/-- **frame から frame への `SL` の元**: `K` のすべての元が平方なら, 2 つの frame の間の
基底変換をスカラー倍して行列式を `1` に正規化できる。

`det (μ • T) = μ² · det T` (`LinearMap.det_smul`, `dim V = 2`) なので,
`μ² = (det T)⁻¹` を満たす `μ` を取ればよい。 -/
theorem exists_specialLinearGroup_frame (hdim : finrank K V = 2)
    (hsq : ∀ c : K, ∃ d : K, d * d = c)
    {u v u' v' : V} (h : LinearIndependent K ![u, v]) (h' : LinearIndependent K ![u', v']) :
    ∃ (A : SpecialLinearGroup K V) (μ : K), μ ≠ 0 ∧
      (A : V ≃ₗ[K] V) u = μ • u' ∧ (A : V ≃ₗ[K] V) v = μ • v' := by
  haveI : FiniteDimensional K V := .of_finrank_eq_succ hdim
  obtain ⟨T, hTu, hTv⟩ := exists_linearEquiv_frame hdim h h'
  obtain ⟨μ, hμ⟩ := hsq ((T.det : K)⁻¹)
  have hdet0 : (T.det : K) ≠ 0 := T.det.ne_zero
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hμ
    exact (inv_ne_zero hdet0) hμ.symm
  set A : V ≃ₗ[K] V :=
    (DistribMulAction.toLinearEquiv K V (Units.mk0 μ hμ0)).trans T with hA
  have hAsmul : ∀ x : V, A x = μ • T x := by
    intro x
    change T ((Units.mk0 μ hμ0) • x) = μ • T x
    rw [Units.smul_def, Units.val_mk0, map_smul]
  have hAmap : (A : V →ₗ[K] V) = μ • (T : V →ₗ[K] V) :=
    LinearMap.ext fun x => hAsmul x
  have hAdet : A.det = 1 := by
    refine Units.ext ?_
    rw [LinearEquiv.coe_det, hAmap, LinearMap.det_smul, hdim, Units.val_one,
      ← LinearEquiv.coe_det, pow_two, hμ, inv_mul_cancel₀ hdet0]
  exact ⟨⟨A, hAdet⟩, μ, hμ0, by rw [hAsmul, hTu], by rw [hAsmul, hTv]⟩

/-- 射影点を固定する元は代表元をスカラー倍する。 -/
lemma exists_smul_eq_of_smul_mk_eq {A : SpecialLinearGroup K V} {w : V} (hw : w ≠ 0)
    (hfix : A • mk K w hw = mk K w hw) :
    ∃ c : K, c ≠ 0 ∧ (A : V ≃ₗ[K] V) w = c • w := by
  rw [Projectivization.specialLinearGroup_smul_def, smul_mk, mk_eq_mk_iff] at hfix
  obtain ⟨c, hc⟩ := hfix
  exact ⟨(c : K), c.ne_zero, by simpa [Units.smul_def] using hc.symm⟩

/-- **sharp 性の核**: `char K = 2` かつ `dim V = 2` のとき, 射影直線の相異なる 3 点を
固定する `SL(V)` の元は単位元。

frame `[u], [v], [u+v]` を取ると `A u = a u`, `A v = b v`, `A (u+v) = c (u+v)` から
1 次独立性で `a = b = c` ⟹ `A = a · id` ⟹ `det A = a² = 1`。
**`char K = 2` なので `a² = 1` から `a = 1`** (標数が奇なら `a = -1` の可能性が残り,
実際 `SL(2,q)` は `q` が奇のとき sharply 3-transitive でない)。 -/
theorem eq_one_of_fixes_three [CharP K 2] (hdim : finrank K V = 2)
    {P₁ P₂ P₃ : ℙ K V} (h12 : P₁ ≠ P₂) (h13 : P₁ ≠ P₃) (h23 : P₂ ≠ P₃)
    {A : SpecialLinearGroup K V} (hA1 : A • P₁ = P₁) (hA2 : A • P₂ = P₂)
    (hA3 : A • P₃ = P₃) : A = 1 := by
  haveI : FiniteDimensional K V := .of_finrank_eq_succ hdim
  obtain ⟨u, v, hu, hv, huv, hli, hP1, hP2, hP3⟩ := exists_projective_frame hdim h12 h13 h23
  subst hP1; subst hP2; subst hP3
  obtain ⟨a, -, hau⟩ := exists_smul_eq_of_smul_mk_eq hu hA1
  obtain ⟨b, -, hbv⟩ := exists_smul_eq_of_smul_mk_eq hv hA2
  obtain ⟨c, -, hcuv⟩ := exists_smul_eq_of_smul_mk_eq huv hA3
  -- 1 次独立性から `a = c` かつ `b = c`。
  have hzero : (a - c) • u + (b - c) • v = 0 := by
    have hlin : (A : V ≃ₗ[K] V) (u + v) = a • u + b • v := by
      rw [map_add, hau, hbv]
    rw [hcuv, smul_add] at hlin
    rw [sub_smul, sub_smul,
      show a • u - c • u + (b • v - c • v) = (a • u + b • v) - (c • u + c • v) from by abel,
      ← hlin, sub_self]
  rw [LinearIndependent.pair_iff] at hli
  obtain ⟨hac, hbc⟩ := hli (a - c) (b - c) hzero
  have hab : a = c := sub_eq_zero.mp hac
  have hba : b = c := sub_eq_zero.mp hbc
  -- `A = c · id`, したがって `det A = c²`。
  have hcard : Fintype.card (Fin 2) = finrank K V := by simp [hdim]
  have hlipair : LinearIndependent K ![u, v] := LinearIndependent.pair_iff.mpr hli
  have hB : ⇑(basisOfLinearIndependentOfCardEqFinrank hlipair hcard) = ![u, v] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hlipair hcard
  have hAmap : ((A : V ≃ₗ[K] V) : V →ₗ[K] V) = c • (LinearMap.id : V →ₗ[K] V) := by
    refine Basis.ext (basisOfLinearIndependentOfCardEqFinrank hlipair hcard) fun i => ?_
    fin_cases i
    · have h0 : (basisOfLinearIndependentOfCardEqFinrank hlipair hcard) 0 = u := by
        rw [hB]; rfl
      simpa [h0, hab] using hau
    · have h1 : (basisOfLinearIndependentOfCardEqFinrank hlipair hcard) 1 = v := by
        rw [hB]; rfl
      simpa [h1, hba] using hbv
  have hdetc : c * c = 1 := by
    have h := A.prop
    rw [← Units.val_inj, LinearEquiv.coe_det, hAmap, LinearMap.det_smul, LinearMap.det_id,
      hdim, mul_one, Units.val_one] at h
    rw [← pow_two]
    exact h
  -- `char K = 2` ⟹ `c = 1`。
  have htwo : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hc1 : c = 1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by linear_combination hdetc
    rcases mul_eq_zero.mp hfac with h | h
    · linear_combination h
    · linear_combination h - htwo
  -- したがって `A` は恒等写像。
  refine Subtype.ext (LinearEquiv.toLinearMap_injective ?_)
  rw [hAmap, hc1, one_smul]
  rfl

/-- **Isaacs Problem 8A.17** (p. 236) 🎉: `dim V = 2` で `K` のすべての元が平方,
かつ `char K = 2` なら, `SL(V)` の射影直線 `ℙ K V` への作用は **sharply 3-transitive**。

有限体 `K = GF(q)` (`q` が 2 の冪) は Frobenius が全単射なので両条件を満たし,
`ℙ K V` は `q + 1` 点だから Isaacs の主張そのものになる。 -/
theorem existsUnique_specialLinearGroup_of_three_distinct [CharP K 2]
    (hdim : finrank K V = 2) (hsq : ∀ c : K, ∃ d : K, d * d = c)
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : ℙ K V}
    (hP12 : P₁ ≠ P₂) (hP13 : P₁ ≠ P₃) (hP23 : P₂ ≠ P₃)
    (hQ12 : Q₁ ≠ Q₂) (hQ13 : Q₁ ≠ Q₃) (hQ23 : Q₂ ≠ Q₃) :
    ∃! A : SpecialLinearGroup K V, A • P₁ = Q₁ ∧ A • P₂ = Q₂ ∧ A • P₃ = Q₃ := by
  haveI : FiniteDimensional K V := .of_finrank_eq_succ hdim
  obtain ⟨u, v, hu, hv, huv, hli, hP1, hP2, hP3⟩ := exists_projective_frame hdim hP12 hP13 hP23
  obtain ⟨u', v', hu', hv', huv', hli', hQ1, hQ2, hQ3⟩ :=
    exists_projective_frame hdim hQ12 hQ13 hQ23
  obtain ⟨A, μ, hμ0, hAu, hAv⟩ := exists_specialLinearGroup_frame hdim hsq hli hli'
  have hsmul : ∀ (w : V) (hw : w ≠ 0) (w' : V) (hw' : w' ≠ 0),
      (A : V ≃ₗ[K] V) w = μ • w' → A • mk K w hw = mk K w' hw' := by
    intro w hw w' hw' hval
    have hval' : (SpecialLinearGroup.toLinearEquiv A) • w = μ • w' := hval
    rw [Projectivization.specialLinearGroup_smul_def, smul_mk, mk_eq_mk_iff]
    exact ⟨Units.mk0 μ hμ0, by simpa [Units.smul_def] using hval'.symm⟩
  refine ⟨A, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hP1, ← hQ1]; exact hsmul u hu u' hu' hAu
  · rw [← hP2, ← hQ2]; exact hsmul v hv v' hv' hAv
  · rw [← hP3, ← hQ3]
    exact hsmul (u + v) huv (u' + v') huv' (by rw [map_add, hAu, hAv, smul_add])
  · rintro B ⟨hB1, hB2, hB3⟩
    have hfix : ∀ P : ℙ K V, A • P = B • P → (B⁻¹ * A) • P = P := by
      intro P hP
      rw [mul_smul, hP, ← mul_smul, inv_mul_cancel, one_smul]
    have h1 : A • P₁ = B • P₁ := by
      rw [hB1, ← hP1, ← hQ1]; exact hsmul u hu u' hu' hAu
    have h2 : A • P₂ = B • P₂ := by
      rw [hB2, ← hP2, ← hQ2]; exact hsmul v hv v' hv' hAv
    have h3 : A • P₃ = B • P₃ := by
      rw [hB3, ← hP3, ← hQ3]
      exact hsmul (u + v) huv (u' + v') huv' (by rw [map_add, hAu, hAv, smul_add])
    have := eq_one_of_fixes_three hdim hP12 hP13 hP23
      (hfix P₁ h1) (hfix P₂ h2) (hfix P₃ h3)
    exact inv_mul_eq_one.mp this

/-! ### 有限体の場合 — Isaacs の主張 (`q` が 2 の冪) そのもの -/

/-- **標数 2 の有限体では平方写像が全単射**: `x ↦ x²` は標数 2 ゆえ単射で,
有限性から全射になる。 -/
lemma exists_sq_of_charTwo [Finite K] [CharP K 2] (c : K) : ∃ d : K, d * d = c := by
  have hinj : Function.Injective fun x : K => x * x := by
    intro x y hxy
    have hfac : (x - y) * (x + y) = 0 := by
      simp only at hxy
      linear_combination hxy
    rcases mul_eq_zero.mp hfac with h | h
    · linear_combination h
    · linear_combination h - CharTwo.add_self_eq_zero y
  exact Finite.injective_iff_surjective.mp hinj c

/-- `ℙ K (Fin 2 → K)` の点 (= 2 次元空間の 1 次元部分空間) はちょうど `q + 1` 個
(`q = |K|`)。 -/
theorem card_projectivization_fin_two [Finite K] :
    Nat.card (ℙ K (Fin 2 → K)) = Nat.card K + 1 :=
  Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)

/-- **Isaacs Problem 8A.17** (p. 236) 🎉 (教科書の形): `q` を 2 の冪, `K` を位数 `q` の
有限体とすると, `SL(2, q)` の 2 次元空間の 1 次元部分空間全体 (`q + 1` 点,
`card_projectivization_fin_two`) への作用は **sharply 3-transitive**。

抽象版 `existsUnique_specialLinearGroup_of_three_distinct` を
`Matrix.SpecialLinearGroup.toLin'_equiv` (行列版と線形写像版の `MulEquiv`) で移すだけ。
平方の全射性は `exists_sq_of_charTwo` から得る。 -/
theorem existsUnique_matrixSpecialLinearGroup_of_three_distinct [Finite K] [CharP K 2]
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : ℙ K (Fin 2 → K)}
    (hP12 : P₁ ≠ P₂) (hP13 : P₁ ≠ P₃) (hP23 : P₂ ≠ P₃)
    (hQ12 : Q₁ ≠ Q₂) (hQ13 : Q₁ ≠ Q₃) (hQ23 : Q₂ ≠ Q₃) :
    ∃! A : Matrix.SpecialLinearGroup (Fin 2) K,
      A • P₁ = Q₁ ∧ A • P₂ = Q₂ ∧ A • P₃ = Q₃ := by
  have hdim : Module.finrank K (Fin 2 → K) = 2 := by simp
  obtain ⟨A, ⟨hA1, hA2, hA3⟩, huniq⟩ :=
    existsUnique_specialLinearGroup_of_three_distinct (V := Fin 2 → K) hdim
      exists_sq_of_charTwo hP12 hP13 hP23 hQ12 hQ13 hQ23
  refine ⟨Matrix.SpecialLinearGroup.toLin'_equiv.symm A, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Projectivization.matrixSpecialLinearGroup_smul_def, MulEquiv.apply_symm_apply]
    exact hA1
  · rw [Projectivization.matrixSpecialLinearGroup_smul_def, MulEquiv.apply_symm_apply]
    exact hA2
  · rw [Projectivization.matrixSpecialLinearGroup_smul_def, MulEquiv.apply_symm_apply]
    exact hA3
  · rintro B ⟨hB1, hB2, hB3⟩
    have hB : Matrix.SpecialLinearGroup.toLin'_equiv B = A := by
      refine huniq _ ⟨?_, ?_, ?_⟩
      · rw [← Projectivization.matrixSpecialLinearGroup_smul_def]; exact hB1
      · rw [← Projectivization.matrixSpecialLinearGroup_smul_def]; exact hB2
      · rw [← Projectivization.matrixSpecialLinearGroup_smul_def]; exact hB3
    rw [← hB, MulEquiv.symm_apply_apply]

end SharplyThreeTransitive

end OddOrder.Isaacs.Ch08
