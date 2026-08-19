/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems3F

/-!
# Isaacs §3F の演習 — `SL(2,3)` (書籍 pp. 110-111, Problems 3F.4 / 3F.5)

`S = SL(2,3)` (3 元体上の行列式 1 の 2×2 行列群) についての演習。

* **3F.4** `card_specialLinearTwoThree` (`|S| = 24`) +
  `exists_normal_sylow_two_mulEquiv_quaternion` (正規 Sylow 2-部分群 `≅ Q_8`)。
* **3F.5** `S ⊴ G = GL(2,3)` は指数 2。`G ∖ S` は位数 2 の元 `g = diag(1,-1)` をもつが
  位数 4 の元をもたない (`orderOf_ne_four_of_notMem_specialLinear`)。一方 Thm 3.36 で
  `S` を指数 2 で含む群 `H` を作ると, `H ∖ S` は位数 4 の元 `h` (`g` と同じ自己同型を
  誘導する) をもち位数 2 の元をもたない。`G ∖ S` と `H ∖ S` はどちらも位数 8 の元をもつ
  (`exists_index_two_extension_orderOf_four`)。

⚠ **配置の理由**: 行列群の import (`Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`) と
`decide` による具体計算はここだけの話題なので, §3F の一般論 (`Problems3F.lean`) とは
別 leaf にしてある。

⚠ **`decide` の使用について**: `SL(2,3)` は 24 元, `Matrix (Fin 2) (Fin 2) (ZMod 3)` は
81 元で `DecidableEq` + `Fintype` があるため, 位数計算・準同型性 (64 通り)・単射性・
正規性 (24×8 通り) はすべて kernel で決定できる (合計 ~6s)。
**`native_decide` は使わない** (`ofReduceBool` 公理が入り axiom-clean が壊れる)。
-/

namespace OddOrder.Isaacs.Ch03

open Matrix QuaternionGroup

section /- 3F.4: SL(2,3) -/

/-- `SL(2,3)` = `ZMod 3` 上の行列式 1 の 2×2 行列群 (書籍 3F.4/3F.5 の `S`)。 -/
abbrev SpecialLinearTwoThree := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

/-- **Isaacs Problem 3F.4 (前半)** (書籍 p. 110): `|SL(2,3)| = 24`。 -/
theorem card_specialLinearTwoThree : Nat.card SpecialLinearTwoThree = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- `SL(2,3)` の中の四元数 `i = [[0,-1],[1,0]]` (`i² = -I`)。 -/
def slQuaternionI : SpecialLinearTwoThree := ⟨!![0, -1; 1, 0], by decide⟩

/-- `SL(2,3)` の中の四元数 `j = [[1,1],[1,-1]]` (`j² = -I`, `j⁻¹ i j = i⁻¹`)。 -/
def slQuaternionJ : SpecialLinearTwoThree := ⟨!![1, 1; 1, -1], by decide⟩

/-- `Q_8 → SL(2,3)` の台写像: `a k ↦ i ^ k`, `xa k ↦ j * i ^ k`。

`QuaternionGroup 2` の生成元関係 (`a 1` の位数 4, `x² = a 2`, `x⁻¹ a x = a⁻¹`) が
`i`, `j` で成り立つので準同型になる。 -/
def quaternionToSL23Fun : QuaternionGroup 2 → SpecialLinearTwoThree
  | .a i => slQuaternionI ^ i.val
  | .xa i => slQuaternionJ * slQuaternionI ^ i.val

/-- `Q_8 → SL(2,3)` の準同型 (`map_mul` は 64 通りを `decide`)。 -/
def quaternionToSL23 : QuaternionGroup 2 →* SpecialLinearTwoThree :=
  MonoidHom.mk' quaternionToSL23Fun (by decide)

theorem quaternionToSL23_injective : Function.Injective quaternionToSL23 := by decide

/-- `SL(2,3)` の Sylow 2-部分群 = `Q_8` の像 `{±I, ±i, ±j, ±k}`。 -/
def sylowTwoSL23 : Subgroup SpecialLinearTwoThree := quaternionToSL23.range

theorem sylowTwoSL23_conj_mem : ∀ n ∈ quaternionToSL23.range,
    ∀ g : SpecialLinearTwoThree, g * n * g⁻¹ ∈ quaternionToSL23.range := by decide

instance sylowTwoSL23_normal : sylowTwoSL23.Normal := ⟨sylowTwoSL23_conj_mem⟩

/-- `Q_8 ≃ SL(2,3)` の Sylow 2-部分群。 -/
noncomputable def quaternionMulEquivSylowTwoSL23 : QuaternionGroup 2 ≃* ↥sylowTwoSL23 :=
  MonoidHom.ofInjective quaternionToSL23_injective

theorem card_sylowTwoSL23 : Nat.card ↥sylowTwoSL23 = 8 := by
  rw [← Nat.card_congr quaternionMulEquivSylowTwoSL23.toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

/-- **Isaacs Problem 3F.4** (書籍 p. 110): `SL(2,3)` は位数 24 で, その Sylow
2-部分群は正規かつ `Q_8` と同型。

具体的には `{±I, ±i, ±j, ±k}` (`i = [[0,-1],[1,0]]`, `j = [[1,1],[1,-1]]`) が
その Sylow 2-部分群。 -/
theorem exists_normal_sylow_two_mulEquiv_quaternion :
    ∃ P : Sylow 2 SpecialLinearTwoThree, (P : Subgroup SpecialLinearTwoThree).Normal ∧
      Nonempty (↥(P : Subgroup SpecialLinearTwoThree) ≃* QuaternionGroup 2) := by
  have h24 : (24 : ℕ).factorization 2 = 3 := by
    have hd : (2 : ℕ) ^ 3 ∣ 24 := by norm_num
    have hnd : ¬ (2 : ℕ) ^ 4 ∣ 24 := by norm_num
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mp hd
    have hlt : ¬ 4 ≤ (24 : ℕ).factorization 2 := fun h =>
      hnd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mpr h)
    omega
  have hfac : Nat.card ↥sylowTwoSL23
      = 2 ^ (Nat.card SpecialLinearTwoThree).factorization 2 := by
    rw [card_sylowTwoSL23, card_specialLinearTwoThree, h24]
    norm_num
  refine ⟨Sylow.ofCard sylowTwoSL23 hfac, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact sylowTwoSL23_normal
  · rw [Sylow.coe_ofCard]
    exact ⟨quaternionMulEquivSylowTwoSL23.symm⟩

end -- 3F.4

section /- 3F.5: GL(2,3) と Thm 3.36 で作る H -/

/-! ### `g = diag(1,-1) ∈ GL(2,3) ∖ SL(2,3)` と誘導自己同型 `σ` -/

/-- `GL(2,3)` = `ZMod 3` 上の可逆 2×2 行列群 (書籍 3F.5 の `G`)。 -/
abbrev GeneralLinearTwoThree := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

/-- 書籍 3F.5 の `g` の行列部分 `diag(1,-1)` (行列式 `-1`, 2 乗は `I`)。 -/
def glReflectionMatrix : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; 0, -1]

theorem glReflectionMatrix_mul_self : glReflectionMatrix * glReflectionMatrix = 1 := by decide

theorem glReflectionMatrix_det : glReflectionMatrix.det = -1 := by decide

/-- **書籍 3F.5 の `g`**: `diag(1,-1) ∈ GL(2,3) ∖ SL(2,3)`, 位数 2。 -/
def glReflection : GeneralLinearTwoThree :=
  ⟨glReflectionMatrix, glReflectionMatrix, glReflectionMatrix_mul_self,
    glReflectionMatrix_mul_self⟩

@[simp] theorem glReflection_inv : glReflection⁻¹ = glReflection := rfl

/-- `-I ∈ SL(2,3)`: `SL(2,3)` の唯一の位数 2 の元 (= `Q_8` の中心元)。 -/
def slNegOne : SpecialLinearTwoThree := ⟨!![-1, 0; 0, -1], by decide⟩

private theorem reflection_conj_aux (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    glReflectionMatrix * (glReflectionMatrix * A * glReflectionMatrix) * glReflectionMatrix
      = A := by
  rw [show glReflectionMatrix * (glReflectionMatrix * A * glReflectionMatrix) * glReflectionMatrix
      = (glReflectionMatrix * glReflectionMatrix) * A * (glReflectionMatrix * glReflectionMatrix) by
    simp only [Matrix.mul_assoc], glReflectionMatrix_mul_self, one_mul, mul_one]

/-- **`g` が `SL(2,3)` に誘導する自己同型 `σ`**: `x ↦ g x g⁻¹` (`g⁻¹ = g` なので `g x g`)。

`glReflection_conj` が「これが本当に `G` の中の共役である」ことを述べる。 -/
def slConjReflection : MulAut SpecialLinearTwoThree where
  toFun x := ⟨glReflectionMatrix * x.val * glReflectionMatrix, by
    rw [Matrix.det_mul, Matrix.det_mul, glReflectionMatrix_det, x.property]; decide⟩
  invFun x := ⟨glReflectionMatrix * x.val * glReflectionMatrix, by
    rw [Matrix.det_mul, Matrix.det_mul, glReflectionMatrix_det, x.property]; decide⟩
  left_inv x := Subtype.ext (reflection_conj_aux x.val)
  right_inv x := Subtype.ext (reflection_conj_aux x.val)
  map_mul' x y := Subtype.ext <| by
    change glReflectionMatrix * (x.val * y.val) * glReflectionMatrix
        = (glReflectionMatrix * x.val * glReflectionMatrix)
          * (glReflectionMatrix * y.val * glReflectionMatrix)
    rw [show (glReflectionMatrix * x.val * glReflectionMatrix)
          * (glReflectionMatrix * y.val * glReflectionMatrix)
        = glReflectionMatrix * x.val * (glReflectionMatrix * glReflectionMatrix)
          * (y.val * glReflectionMatrix) by simp only [Matrix.mul_assoc],
      glReflectionMatrix_mul_self, mul_one]
    simp only [Matrix.mul_assoc]

/-! ### `SL(2,3)` の中の決定可能な事実

3F.5 の全体は「`G ∖ S` と `H ∖ S` の元の 2 乗が `SL(2,3)` のどの元か」に帰着する。
`(g x)² = σ(x) x`, `(h ι(x))² = σ(x) (-I) x` なので, 必要なのは下の 2 つの
**核心の計算** (どちらも 24 元の全数検査) である。 -/

theorem slNegOne_ne_one : slNegOne ≠ 1 := by decide

theorem slNegOne_mul_self : slNegOne * slNegOne = 1 := by decide

/-- `SL(2,3)` の位数 2 の元は `-I` ただ 1 つ (Sylow 2-部分群 `Q_8` が正規だから)。 -/
theorem eq_one_or_eq_slNegOne_of_mul_self (x : SpecialLinearTwoThree) (h : x * x = 1) :
    x = 1 ∨ x = slNegOne := by revert x; decide

theorem mulAut_conj_slNegOne : MulAut.conj slNegOne = (1 : MulAut SpecialLinearTwoThree) :=
  MulEquiv.ext (by decide)

theorem slConjReflection_slNegOne : slConjReflection slNegOne = slNegOne := by decide

/-- Thm 3.36 を `m = 2`, `a = -I`, `σ = slConjReflection` で使うための仮説
`σ² = conj a` (`g² = 1` なので `σ² = 1`, `-I` は中心的なので `conj (-I) = 1`)。 -/
theorem slConjReflection_sq : slConjReflection ^ 2 = MulAut.conj slNegOne := by
  rw [mulAut_conj_slNegOne, sq]
  exact MulEquiv.ext slConjReflection.left_inv

/-- **核心の計算 (G 側)**: `σ(x) x ≠ -I` (`x ∈ SL(2,3)`)。

手計算では: `x = !![a,b;c,d]` に対し `σ(x) x = !![a²-bc, b(a-d); c(d-a), d²-bc]` で,
これが `-I` なら `a(a-d) = 1` (よって `a ≠ 0`, `a ≠ d`) から `b = c = 0`, したがって
`a² = -1` となるが `ZMod 3` の平方は `0, 1` のみで矛盾。 -/
theorem slConjReflection_mul_ne_slNegOne (x : SpecialLinearTwoThree) :
    slConjReflection x * x ≠ slNegOne := by revert x; decide

/-- **核心の計算 (H 側)**: `σ(x) (-I) x ≠ 1`。`-I` が中心的なので
`slConjReflection_mul_ne_slNegOne` と同値な事実。 -/
theorem slConjReflection_mul_slNegOne_mul_ne_one (x : SpecialLinearTwoThree) :
    slConjReflection x * slNegOne * x ≠ 1 := by revert x; decide

/-- 位数 8 の元を作る証人 (G 側): `σ(j) j = i` は位数 4。 -/
theorem slConjReflection_slQuaternionJ :
    slConjReflection slQuaternionJ * slQuaternionJ = slQuaternionI := by decide

theorem slQuaternionI_mul_self : slQuaternionI * slQuaternionI = slNegOne := by decide

/-- `-i = !![0,1;-1,0] ∈ SL(2,3)` (位数 4)。 -/
def slNegQuaternionI : SpecialLinearTwoThree := ⟨!![0, 1; -1, 0], by decide⟩

/-- 位数 8 の元を作る証人 (H 側): `σ(j) (-I) j = -i` は位数 4。 -/
theorem slConjReflection_slQuaternionJ_slNegOne :
    slConjReflection slQuaternionJ * slNegOne * slQuaternionJ = slNegQuaternionI := by decide

theorem slNegQuaternionI_mul_self : slNegQuaternionI * slNegQuaternionI = slNegOne := by decide

/-! ### `SL(2,3) ≤ GL(2,3)` は指数 2 -/

/-- `SL(2,3)` を `GL(2,3)` の部分群として見たもの (書籍 3F.5 の `S ⊆ G`)。 -/
def specialLinearTwoThreeSubgroup : Subgroup GeneralLinearTwoThree :=
  (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod 3)).range

theorem specialLinearTwoThreeSubgroup_eq_ker : specialLinearTwoThreeSubgroup
    = (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod 3)).ker := by
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact Matrix.SpecialLinearGroup.coeToGL_det x
  · intro hA
    have hdet : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
      have := congrArg Units.val hA
      simpa [Matrix.GeneralLinearGroup.det] using this
    exact ⟨⟨(A : Matrix (Fin 2) (Fin 2) (ZMod 3)), hdet⟩, Units.ext rfl⟩

theorem mem_specialLinearTwoThreeSubgroup_iff (A : GeneralLinearTwoThree) :
    A ∈ specialLinearTwoThreeSubgroup ↔ Matrix.GeneralLinearGroup.det A = 1 := by
  rw [specialLinearTwoThreeSubgroup_eq_ker]
  exact MonoidHom.mem_ker

/-- **Isaacs Problem 3F.5 (前提)** (書籍 p. 110): `SL(2,3)` は `GL(2,3)` で指数 2。

`det : GL(2,3) → (ZMod 3)ˣ` の核が `SL(2,3)` で, `det` は全射, `|(ZMod 3)ˣ| = 2`。 -/
theorem specialLinearTwoThreeSubgroup_index : specialLinearTwoThreeSubgroup.index = 2 := by
  rw [specialLinearTwoThreeSubgroup_eq_ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective,
    Nat.card_congr (Subgroup.topEquiv (G := (ZMod 3)ˣ)).toEquiv, Nat.card_eq_fintype_card]
  decide

/-- `(ZMod 3)ˣ` は位数 2 なので `1` でない単元は `-1`。 -/
theorem units_zmodThree_eq_neg_one (u : (ZMod 3)ˣ) (hu : u ≠ 1) : u = -1 := by
  revert u; decide

theorem glReflection_det : Matrix.GeneralLinearGroup.det glReflection = -1 := by decide

theorem glReflection_notMem : glReflection ∉ specialLinearTwoThreeSubgroup := by
  rw [mem_specialLinearTwoThreeSubgroup_iff]; decide

/-- `G ∖ S = g S`: `S` の外の元は `g x` (`x ∈ SL(2,3)`) と一意に書ける。 -/
theorem exists_eq_glReflection_mul (A : GeneralLinearTwoThree)
    (hA : A ∉ specialLinearTwoThreeSubgroup) :
    ∃ x : SpecialLinearTwoThree, A = glReflection * Matrix.SpecialLinearGroup.toGL x := by
  have hAdet : Matrix.GeneralLinearGroup.det A ≠ 1 := by
    rwa [mem_specialLinearTwoThreeSubgroup_iff] at hA
  have hAeq : Matrix.GeneralLinearGroup.det A = -1 := units_zmodThree_eq_neg_one _ hAdet
  have hmem : glReflection⁻¹ * A ∈ specialLinearTwoThreeSubgroup := by
    rw [mem_specialLinearTwoThreeSubgroup_iff, map_mul, map_inv, glReflection_det, hAeq]
    decide
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, by rw [hx]; group⟩

/-- `slConjReflection` は本当に `g ∈ GL(2,3)` が `SL(2,3)` に誘導する自己同型。 -/
theorem glReflection_conj (x : SpecialLinearTwoThree) :
    glReflection * (Matrix.SpecialLinearGroup.toGL x) * glReflection⁻¹
      = Matrix.SpecialLinearGroup.toGL (slConjReflection x) :=
  Units.ext rfl

/-- `(g x)² = σ(x) x` (`g² = 1` を使う)。 -/
theorem sq_glReflection_mul (x : SpecialLinearTwoThree) :
    (glReflection * Matrix.SpecialLinearGroup.toGL x) ^ 2
      = Matrix.SpecialLinearGroup.toGL (slConjReflection x * x) := by
  rw [map_mul, ← glReflection_conj x, glReflection_inv, sq]
  group

/-! ### `G = GL(2,3)` 側の結論 -/

private theorem orderOf_eq_four_of {M : Type*} [Monoid M] {x : M}
    (h2 : x ^ 2 ≠ 1) (h4 : x ^ 4 = 1) : orderOf x = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x)
    (by rw [show (2 : ℕ) ^ (1 : ℕ) = 2 from rfl]; exact h2)
    (by rw [show (2 : ℕ) ^ (1 + 1 : ℕ) = 4 from rfl]; exact h4)
  rwa [show (2 : ℕ) ^ (1 + 1 : ℕ) = 4 from rfl] at h

private theorem orderOf_eq_eight_of {M : Type*} [Monoid M] {x : M}
    (h4 : x ^ 4 ≠ 1) (h8 : x ^ 8 = 1) : orderOf x = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := x)
    (by rw [show (2 : ℕ) ^ (2 : ℕ) = 4 from rfl]; exact h4)
    (by rw [show (2 : ℕ) ^ (2 + 1 : ℕ) = 8 from rfl]; exact h8)
  rwa [show (2 : ℕ) ^ (2 + 1 : ℕ) = 8 from rfl] at h

/-- **Isaacs Problem 3F.5 (1)** (書籍 p. 110): `G ∖ S` は位数 2 の元 `g = diag(1,-1)`
をもつ。 -/
theorem orderOf_glReflection : orderOf glReflection = 2 :=
  orderOf_eq_prime (by decide) (by decide)

/-- **Isaacs Problem 3F.5 (2)** (書籍 p. 110): `G ∖ S = GL(2,3) ∖ SL(2,3)` は
位数 4 の元をもたない。

`A ∈ G ∖ S` は `A = g x` (`x ∈ S`) と書け, `A² = σ(x) x ∈ S`。`orderOf A = 4` なら
`σ(x) x` は `S` の位数 2 の元, すなわち `-I` になるが, これは
`slConjReflection_mul_ne_slNegOne` に反する。 -/
theorem orderOf_ne_four_of_notMem_specialLinear (A : GeneralLinearTwoThree)
    (hA : A ∉ specialLinearTwoThreeSubgroup) : orderOf A ≠ 4 := by
  intro h4
  obtain ⟨x, rfl⟩ := exists_eq_glReflection_mul A hA
  have hsq := sq_glReflection_mul x
  have h41 : (glReflection * Matrix.SpecialLinearGroup.toGL x) ^ 4 = 1 := by
    rw [← h4]; exact pow_orderOf_eq_one _
  have hyy : (slConjReflection x * x) * (slConjReflection x * x) = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_one, ← hsq, ← pow_add]
    exact h41
  have hy1 : slConjReflection x * x ≠ 1 := by
    intro he
    have h2 : (glReflection * Matrix.SpecialLinearGroup.toGL x) ^ 2 = 1 := by
      rw [hsq, he, map_one]
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at hdvd
    exact absurd hdvd (by decide)
  rcases eq_one_or_eq_slNegOne_of_mul_self _ hyy with h | h
  · exact hy1 h
  · exact slConjReflection_mul_ne_slNegOne x h

/-- **Isaacs Problem 3F.5 (5a)** (書籍 p. 111): `G ∖ S` は位数 8 の元をもつ。

証人は `g j` (`j = !![1,1;1,-1]`): `(g j)² = σ(j) j = i` は位数 4。 -/
theorem exists_orderOf_eq_eight_notMem_specialLinear :
    ∃ A : GeneralLinearTwoThree, A ∉ specialLinearTwoThreeSubgroup ∧ orderOf A = 8 := by
  refine ⟨glReflection * Matrix.SpecialLinearGroup.toGL slQuaternionJ, ?_, ?_⟩
  · rw [mem_specialLinearTwoThreeSubgroup_iff, map_mul, glReflection_det,
      Matrix.SpecialLinearGroup.coeToGL_det]
    decide
  · have hs2 : (glReflection * Matrix.SpecialLinearGroup.toGL slQuaternionJ) ^ 2
        = Matrix.SpecialLinearGroup.toGL slQuaternionI := by
      rw [sq_glReflection_mul, slConjReflection_slQuaternionJ]
    have hs4 : (glReflection * Matrix.SpecialLinearGroup.toGL slQuaternionJ) ^ 4
        = Matrix.SpecialLinearGroup.toGL slNegOne := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2, pow_two, ← map_mul, slQuaternionI_mul_self]
    refine orderOf_eq_eight_of ?_ ?_
    · rw [hs4]
      intro hc
      exact slNegOne_ne_one (Matrix.SpecialLinearGroup.toGL_injective (by rw [hc, map_one]))
    · rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hs4, pow_two, ← map_mul, slNegOne_mul_self,
        map_one]

/-! ### Thm 3.36 で作る `H` -/

/-- **Isaacs Problem 3F.5 (3)(4)(5b)** (書籍 pp. 110-111) ⭐:
`S = SL(2,3)` を指数 2 で含む群 `H` で,

* `H ∖ S` が位数 4 の元 `h` をもち, `h` が `S` に誘導する自己同型が
  `g ∈ G = GL(2,3)` の誘導するもの (`slConjReflection`) と一致し,
* `H ∖ S` は位数 2 の元をもたず,
* `H ∖ S` は位数 8 の元をもつ

ものが存在する。

**証明**: Thm 3.36 (`cyclic_extension_exists`) を `N = SL(2,3)`, `m = 2`,
`a = -I`, `σ = slConjReflection` に適用する。仮説 `σ(-I) = -I` と
`σ² = conj (-I)` はどちらも成り立つ (`g² = 1` かつ `-I` は中心的) ので,
`h² = ι(-I)` かつ `h ι(x) h⁻¹ = ι(σ x)` なる `h` が得られる。

`H ∖ S` の元は `h ι(x)` の形で `(h ι(x))² = ι(σ(x) (-I) x)` (`sq_mul_coe_of_conj`)。
したがって位数 2 の元が無いことは `slConjReflection_mul_slNegOne_mul_ne_one` そのもの
(= `G ∖ S` に位数 4 の元が無いことと同じ計算)。位数 8 の元は `h ι(j)`:
その 2 乗は `ι(-i)` で位数 4。 -/
theorem exists_index_two_extension_orderOf_four :
    ∃ (H : Type) (_ : Group H) (N : Subgroup H)
      (ι : SpecialLinearTwoThree ≃* ↥N) (h : H),
      N.index = 2 ∧ h ∉ N ∧ orderOf h = 4 ∧
      (∀ x : SpecialLinearTwoThree, h * (ι x : H) * h⁻¹ = (ι (slConjReflection x) : H)) ∧
      (∀ t : H, t ∉ N → orderOf t ≠ 2) ∧
      (∃ t : H, t ∉ N ∧ orderOf t = 8) := by
  obtain ⟨H, hHgrp, N, hNnorm, ι, h, hgen, hcard, hhsq, hconj⟩ :=
    cyclic_extension_exists (N := SpecialLinearTwoThree) (m := 2) (by norm_num)
      slNegOne slConjReflection slConjReflection_slNegOne slConjReflection_sq
  -- ⚠ `haveI` だと本体を忘れて `hHgrp` と defeq でない別インスタンスが立つ (instance
  -- mismatch でほぼ全ステップが失敗する) ので `letI` を使う。
  let : Group H := hHgrp
  let : N.Normal := hNnorm
  have hhN : h ∉ N := notMem_of_zpowers_quotientMk_eq_top hgen hcard
  have hsqcoset : ∀ x : SpecialLinearTwoThree,
      (h * (ι x : H)) ^ 2 = (ι (slConjReflection x * slNegOne * x) : H) :=
    sq_mul_coe_of_conj ι slConjReflection hhsq hconj
  have hnegsq : (ι slNegOne : H) * (ι slNegOne : H) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, slNegOne_mul_self, map_one, Subgroup.coe_one]
  refine ⟨H, hHgrp, N, ι, h, hcard, hhN, ?_, hconj, ?_, ?_⟩
  · -- `h² = ι(-I) ≠ 1` かつ `h⁴ = ι((-I)²) = 1`
    refine orderOf_eq_four_of ?_ ?_
    · rw [hhsq]
      exact fun hc => slNegOne_ne_one ((coe_mulEquiv_eq_one_iff ι).mp hc)
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hhsq, pow_two, hnegsq]
  · -- `H ∖ S` に位数 2 の元は無い
    intro t ht h2
    obtain ⟨n, hn⟩ := exists_eq_mul_of_notMem_of_card_quotient_eq_two hcard hhN ht
    have hn' : t = h * (ι (ι.symm n) : H) := by rw [MulEquiv.apply_symm_apply]; exact hn
    rw [hn'] at h2
    have hone := pow_orderOf_eq_one (h * (ι (ι.symm n) : H))
    rw [h2, hsqcoset (ι.symm n)] at hone
    exact slConjReflection_mul_slNegOne_mul_ne_one _ ((coe_mulEquiv_eq_one_iff ι).mp hone)
  · -- `H ∖ S` は位数 8 の元 `h ι(j)` をもつ
    refine ⟨h * (ι slQuaternionJ : H), ?_, ?_⟩
    · intro hmem
      refine hhN ?_
      have hrw : h = (h * (ι slQuaternionJ : H)) * (ι slQuaternionJ : H)⁻¹ := by group
      rw [hrw]
      exact N.mul_mem hmem (N.inv_mem (ι slQuaternionJ).2)
    · have hs2 : (h * (ι slQuaternionJ : H)) ^ 2 = (ι slNegQuaternionI : H) := by
        rw [hsqcoset, slConjReflection_slQuaternionJ_slNegOne]
      have hs4 : (h * (ι slQuaternionJ : H)) ^ 4 = (ι slNegOne : H) := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2, pow_two, ← Subgroup.coe_mul, ← map_mul,
          slNegQuaternionI_mul_self]
      refine orderOf_eq_eight_of ?_ ?_
      · rw [hs4]
        exact fun hc => slNegOne_ne_one ((coe_mulEquiv_eq_one_iff ι).mp hc)
      · rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hs4, pow_two, hnegsq]

end -- 3F.5

end OddOrder.Isaacs.Ch03
