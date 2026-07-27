/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Sylow
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch03_SplitExtensions.Basic
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.Isaacs.Ch08_PermutationGroups.HalfTransitive
import OddOrder.Isaacs.Ch08_PermutationGroups.RegularNormal

/-!
# Isaacs, Finite Group Theory — Problems 8A (pp. 235–236)

Isaacs §8A の章末演習。「regular 部分群」は `RegularNormal.lean` の流儀に合わせ
**軌道写像 `smulBase N α : ↥N → Ω` が全単射**であることとして扱う (Thm 8.5)。
半正則 (semiregular) は同じく**軌道写像が単射**、同値に `N ⊓ G_α = ⊥`
(`injective_smulBase_iff_disjoint_stabilizer`)。

## Main results

- `regularRep`, `bijective_smulBase_regularRep_range` — 型の同値に沿って運んだ
  左正則表現とその像の regular 性 (8A.1 / 8A.3 / 8A.4 の共通道具)。
- `exists_regular_subgroups_of_equiv`, `exists_regular_subgroups_of_card_eq` —
  **Problem 8A.1** 前半: `|A| = |B|` なら `Sym(A)` は `A`, `B` に同型な regular 部分群を
  ともにもつ。
- `transZFour`, `flipZFour` と `D₈` の関係式群 — **Problem 8A.1 後半**の計算核:
  `ZMod 4` 上で `s t s⁻¹ = t⁻¹`, `t s t⁻¹ = s t²`, `V` の各元が位数 ≤ 2, `t² ≠ 1`。
  すべて `decide` で確認 (答は「同型でない regular normal 部分群はもてる」)。
- `regularRepRight`, `exists_two_distinct_regular_normal_of_center_eq_bot` —
  **Problem 8A.3**: `Z(G) = 1` (かつ非自明) なら `Sym(G)` の中に `G` に同型な相異なる
  regular normal 部分群が 2 つある (左正則表現の像と右正則表現の像)。
- `smul_eq_self_of_mem_centralizer`, `centralizer_inf_stabilizer_eq_bot`,
  `bijective_smulBase_top_of_comm` — **Problem 8A.2**: transitive な `H ≤ G` の
  中心化群 `C_G(H)` は半正則。帰結として可換 transitive な置換群は regular。
- `centralizer_eq_of_regular_of_inf_eq_bot`, `regularPairHom`,
  `mulEquiv_and_center_eq_bot_of_regular_normal` — **Problem 8A.4**: regular normal な
  `U`, `V` が `U ⊓ V = 1` を満たすと `C_G(U) = V` となり, `U ≅ V` で中心はともに自明。
- `smul_mem_fixedPoints_of_mem_normalizer`,
  `exists_mem_normalizer_stabilizer_smul_eq`,
  `eq_of_mem_fixedPoints_stabilizer_of_transitive_on_compl` — **Problem 8A.5**:
  `Δ = Fix(G_α)` は `N_G(G_α)` で保たれ, その上で `N_G(G_α)` は推移的。`k ≥ 2` かつ
  `|Δ| ≥ 2` は `|Ω| = 2` を強制するので, `r = min(k, |Δ|)` の主張はこの推移性に尽きる。
- `exists_mem_conj_eq_of_sylow_le`, `exists_mem_normalizer_sylow_smul_eq` —
  **Problem 8A.6**: `Q ∈ Syl_p(G_α)` について `N_G(Q)` は `Fix(Q)` に推移的。
- `isFrobeniusAction_of_comm_of_half_transitive`,
  `isFrobeniusAction_and_isCyclic_of_comm_of_half_transitive` — **Problem 8A.7**:
  可換群の忠実 half-transitive 作用は Frobenius で, その群は巡回。
- `smul_orbit_eq_orbit_smul`, `card_orbit_eq_of_normal` — **Problem 8A.8**:
  transitive な `G` の正規部分群 `N` について `G` は `N`-軌道を推移的に置換し,
  したがって `N` は half-transitive (すべての `N`-軌道が同じ濃度)。
- `isPretransitive_of_normal_of_two_transitive` — **Problem 8A.9**: 2-transitive な `G` の
  非自明に作用する正規部分群は推移的。
- `card_le_four_of_three_transitive_on_nonidentity`,
  `card_le_four_of_regular_normal_of_stabilizer_three_transitive` —
  **Problem 8A.10 の核心**: 自己同型群が `N ∖ {1}` に 3-transitive なら `|N| ≤ 4`;
  `N` が regular normal で `G_α` が `Ω ∖ {α}` に 3-transitive なら `|N| ≤ 4`。
- `card_eq_four_of_solvable_of_stabilizer_three_transitive`,
  `nonempty_mulEquiv_perm_fin_four_of_four_transitive` — **Problem 8A.10**:
  可解な 4-transitive 置換群の次数は 4 で, したがって `S₄` に同型。
- `card_fixedBy_prod`, `sum_sq_card_fixedBy`, `card_orbits_prod_eq_two_iff`,
  `sum_sq_card_fixedBy_eq_two_mul_iff` — **Problem 8A.12**: 推移的な `G` について
  `G` が 2-transitive ⟺ 置換指標の 2 乗の平均が 2。
- `doubleCoset_transitive_iff` — **Problem 8A.15**: `G` の `H`-剰余類への作用が
  2-transitive ⟺ 二重剰余類が `H` とその外のちょうど 2 つ (= `H × H` の両側作用が
  `G` 上 2 軌道)。
- `cosetToOrbit`, `card_orbits_le_index`, `two_mul_card_orbits_le_index` —
  **Problem 8A.14** (後半込み): `G` 推移的で `[G:H] = m` なら
  `H` の軌道は高々 `m` 個 (`gH ↦ ⟦g⁻¹ • α⟧` が `G ⧸ H` からの全射)。
- `card_fixedBy_prod_three`, `sum_cube_card_fixedBy` — **Problem 8A.13** の骨格:
  置換指標の 3 乗和は `Ω³` 上の軌道数 × `|G|`。求める `m` は **5**
  (3 点の一致パターン `xxx` / `xxy` / `xyx` / `yxx` / 全相異)。
- `affineLineGroup`, `existsUnique_affineLineGroup_of_ne`,
  `affineLineGroup_isSolvable` — **Problem 8A.11**: 1 次元アフィン群
  `AGL(1, F) = {x ↦ ax + b}` は `F` 上 sharply 2-transitive で, metabelian ゆえ可解。
  有限体は各素数冪について存在するので, 次数 `q` の可解 sharply 2-transitive 群が得られる。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8A (pp. 235-236) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### 左正則表現 (8A.1 / 8A.3 / 8A.4 の共通道具) -/

/-- 型の同値 `e : Ω ≃ A` に沿って運んだ **`A` の左正則表現** `A →* Equiv.Perm Ω`,
`a ↦ (x ↦ e.symm (a * e x))`。

`Ω = A`, `e = Equiv.refl` のときが通常の Cayley 埋め込み。像は常に regular
(`bijective_smulBase_regularRep_range`)。 -/
def regularRep {A Ω : Type*} [Group A] (e : Ω ≃ A) : A →* Equiv.Perm Ω where
  toFun a := e.trans ((Equiv.mulLeft a).trans e.symm)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

@[simp] lemma regularRep_apply {A Ω : Type*} [Group A] (e : Ω ≃ A) (a : A) (x : Ω) :
    regularRep e a x = e.symm (a * e x) := rfl

lemma regularRep_injective {A Ω : Type*} [Group A] [Nonempty Ω] (e : Ω ≃ A) :
    Function.Injective (regularRep e) := by
  intro a b hab
  have := congrArg (fun p : Equiv.Perm Ω => e (p (e.symm 1))) hab
  simpa using this

/-- **左正則表現の像は regular**: 軌道写像 `a ↦ e.symm (a * e α)` は全単射。 -/
theorem bijective_smulBase_regularRep_range {A Ω : Type*} [Group A] [Nonempty Ω]
    (e : Ω ≃ A) (α : Ω) :
    Function.Bijective (smulBase (regularRep e).range α) := by
  constructor
  · rintro ⟨-, a, rfl⟩ ⟨-, b, rfl⟩ hnm
    have hab : a = b := by simpa [smulBase] using hnm
    exact Subtype.ext (congrArg (regularRep e) hab)
  · intro β
    refine ⟨⟨regularRep e (e β * (e α)⁻¹), ⟨_, rfl⟩⟩, ?_⟩
    simp only [smulBase_apply, Equiv.Perm.smul_def, regularRep_apply, inv_mul_cancel_right,
      Equiv.symm_apply_apply]

/-- **Isaacs Problem 8A.1** (p. 235), 前半: 位数の等しい二群 `A`, `B` に対し, ある置換群が
`A` に同型な regular 部分群と `B` に同型な regular 部分群をともにもつ。

構成は書籍の hint どおり対称群 `Sym(A)`: `A` 自身は Cayley 埋め込みで, `B` は型の同値
`B ≃ A` で運んだ左正則表現で入る。`A ≇ B` は構成には不要 (それが問題を面白くしているだけ)。 -/
theorem exists_regular_subgroups_of_equiv {A B : Type*} [Group A] [Group B] [Nonempty A]
    (e : B ≃ A) :
    ∃ N M : Subgroup (Equiv.Perm A),
      (∀ α : A, Function.Bijective (smulBase N α)) ∧
      (∀ α : A, Function.Bijective (smulBase M α)) ∧
      Nonempty (N ≃* A) ∧ Nonempty (M ≃* B) :=
  ⟨(regularRep (Equiv.refl A)).range, (regularRep e.symm).range,
    fun α => bijective_smulBase_regularRep_range _ α,
    fun α => bijective_smulBase_regularRep_range _ α,
    ⟨(MonoidHom.ofInjective (regularRep_injective (Equiv.refl A))).symm⟩,
    ⟨(MonoidHom.ofInjective (regularRep_injective (A := B) e.symm)).symm⟩⟩

/-- **Isaacs Problem 8A.1** (p. 235), 前半 (書籍の形): `|A| = |B|` なる有限群 `A`, `B` に対し
`Sym(A)` は `A` に同型な regular 部分群と `B` に同型な regular 部分群をともにもつ。 -/
theorem exists_regular_subgroups_of_card_eq {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (h : Nat.card A = Nat.card B) :
    ∃ N M : Subgroup (Equiv.Perm A),
      (∀ α : A, Function.Bijective (smulBase N α)) ∧
      (∀ α : A, Function.Bijective (smulBase M α)) ∧
      Nonempty (N ≃* A) ∧ Nonempty (M ≃* B) :=
  exists_regular_subgroups_of_equiv (Finite.card_eq.mp h.symm).some

/-! ### Problem 8A.1 後半 — 同型でない regular normal 部分群の対 (`D₈ ≤ S₄`) -/

section KleinCounterexample

/-- `ZMod 4` の平行移動 `x ↦ x + 1`。 -/
def transZFour : Equiv.Perm (ZMod 4) := Equiv.addRight 1

/-- `ZMod 4` の反転 `x ↦ 1 - x`。 -/
def flipZFour : Equiv.Perm (ZMod 4) := (Equiv.neg (ZMod 4)).trans (Equiv.addRight 1)

/-! `D₈ = ⟨t, s⟩ ≤ Sym(ZMod 4)` の関係式。`ZMod 4` は決定可能なのですべて `decide` で
確認できる。`T = ⟨t⟩ ≅ Z₄` と Klein 群 `V = {1, t², s, s t²} ≅ Z₂ × Z₂` がともに
`D₈` の指数 2 の部分群であり, どちらも `ZMod 4` に regular に作用する。 -/

@[simp] lemma transZFour_pow_four : transZFour ^ 4 = 1 := by decide

@[simp] lemma flipZFour_sq : flipZFour * flipZFour = 1 := by decide

/-- `s t s⁻¹ = t⁻¹` — これで `T = ⟨t⟩` は `⟨t, s⟩` に正規。 -/
lemma flip_mul_trans_mul_flip : flipZFour * transZFour * flipZFour = transZFour⁻¹ := by decide

/-- `t s t⁻¹ = s t²` — これで Klein 群 `V = {1, t², s, s t²}` は `⟨t, s⟩` に正規。 -/
lemma trans_mul_flip_mul_trans_inv :
    transZFour * flipZFour * transZFour⁻¹ = flipZFour * transZFour ^ 2 := by decide

/-- `t²` と `s` は可換 — `V` が Klein 群 (指数 2) であることの要。 -/
lemma trans_sq_commute_flip :
    transZFour ^ 2 * flipZFour = flipZFour * transZFour ^ 2 := by decide

/-- `V` の 4 元はすべて位数 2 以下 (`V ≅ Z₂ × Z₂`)。 -/
lemma klein_sq_eq_one :
    (transZFour ^ 2) ^ 2 = 1 ∧ flipZFour ^ 2 = 1 ∧ (flipZFour * transZFour ^ 2) ^ 2 = 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `t` の位数は 4 — `T ≅ Z₄` は位数 4 の元をもつので `V` (指数 2) と同型でない。 -/
lemma transZFour_sq_ne_one : transZFour ^ 2 ≠ 1 := by decide

end KleinCounterexample

/-! ### Problem 8A.2 — 中心化群は半正則 -/

/-- **Isaacs Problem 8A.2** (p. 235) の核心: `H ≤ G` が `Ω` に推移的なら, `C_G(H)` の元は
1 点を固定するだけで全点を固定する。

`β = h • α` (`h ∈ H`) と書き, `c` が `h` と可換なことから
`c • β = c • h • α = h • c • α = h • α = β`。 -/
theorem smul_eq_self_of_mem_centralizer {H : Subgroup G} [IsPretransitive H Ω]
    {c : G} (hc : c ∈ Subgroup.centralizer (H : Set G)) {α : Ω} (hα : c • α = α) (β : Ω) :
    c • β = β := by
  obtain ⟨h, rfl⟩ := exists_smul_eq H α β
  rw [subgroup_smul_def, ← mul_smul,
    ← Subgroup.mem_centralizer_iff.mp hc (h : G) h.2, mul_smul, hα]

/-- **Isaacs Problem 8A.2** (p. 235), 前半: `H ≤ G` が `Ω` に推移的なら `C_G(H)` は
**半正則** — どの点安定化群とも自明にしか交わらない。

置換群 (= 忠実な作用) であることが要る: `smul_eq_self_of_mem_centralizer` は
「全点を固定する」までしか言わず, そこから `c = 1` を出すのに忠実性を使う。 -/
theorem centralizer_inf_stabilizer_eq_bot [FaithfulSMul G Ω] {H : Subgroup G}
    [IsPretransitive H Ω] (α : Ω) :
    Subgroup.centralizer (H : Set G) ⊓ stabilizer G α = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hc, hα⟩
  rw [Subgroup.mem_bot]
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => ?_
  rw [one_smul]
  exact smul_eq_self_of_mem_centralizer hc (mem_stabilizer_iff.mp hα) β

/-- **Isaacs Problem 8A.2** (p. 235), 後半: **可換な推移的置換群は regular**。

可換なので `G = C_G(G)` が半正則 (前半), 推移性と合わせて軌道写像は全単射。 -/
theorem bijective_smulBase_top_of_comm [FaithfulSMul G Ω] [IsPretransitive G Ω]
    (hcomm : ∀ x y : G, x * y = y * x) (α : Ω) :
    Function.Bijective (smulBase (⊤ : Subgroup G) α) := by
  haveI : IsPretransitive (⊤ : Subgroup G) Ω := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := exists_smul_eq G x y
    exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩
  rw [bijective_smulBase_iff]
  refine ⟨inferInstance, ?_⟩
  have hcentral : (⊤ : Subgroup G) ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) :=
    fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
  refine le_antisymm (le_trans (inf_le_inf_right _ hcentral) ?_) bot_le
  exact le_of_eq (centralizer_inf_stabilizer_eq_bot (H := (⊤ : Subgroup G)) α)

/-! ### Problem 8A.3 — 左右の正則表現 -/

/-- 型の同値 `e : Ω ≃ A` に沿って運んだ **`A` の右正則表現** `A →* Equiv.Perm Ω`,
`a ↦ (x ↦ e.symm (e x * a⁻¹))`。逆元をとるのは反準同型を準同型に直すため。 -/
def regularRepRight {A Ω : Type*} [Group A] (e : Ω ≃ A) : A →* Equiv.Perm Ω where
  toFun a := e.trans ((Equiv.mulRight a⁻¹).trans e.symm)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [mul_assoc]

@[simp] lemma regularRepRight_apply {A Ω : Type*} [Group A] (e : Ω ≃ A) (a : A) (x : Ω) :
    regularRepRight e a x = e.symm (e x * a⁻¹) := rfl

lemma regularRepRight_injective {A Ω : Type*} [Group A] [Nonempty Ω] (e : Ω ≃ A) :
    Function.Injective (regularRepRight e) := by
  intro a b hab
  have := congrArg (fun p : Equiv.Perm Ω => e (p (e.symm 1))) hab
  simpa using this

/-- **右正則表現の像も regular**。 -/
theorem bijective_smulBase_regularRepRight_range {A Ω : Type*} [Group A] [Nonempty Ω]
    (e : Ω ≃ A) (α : Ω) :
    Function.Bijective (smulBase (regularRepRight e).range α) := by
  constructor
  · rintro ⟨-, a, rfl⟩ ⟨-, b, rfl⟩ hnm
    have hab : a = b := by simpa [smulBase] using hnm
    exact Subtype.ext (congrArg (regularRepRight e) hab)
  · intro β
    refine ⟨⟨regularRepRight e ((e β)⁻¹ * e α), ⟨_, rfl⟩⟩, ?_⟩
    simp only [smulBase_apply, Equiv.Perm.smul_def, regularRepRight_apply, mul_inv_rev,
      inv_inv, mul_inv_cancel_left, Equiv.symm_apply_apply]

/-- 左正則表現と右正則表現は可換 (結合律そのもの)。 -/
lemma regularRepRight_range_le_centralizer {A Ω : Type*} [Group A] (e : Ω ≃ A) :
    (regularRepRight e).range ≤
      Subgroup.centralizer (((regularRep e).range : Subgroup (Equiv.Perm Ω)) :
        Set (Equiv.Perm Ω)) := by
  rintro - ⟨b, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro - ⟨a, rfl⟩
  ext x
  simp [mul_assoc]

/-- **Isaacs Problem 8A.3** (p. 235): `Z(G) = 1` なる非自明な群 `G` に対し, ある置換群が
`G` に同型な **相異なる** regular normal 部分群を 2 つもつ。

`Sym(G)` の中の左正則表現の像 `L` と右正則表現の像 `R` を取る。どちらも regular で
`G` に同型, たがいに可換なので `P = L ⊔ R` の中でどちらも正規。`L = R` なら左移動が
すべて右移動になり `G = Z(G) = 1` となって非自明性に反する。 -/
theorem exists_two_distinct_regular_normal_of_center_eq_bot {A : Type*} [Group A]
    [Nontrivial A] (hZ : Subgroup.center A = ⊥) :
    ∃ L R : Subgroup (Equiv.Perm A),
      L ≠ R ∧
      (∀ α : A, Function.Bijective (smulBase L α)) ∧
      (∀ α : A, Function.Bijective (smulBase R α)) ∧
      L ⊔ R ≤ Subgroup.normalizer (L : Set (Equiv.Perm A)) ∧
      L ⊔ R ≤ Subgroup.normalizer (R : Set (Equiv.Perm A)) ∧
      Nonempty (L ≃* A) ∧ Nonempty (R ≃* A) := by
  classical
  refine ⟨(regularRep (Equiv.refl A)).range, (regularRepRight (Equiv.refl A)).range,
    ?_, fun α => bijective_smulBase_regularRep_range _ α,
    fun α => bijective_smulBase_regularRepRight_range _ α, ?_, ?_,
    ⟨(MonoidHom.ofInjective (regularRep_injective (Equiv.refl A))).symm⟩,
    ⟨(MonoidHom.ofInjective (regularRepRight_injective (Equiv.refl A))).symm⟩⟩
  · -- `L = R` なら任意の `a` について左移動 = ある右移動 ⟹ `a ∈ Z(A) = ⊥`
    intro hLR
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hmem : regularRep (Equiv.refl A) a ∈ (regularRepRight (Equiv.refl A)).range := by
      rw [← hLR]; exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    have hb1 := congrArg (fun p : Equiv.Perm A => p 1) hb
    simp only [regularRep_apply, regularRepRight_apply, Equiv.refl_apply,
      Equiv.refl_symm, mul_one, one_mul] at hb1
    refine ha ?_
    have hcentral : a ∈ Subgroup.center A := by
      refine Subgroup.mem_center_iff.mpr fun x => ?_
      have hx := congrArg (fun p : Equiv.Perm A => p x) hb
      simp only [regularRep_apply, regularRepRight_apply, Equiv.refl_apply,
        Equiv.refl_symm] at hx
      rw [hb1] at hx
      exact hx
    rw [hZ, Subgroup.mem_bot] at hcentral
    exact hcentral
  · exact sup_le Subgroup.le_normalizer
      (le_trans (regularRepRight_range_le_centralizer _) (Subgroup.centralizer_le_normalizer _))
  · refine sup_le (le_trans ?_ (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact ((Subgroup.mem_centralizer_iff.mp
      (regularRepRight_range_le_centralizer (Equiv.refl A) hy) x hx)).symm

/-! ### Problem 8A.4 — 交わらない 2 つの regular normal 部分群 -/

section RegularPair

variable {U V : Subgroup G}

/-- 交わらない正規部分群は元ごとに可換なので `V ≤ C_G(U)` (8A.4 の step 1)。 -/
lemma le_centralizer_of_normal_of_inf_eq_bot [U.Normal] [V.Normal] (h : U ⊓ V = ⊥) :
    V ≤ Subgroup.centralizer (U : Set G) := fun v hv =>
  Subgroup.mem_centralizer_iff.mpr fun u hu =>
    Subgroup.commute_of_normal_of_disjoint U V inferInstance inferInstance
      (disjoint_iff.mpr h) u v hu hv

/-- **8A.4 の step 2**: `U`, `V` がともに regular normal で `U ⊓ V = ⊥` なら `C_G(U) = V`。

`⊇` は step 1。`⊆` は `V` の推移性で `c • α = v • α` なる `v ∈ V` を取り, `v⁻¹c` が
`C_G(U)` に属して `α` を固定することと `C_G(U)` の半正則性 (8A.2) から `v⁻¹c = 1`。 -/
theorem centralizer_eq_of_regular_of_inf_eq_bot [FaithfulSMul G Ω] [U.Normal] [V.Normal]
    {α : Ω} (hU : Function.Bijective (smulBase U α)) (hV : Function.Bijective (smulBase V α))
    (h : U ⊓ V = ⊥) :
    Subgroup.centralizer (U : Set G) = V := by
  haveI : IsPretransitive U Ω := (surjective_smulBase_iff U α).mp hU.2
  haveI : IsPretransitive V Ω := (surjective_smulBase_iff V α).mp hV.2
  refine le_antisymm (fun c hc => ?_) (le_centralizer_of_normal_of_inf_eq_bot h)
  obtain ⟨v, hv⟩ := exists_smul_eq V α (c • α)
  rw [subgroup_smul_def] at hv
  have hstab : ((v : G)⁻¹ * c) ∈ stabilizer G α := by
    rw [mem_stabilizer_iff, mul_smul, ← hv, inv_smul_smul]
  have hmem : ((v : G)⁻¹ * c) ∈ Subgroup.centralizer (U : Set G) ⊓ stabilizer G α :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _
      (le_centralizer_of_normal_of_inf_eq_bot h v.2)) hc, hstab⟩
  rw [centralizer_inf_stabilizer_eq_bot (H := U) α, Subgroup.mem_bot,
    inv_mul_eq_one] at hmem
  exact hmem ▸ v.2

/-- **8A.4 の後半**: そのような `U` の中心は自明。

`z ∈ Z(U)` は `U` を中心化するので `z ∈ C_G(U) = V`, かつ `z ∈ U` なので `z ∈ U ⊓ V = ⊥`。 -/
theorem center_eq_bot_of_regular_of_inf_eq_bot [FaithfulSMul G Ω] [U.Normal] [V.Normal]
    {α : Ω} (hU : Function.Bijective (smulBase U α)) (hV : Function.Bijective (smulBase V α))
    (h : U ⊓ V = ⊥) :
    Subgroup.center ↥U = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzV : (z : G) ∈ V := by
    rw [← centralizer_eq_of_regular_of_inf_eq_bot hU hV h]
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨u, hu⟩)
  have : (z : G) ∈ U ⊓ V := ⟨z.2, hzV⟩
  rw [h, Subgroup.mem_bot] at this
  exact Subtype.ext this

/-- **8A.4 の step 4** (準同型): `u ↦ (u⁻¹ • α を実現する唯一の `V` の元)`。

`V` の元は `U` の元と可換なので (`step 1`) これは準同型になる:
`ψ(u₁)ψ(u₂) • α = ψ(u₁) • (u₂⁻¹ • α) = u₂⁻¹ • (u₁⁻¹ • α) = (u₁u₂)⁻¹ • α`。 -/
noncomputable def regularPairHom [U.Normal] [V.Normal] {α : Ω}
    (hV : Function.Bijective (smulBase V α)) (h : U ⊓ V = ⊥) : ↥U →* ↥V where
  toFun u := preSmulBase hV ((u : G)⁻¹ • α)
  map_one' := by rw [preSmulBase_eq_iff]; simp
  map_mul' u₁ u₂ := by
    rw [preSmulBase_eq_iff, Subgroup.coe_mul, mul_smul,
      smulBase_preSmulBase hV ((u₂ : G)⁻¹ • α)]
    have hcomm := (Subgroup.mem_centralizer_iff.mp
      (le_centralizer_of_normal_of_inf_eq_bot (U := U) h
        (preSmulBase hV ((u₁ : G)⁻¹ • α)).2) ((u₂ : G)⁻¹) (Subgroup.inv_mem _ u₂.2)).symm
    rw [← mul_smul, hcomm, mul_smul, smulBase_preSmulBase hV ((u₁ : G)⁻¹ • α),
      ← mul_smul, Subgroup.coe_mul, mul_inv_rev]

@[simp] lemma regularPairHom_apply [U.Normal] [V.Normal] {α : Ω}
    (hV : Function.Bijective (smulBase V α)) (h : U ⊓ V = ⊥) (u : ↥U) :
    regularPairHom hV h u = preSmulBase hV ((u : G)⁻¹ • α) := rfl

/-- **Isaacs Problem 8A.4** (p. 235): 置換群 `G` の regular normal 部分群 `U`, `V` が
`U ⊓ V = 1` を満たすなら `U ≅ V` で, どちらも中心が自明。 -/
theorem mulEquiv_and_center_eq_bot_of_regular_normal [FaithfulSMul G Ω]
    [U.Normal] [V.Normal] {α : Ω}
    (hU : Function.Bijective (smulBase U α)) (hV : Function.Bijective (smulBase V α))
    (h : U ⊓ V = ⊥) :
    Nonempty (↥U ≃* ↥V) ∧ Subgroup.center ↥U = ⊥ ∧ Subgroup.center ↥V = ⊥ := by
  refine ⟨⟨MulEquiv.ofBijective (regularPairHom hV h) ⟨?_, ?_⟩⟩,
    center_eq_bot_of_regular_of_inf_eq_bot hU hV h,
    center_eq_bot_of_regular_of_inf_eq_bot hV hU (by rwa [inf_comm])⟩
  · intro u₁ u₂ huu
    have h1 := smulBase_preSmulBase hV ((u₁ : G)⁻¹ • α)
    have h2 := smulBase_preSmulBase hV ((u₂ : G)⁻¹ • α)
    rw [show preSmulBase hV ((u₁ : G)⁻¹ • α) = preSmulBase hV ((u₂ : G)⁻¹ • α) from huu,
      h2] at h1
    have : smulBase U α u₁⁻¹ = smulBase U α u₂⁻¹ := by
      simpa [smulBase] using h1.symm
    simpa using congrArg (fun x : ↥U => x⁻¹) (hU.1 this)
  · intro v
    refine ⟨(preSmulBase hU ((v : G) • α))⁻¹, ?_⟩
    rw [regularPairHom_apply, preSmulBase_eq_iff]
    simp

end RegularPair

/-! ### Problem 8A.5 — 点安定化群の固定点集合 -/

/-- 有限群では `H ≤ K` と位数の一致から `H = K`。 -/
private theorem eq_of_le_of_card_eq [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    (hcard : Nat.card ↥K = Nat.card ↥H) : H = K := by
  refine le_antisymm hle (Subgroup.subgroupOf_eq_top.mp (Subgroup.eq_top_of_card_eq _ ?_))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]

/-- `Δ = Fix(H)` は `N_G(H)` で保たれる: `h • (n • β) = n • ((n⁻¹hn) • β) = n • β`。 -/
theorem smul_mem_fixedPoints_of_mem_normalizer {H : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) {β : Ω}
    (hβ : β ∈ MulAction.fixedPoints ↥H Ω) : n • β ∈ MulAction.fixedPoints ↥H Ω := by
  intro h
  have hmem : n⁻¹ * (h : G) * n ∈ H := (Subgroup.mem_normalizer_iff''.mp hn (h : G)).mp h.2
  have := hβ ⟨n⁻¹ * (h : G) * n, hmem⟩
  rw [subgroup_smul_def] at this
  calc (h : G) • (n • β) = (n * (n⁻¹ * (h : G) * n)) • β := by rw [← mul_smul]; group
    _ = n • ((n⁻¹ * (h : G) * n) • β) := mul_smul _ _ _
    _ = n • β := by rw [this]

/-- **Isaacs Problem 8A.5** (p. 235) の主内容: `G` が `Ω` に推移的で `H = G_α` のとき,
`N_G(H)` は `Δ = Fix(H)` に**推移的**に作用する。

`β ∈ Δ` は `H ≤ G_β` を意味する。`G` の推移性で `β = g • α` と書くと
`G_β = gHg⁻¹` なので `H ≤ gHg⁻¹`, 有限性から `H = gHg⁻¹`, すなわち `g ∈ N_G(H)`。 -/
theorem exists_mem_normalizer_stabilizer_smul_eq [Finite G] [IsPretransitive G Ω] {α β : Ω}
    (hβ : β ∈ MulAction.fixedPoints ↥(stabilizer G α) Ω) :
    ∃ n ∈ Subgroup.normalizer ((stabilizer G α : Subgroup G) : Set G), n • α = β := by
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  refine ⟨g, ?_, hg⟩
  have hle : stabilizer G α ≤ (stabilizer G α).map (MulAut.conj g).toMonoidHom := by
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hg]
    exact fun h hh => hβ ⟨h, hh⟩
  have hcard : Nat.card ↥((stabilizer G α).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥(stabilizer G α) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq := eq_of_le_of_card_eq hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [heq] at hh
    obtain ⟨y, hy, hyeq⟩ := hh
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hyeq
    exact (mul_left_cancel (mul_right_cancel hyeq)) ▸ hy

/-- **Isaacs Problem 8A.5** の退化部分: `G` が 2-transitive (= `G_α` が `Ω ∖ {α}` に推移的)
で `Δ = Fix(G_α)` が `α` 以外の点 `β` をもつなら, `Ω` は 2 点しかもたない。

したがって `r = min(k, |Δ|)` は `k ≥ 2` かつ `|Δ| ≥ 2` のとき `Ω` が 2 点集合の場合に限られ,
そこでは `N_G(H) = G` が `Δ = Ω` に `k`-transitive に作用する。一般には `|Δ| ≥ 3` なら
`k ≤ 1` で `r = 1`, すなわち上の推移性が主張のすべて。 -/
theorem eq_of_mem_fixedPoints_stabilizer_of_transitive_on_compl {α β : Ω}
    (hβ : β ∈ MulAction.fixedPoints ↥(stabilizer G α) Ω)
    (htwo : ∀ γ : Ω, γ ≠ α → ∃ h : ↥(stabilizer G α), h • β = γ) :
    ∀ γ : Ω, γ ≠ α → γ = β := by
  intro γ hγ
  obtain ⟨h, hh⟩ := htwo γ hγ
  exact (hh ▸ hβ h).symm ▸ rfl

/-! ### Problem 8A.6 — Sylow 版 -/

/-- 共役で部分群が保たれれば正規化群の元。 -/
private theorem mem_normalizer_of_map_conj_eq {Q : Subgroup G} {n : G}
    (h : Q.map (MulAut.conj n).toMonoidHom = Q) : n ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    rw [← h]
    exact ⟨q, hq, rfl⟩
  · intro hq
    rw [← h] at hq
    obtain ⟨y, hy, hyeq⟩ := hq
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hyeq
    exact (mul_left_cancel (mul_right_cancel hyeq)) ▸ hy

/-- `Q ≤ K` のとき `Nat.card Q * [K : Q] = Nat.card K`。 -/
private theorem card_mul_relIndex [Finite G] {Q K : Subgroup G} (h : Q ≤ K) :
    Nat.card ↥Q * Q.relIndex K = Nat.card ↥K := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.card_mul_index (Q.subgroupOf K)

/-- `Q ≤ K` のとき `↥K` の中で見た `Q` も `p`-群。 -/
private theorem isPGroup_subgroupOf {p : ℕ} {Q K : Subgroup G} (hQK : Q ≤ K)
    (hp : IsPGroup p ↥Q) : IsPGroup p ↥(Q.subgroupOf K) :=
  hp.of_injective (Subgroup.subgroupOfEquivOfLe hQK).toMonoidHom (MulEquiv.injective _)

/-- **部分群 `K` の中の 2 つの `p`-Sylow は `K` の元で共役** (ambient `Subgroup G` の言葉)。

`Sylow p ↥K` へ持ち上げて mathlib の共役性 (`MulAction.exists_smul_eq`) を使い,
`K.subtype` で押し出して戻す。 -/
theorem exists_mem_conj_eq_of_sylow_le [Finite G] {p : ℕ} [Fact p.Prime]
    {K Q₁ Q₂ : Subgroup G} (h₁ : Q₁ ≤ K) (h₂ : Q₂ ≤ K)
    (hp₁ : IsPGroup p ↥Q₁) (hp₂ : IsPGroup p ↥Q₂)
    (hi₁ : ¬ p ∣ Q₁.relIndex K) (hi₂ : ¬ p ∣ Q₂.relIndex K) :
    ∃ x ∈ K, Q₁.map (MulAut.conj x).toMonoidHom = Q₂ := by
  classical
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (↥K)
    ((isPGroup_subgroupOf h₁ hp₁).toSylow hi₁) ((isPGroup_subgroupOf h₂ hp₂).toSylow hi₂)
  have hcoe : (Q₁.subgroupOf K).map (MulAut.conj x).toMonoidHom = Q₂.subgroupOf K := by
    have h0 := congrArg (fun S : Sylow p ↥K => (S : Subgroup ↥K)) hx
    simp only [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h0
    exact h0
  have hcomp : K.subtype.comp (MulAut.conj x).toMonoidHom
      = (MulAut.conj (x : G)).toMonoidHom.comp K.subtype := by
    ext y; simp
  refine ⟨(x : G), x.2, ?_⟩
  calc Q₁.map (MulAut.conj (x : G)).toMonoidHom
      = ((Q₁.subgroupOf K).map K.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le h₁]
    _ = (Q₁.subgroupOf K).map (K.subtype.comp (MulAut.conj x).toMonoidHom) := by
        rw [Subgroup.map_map, hcomp]
    _ = ((Q₁.subgroupOf K).map (MulAut.conj x).toMonoidHom).map K.subtype := by
        rw [Subgroup.map_map]
    _ = Q₂ := by rw [hcoe, Subgroup.map_subgroupOf_eq_of_le h₂]

/-- **Isaacs Problem 8A.6** (p. 235): `G` が `Ω` に推移的で `H = G_α`, `Q ∈ Syl_p(H)` のとき,
`N_G(Q)` は `Δ = Fix(Q)` に推移的に作用する。

`β = g • α` と書くと `G_β = gHg⁻¹` で, `Q` と `gQg⁻¹` はともに `G_β` の `p`-Sylow。
`G_β` の元 `x` で `xQx⁻¹ = gQg⁻¹` を取ると `n := x⁻¹g` が `Q` を正規化し,
`n • α = x⁻¹ • β = β`。 -/
theorem exists_mem_normalizer_sylow_smul_eq [Finite G] [IsPretransitive G Ω] {p : ℕ}
    [Fact p.Prime] {α β : Ω} {Q : Subgroup G} (hQH : Q ≤ stabilizer G α)
    (hp : IsPGroup p ↥Q) (hi : ¬ p ∣ Q.relIndex (stabilizer G α))
    (hβ : β ∈ MulAction.fixedPoints ↥Q Ω) :
    ∃ n ∈ Subgroup.normalizer (Q : Set G), n • α = β := by
  classical
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  have hKeq : stabilizer G β = (stabilizer G α).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hQK : Q ≤ stabilizer G β := fun q hq => hβ ⟨q, hq⟩
  have hQ'K : Q.map (MulAut.conj g).toMonoidHom ≤ stabilizer G β := by
    rw [hKeq]; exact Subgroup.map_mono hQH
  have hcardQ' : Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) = Nat.card ↥Q :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardK : Nat.card ↥(stabilizer G β) = Nat.card ↥(stabilizer G α) := by
    rw [hKeq]; exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hrel : Q.relIndex (stabilizer G β) = Q.relIndex (stabilizer G α) :=
    Nat.eq_of_mul_eq_mul_left hpos
      ((card_mul_relIndex hQK).trans (hcardK.trans (card_mul_relIndex hQH).symm))
  have hrel' : (Q.map (MulAut.conj g).toMonoidHom).relIndex (stabilizer G β)
      = Q.relIndex (stabilizer G α) := by
    refine Nat.eq_of_mul_eq_mul_left
      (show 0 < Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) from Nat.card_pos) ?_
    rw [card_mul_relIndex hQ'K, hcardQ', card_mul_relIndex hQH]
    exact hcardK
  have hpQ' : IsPGroup p ↥(Q.map (MulAut.conj g).toMonoidHom) :=
    hp.of_injective
      (Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.toMonoidHom (MulEquiv.injective _)
  obtain ⟨x, hxK, hxeq⟩ := exists_mem_conj_eq_of_sylow_le hQK hQ'K hp hpQ'
    (by rw [hrel]; exact hi) (by rw [hrel']; exact hi)
  have hsplit : ∀ a b : G, (MulAut.conj (a * b)).toMonoidHom
      = (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
    intro a b; ext y; simp [mul_assoc]
  refine ⟨x⁻¹ * g, mem_normalizer_of_map_conj_eq ?_, ?_⟩
  · rw [hsplit, ← Subgroup.map_map, ← hxeq, Subgroup.map_map, ← hsplit]
    simp only [inv_mul_cancel, map_one]
    ext y
    simp
  · rw [mul_smul, hg, inv_smul_eq_iff]
    exact (mem_stabilizer_iff.mp hxK).symm

/-! ### Problem 8A.7 — 可換群の half-transitive 作用は Frobenius -/

section AbelianHalfTransitive

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

/-- 可換な `A` が作用するとき, 一つの元 `a` の固定部分群は `A`-不変。 -/
theorem smul_mem_fixedBy_of_comm (hcomm : ∀ x y : A, x * y = y * x) (a b : A) {n : N}
    (hn : a • n = n) : a • (b • n) = b • n := by
  rw [smul_smul, hcomm, ← smul_smul, hn]

/-- **Isaacs Problem 8A.7** (p. 235), 前半: **可換群 `A` が `N` に忠実に作用し, 非単位元上の
作用が half-transitive なら, その作用は Frobenius**。

Thm 8.9 (`isFrobeniusAction_or_isElementaryAbelian_of_half_transitive`) の例外肢を
可換性で潰す: `a ≠ 1` が `n ≠ 1` を固定するなら, `a` の固定部分群 `Fix(a)` は
(`A` が可換なので) `A`-不変で `⊥` でない。例外肢は「`⊥` 以外の真の `A`-不変部分群は無い」
と言うので `Fix(a) = ⊤`, すなわち `a` は自明に作用し忠実性に反する。 -/
theorem isFrobeniusAction_of_comm_of_half_transitive [Finite A] [Finite N] [FaithfulSMul A N]
    (hcomm : ∀ x y : A, x * y = y * x)
    (hhalf : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      Nat.card (MulAction.orbit A x) = Nat.card (MulAction.orbit A y)) :
    Ch06.IsFrobeniusAction A N := by
  rcases isFrobeniusAction_or_isElementaryAbelian_of_half_transitive A N hhalf with h | ⟨-, hirr⟩
  · exact h
  intro a ha n hn hfix
  -- `Fix(a)` は `A`-不変な非自明部分群
  let F : Subgroup N :=
    { carrier := {x : N | a • x = x}
      one_mem' := smul_one a
      mul_mem' := fun {u v} hu hv => by
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        rw [smul_mul', hu, hv]
      inv_mem' := fun {u} hu => by
        simp only [Set.mem_setOf_eq] at hu ⊢
        rw [smul_inv', hu] }
  have hFinv : ∀ b : A, ∀ x ∈ F, b • x ∈ F := fun b x hx =>
    smul_mem_fixedBy_of_comm hcomm a b hx
  have hFtop : F = ⊤ := by
    by_contra hne
    have := hirr F hne hFinv
    have hnF : n ∈ F := hfix
    rw [this, Subgroup.mem_bot] at hnF
    exact hn hnF
  refine ha (FaithfulSMul.eq_of_smul_eq_smul (α := N) fun x => ?_)
  have : x ∈ F := hFtop ▸ Subgroup.mem_top x
  rw [one_smul]
  exact this

/-- **Isaacs Problem 8A.7** (p. 235): 可換群 `A` が非自明な `N` に忠実に作用し, 非単位元上の
作用が half-transitive なら, その作用は Frobenius で **`A` は巡回群**。

`A` が巡回であることは前半 (Frobenius) と Isaacs Cor 6.17 の可換分岐
(`Ch06.isCyclic_of_frobeniusAction_of_isMulCommutative`, 可換な Frobenius 補群は巡回) から。 -/
theorem isFrobeniusAction_and_isCyclic_of_comm_of_half_transitive [Finite A] [Finite N]
    [Nontrivial N] [FaithfulSMul A N] [IsMulCommutative A]
    (hhalf : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      Nat.card (MulAction.orbit A x) = Nat.card (MulAction.orbit A y)) :
    Ch06.IsFrobeniusAction A N ∧ IsCyclic A := by
  have hfrob := isFrobeniusAction_of_comm_of_half_transitive
    (fun x y => (IsMulCommutative.is_comm (M := A)).comm x y) hhalf
  exact ⟨hfrob, Ch06.isCyclic_of_frobeniusAction_of_isMulCommutative hfrob⟩

end AbelianHalfTransitive

/-! ### Problem 8A.8 — 正規部分群の軌道は推移的に置換される -/

/-- **Isaacs Problem 8A.8** (p. 235): `N ⊴ G` のとき `g` は `N`-軌道を `N`-軌道へ写す:
`g • orbit N α = orbit N (g • α)`。

`N` が正規なので `g * n = (g n g⁻¹) * g` と書き換えられる。 -/
theorem smul_orbit_eq_orbit_smul {N : Subgroup G} [N.Normal] (g : G) (α : Ω) :
    g • orbit N α = orbit N (g • α) := by
  ext x
  constructor
  · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
    refine ⟨⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⟩, ?_⟩
    simp only [subgroup_smul_def, ← mul_smul]
    group
  · rintro ⟨n, rfl⟩
    refine ⟨(g⁻¹ * (n : G) * g) • α, ⟨⟨g⁻¹ * (n : G) * g, ?_⟩, rfl⟩, ?_⟩
    · simpa using Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⁻¹
    · simp only [subgroup_smul_def, ← mul_smul]
      group

/-- **Isaacs Problem 8A.8** (p. 235) の帰結: `G` が推移的で `N ⊴ G` なら `N` は
**half-transitive** — すべての `N`-軌道が同じ濃度をもつ。

`G` の推移性で `β = g • α` と書き, `g • orbit N α = orbit N β` が全単射を与える。 -/
theorem card_orbit_eq_of_normal [IsPretransitive G Ω] {N : Subgroup G} [N.Normal] (α β : Ω) :
    Nat.card (orbit N α) = Nat.card (orbit N β) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  rw [← smul_orbit_eq_orbit_smul g α]
  exact Nat.card_congr ((Equiv.Set.image (fun x : Ω => g • x) (orbit N α)
    (MulAction.injective g)).trans (Equiv.setCongr Set.image_smul))

/-! ### Problem 8A.9 — 2-transitive 群の非自明な正規部分群は推移的 -/

/-- **Isaacs Problem 8A.9** (p. 236): `G` が `Ω` に 2-transitive で `N ⊴ G` が非自明に
作用するなら, `N` は推移的。

2-transitivity は「推移的 (`IsPretransitive G Ω`) かつ各点安定化群 `G_α` が `Ω ∖ {α}` に
推移的」の形で仮定する (`h2`)。

`N ⊴ G` なので `g • orbit N α = orbit N (g • α)` (8A.8)。非自明性から `orbit N α` には
`α` 以外の点 `γ` があり, `G_α` の推移性で任意の `β ≠ α` を `γ` から得る `g` を取れば
`β = g • γ ∈ g • orbit N α = orbit N α`。 -/
theorem isPretransitive_of_normal_of_two_transitive [IsPretransitive G Ω]
    (h2 : ∀ α β γ : Ω, β ≠ α → γ ≠ α → ∃ g : G, g • α = α ∧ g • β = γ)
    {N : Subgroup G} [N.Normal] {x : Ω} {n : ↥N} (hn : (n : G) • x ≠ x) :
    IsPretransitive N Ω := by
  refine ⟨fun a b => ?_⟩
  -- `orbit N a` には `a` 以外の点 `γ` がある
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G x a
  have horb : g₀ • orbit N x = orbit N a := by rw [smul_orbit_eq_orbit_smul, hg₀]
  have hγmem : g₀ • ((n : G) • x) ∈ orbit N a := by
    rw [← horb]
    exact ⟨(n : G) • x, ⟨n, rfl⟩, rfl⟩
  have hγne : g₀ • ((n : G) • x) ≠ a := by
    rw [← hg₀]
    exact fun hc => hn (MulAction.injective g₀ hc)
  -- `b = a` なら自明, そうでなければ `G_a` の推移性で移す
  rcases eq_or_ne b a with rfl | hba
  · exact ⟨1, one_smul _ _⟩
  obtain ⟨g, hga, hgγ⟩ := h2 a (g₀ • ((n : G) • x)) b hγne hba
  have : b ∈ orbit N a := by
    rw [← hgγ, ← hga, ← smul_orbit_eq_orbit_smul]
    exact ⟨_, hγmem, rfl⟩
  obtain ⟨m, hm⟩ := this
  exact ⟨m, hm⟩

/-! ### Problem 8A.10 — 可解 4-transitive 群 -/

/-- **8A.10 の核心**: 群 `N` に自己同型として作用する `A` が非単位元の集合 `N ∖ {1}` に
**3-transitive** なら `|N| ≤ 4`。

自己同型は積を保つので, `x`, `y` を固定する元は `xy` も固定する。`|N| ≥ 5` なら
`1, x, y, xy` と異なる `w` が取れ, 3-transitivity で `(x, y, xy) ↦ (x, y, w)` を実現する
自己同型があるはずだが, それは `xy ↦ xy ≠ w` を強いる — 矛盾。

`N` が elementary abelian であることは不要 (積を保つことだけを使う)。 -/
theorem card_le_four_of_three_transitive_on_nonidentity
    {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    (h3 : ∀ x y z x' y' z' : N, x ≠ 1 → y ≠ 1 → z ≠ 1 → x' ≠ 1 → y' ≠ 1 → z' ≠ 1 →
      x ≠ y → x ≠ z → y ≠ z → x' ≠ y' → x' ≠ z' → y' ≠ z' →
      ∃ a : A, a • x = x' ∧ a • y = y' ∧ a • z = z') :
    Nat.card N ≤ 4 := by
  classical
  by_contra hcard
  have h5 : 5 ≤ Nat.card N := Nat.lt_of_not_le hcard
  haveI : Finite N := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite N
  -- 濃度が `Nat.card N` 未満の `Finset` の外に元が取れる
  have hout : ∀ s : Finset N, s.card < Nat.card N → ∃ z : N, z ∉ s := by
    intro s hs
    by_contra hc
    rw [Finset.eq_univ_iff_forall.mpr (not_exists_not.mp hc), Finset.card_univ,
      ← Nat.card_eq_fintype_card] at hs
    exact lt_irrefl _ hs
  -- `x ≠ 1`
  obtain ⟨x, hx⟩ := hout {1} (by simp only [Finset.card_singleton]; omega)
  simp only [Finset.mem_singleton] at hx
  -- `y ∉ {1, x, x⁻¹}` — これで `x * y ∉ {1, x, y}`
  obtain ⟨y, hy⟩ := hout {1, x, x⁻¹} (lt_of_le_of_lt (Finset.card_insert_le _ _) (by
    refine lt_of_le_of_lt (Nat.succ_le_succ (Finset.card_insert_le _ _)) ?_
    simp only [Finset.card_singleton]
    omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy1, hyx, hyxinv⟩ := hy
  have hxy1 : x * y ≠ 1 := fun hc => hyxinv (inv_eq_of_mul_eq_one_right hc).symm
  have hxyx : x * y ≠ x := fun hc => hy1 (by simpa using congrArg (x⁻¹ * ·) hc)
  have hxyy : x * y ≠ y := fun hc => hx (by simpa using congrArg (· * y⁻¹) hc)
  -- `w ∉ {1, x, y, x * y}`
  obtain ⟨w, hw⟩ := hout {1, x, y, x * y} (by
    refine lt_of_le_of_lt (Finset.card_insert_le _ _) ?_
    refine lt_of_le_of_lt (Nat.succ_le_succ (Finset.card_insert_le _ _)) ?_
    refine lt_of_le_of_lt (Nat.succ_le_succ (Nat.succ_le_succ (Finset.card_insert_le _ _))) ?_
    simp only [Finset.card_singleton]
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨hw1, hwx, hwy, hwxy⟩ := hw
  -- 3-transitivity: `(x, y, x*y) ↦ (x, y, w)`
  obtain ⟨a, hax, hay, haxy⟩ := h3 x y (x * y) x y w hx hy1 hxy1 hx hy1 hw1
    (Ne.symm hyx) (Ne.symm hxyx) (Ne.symm hxyy) (Ne.symm hyx) (Ne.symm hwx) (Ne.symm hwy)
  exact hwxy (by rw [← haxy, smul_mul', hax, hay])

/-- **8A.10 の step 5**: `N` が regular normal で点安定化群 `G_α` が `Ω ∖ {α}` に
3-transitive なら, `|N| ≤ 4`。

Thm 8.5 の第 3 主張 (共役作用と点作用の置換同型) を軌道写像 `n ↦ n • α` で直接使う:
`g • α = α` のとき `(g n g⁻¹) • α = g • (n • α)` なので, `Ω ∖ {α}` 上の 3-transitivity は
`N ∖ {1}` 上の**自己同型による** 3-transitivity に翻訳され,
`card_le_four_of_three_transitive_on_nonidentity` が使える。 -/
theorem card_le_four_of_regular_normal_of_stabilizer_three_transitive
    {N : Subgroup G} [N.Normal] {α : Ω} (hreg : Function.Bijective (smulBase N α))
    (h3 : ∀ β₁ β₂ β₃ γ₁ γ₂ γ₃ : Ω, β₁ ≠ α → β₂ ≠ α → β₃ ≠ α → γ₁ ≠ α → γ₂ ≠ α → γ₃ ≠ α →
      β₁ ≠ β₂ → β₁ ≠ β₃ → β₂ ≠ β₃ → γ₁ ≠ γ₂ → γ₁ ≠ γ₃ → γ₂ ≠ γ₃ →
      ∃ g : G, g • α = α ∧ g • β₁ = γ₁ ∧ g • β₂ = γ₂ ∧ g • β₃ = γ₃) :
    Nat.card ↥N ≤ 4 := by
  refine card_le_four_of_three_transitive_on_nonidentity (A := MulAut ↥N) ?_
  intro x y z x' y' z' hx hy hz hx' hy' hz' hxy hxz hyz hxy' hxz' hyz'
  -- 非単位元は `α` と異なる点へ, 相異なる元は相異なる点へ移る
  have hne : ∀ n : ↥N, n ≠ 1 → (n : G) • α ≠ α := fun n hn hc =>
    hn (hreg.1 (show smulBase N α n = smulBase N α 1 by simpa [smulBase] using hc))
  have hinj : ∀ m n : ↥N, (m : G) • α = (n : G) • α → m = n := fun m n hc =>
    hreg.1 (by simpa [smulBase] using hc)
  obtain ⟨g, hgα, hg1, hg2, hg3⟩ :=
    h3 ((x : G) • α) ((y : G) • α) ((z : G) • α) ((x' : G) • α) ((y' : G) • α) ((z' : G) • α)
      (hne x hx) (hne y hy) (hne z hz) (hne x' hx') (hne y' hy') (hne z' hz')
      (fun hc => hxy (hinj _ _ hc)) (fun hc => hxz (hinj _ _ hc)) (fun hc => hyz (hinj _ _ hc))
      (fun hc => hxy' (hinj _ _ hc)) (fun hc => hxz' (hinj _ _ hc)) (fun hc => hyz' (hinj _ _ hc))
  -- `g` による共役が求める自己同型
  have hginv : g⁻¹ • α = α := by rw [inv_smul_eq_iff, hgα]
  have key : ∀ (n n' : ↥N), g • ((n : G) • α) = (n' : G) • α →
      (MulAut.conjNormal (H := N) g) • n = n' := by
    intro n n' hc
    refine hinj _ _ ?_
    rw [MulAut.smul_def, MulAut.conjNormal_apply]
    calc (g * (n : G) * g⁻¹) • α = g • ((n : G) • (g⁻¹ • α)) := by
          simp only [← mul_smul, mul_assoc]
      _ = (n' : G) • α := by rw [hginv, hc]
  exact ⟨MulAut.conjNormal (H := N) g, key x x' hg1, key y y' hg2, key z z' hg3⟩

/-- **Isaacs Problem 8A.10** (p. 236) の主内容: **可解な 4-transitive 置換群の次数は 4**。

書籍 hint どおり極小正規部分群 `N` を取る。`N` は忠実性から非自明に作用するので **8A.9**
で推移的, `G` 可解ゆえ **Isaacs Thm 3.11** で可換 (実は elementary abelian), 可換 + 推移的
+ 忠実で **8A.2** より `C_G(N) ⊓ G_α = ⊥`, `N ≤ C_G(N)` だから `N` は **regular**。
`G_α` は `Ω ∖ {α}` に 3-transitive なので
`card_le_four_of_regular_normal_of_stabilizer_three_transitive` で `|N| ≤ 4`,
regular ゆえ `|Ω| = |N| ≤ 4`。

4-transitivity は「推移的 + `G_α` が `Ω ∖ {α}` に 3-transitive」の形で仮定する
(`h2` は 2-transitivity 部分, `h3` は 3-transitivity 部分)。 -/
theorem card_eq_four_of_solvable_of_stabilizer_three_transitive [Finite G] [IsSolvable G]
    [FaithfulSMul G Ω] [IsPretransitive G Ω] {α : Ω} (hΩ4 : 4 ≤ Nat.card Ω)
    (h2 : ∀ α' β γ : Ω, β ≠ α' → γ ≠ α' → ∃ g : G, g • α' = α' ∧ g • β = γ)
    (h3 : ∀ β₁ β₂ β₃ γ₁ γ₂ γ₃ : Ω, β₁ ≠ α → β₂ ≠ α → β₃ ≠ α → γ₁ ≠ α → γ₂ ≠ α → γ₃ ≠ α →
      β₁ ≠ β₂ → β₁ ≠ β₃ → β₂ ≠ β₃ → γ₁ ≠ γ₂ → γ₁ ≠ γ₃ → γ₂ ≠ γ₃ →
      ∃ g : G, g • α = α ∧ g • β₁ = γ₁ ∧ g • β₂ = γ₂ ∧ g • β₃ = γ₃) :
    Nat.card Ω = 4 := by
  classical
  -- `Ω` は 2 点以上, したがって `G` は非自明
  haveI hΩfin : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  haveI hΩnt : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨β, hβ⟩ := exists_ne α
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G α β
  haveI hGnt : Nontrivial G := ⟨g₀, 1, fun hc => hβ (by rw [← hg₀, hc, one_smul])⟩
  -- 極小正規部分群 `N`
  obtain ⟨N, hNmin, -⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  haveI hNnormal : N.Normal := hNmin.1
  haveI hNnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNmin.2.1
  -- `N` は非自明に作用する (忠実性)
  obtain ⟨n, hn1⟩ := exists_ne (1 : ↥N)
  have hnact : ∃ x : Ω, (n : G) • x ≠ x := by
    by_contra hc
    exact hn1 (Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
      fun x => by rw [OneMemClass.coe_one, one_smul]; exact not_exists_not.mp hc x))
  obtain ⟨x, hx⟩ := hnact
  -- 8A.9: `N` は推移的
  haveI hNtrans : IsPretransitive ↥N Ω := isPretransitive_of_normal_of_two_transitive h2 hx
  -- Thm 3.11: `N` は可換
  have habel := OddOrder.Isaacs.Ch03.solvable_minimal_normal_isAbelian hNmin
  have hNcent : N ≤ Subgroup.centralizer (N : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => habel b hb a ha
  -- 8A.2: `N` は regular
  have hbot : N ⊓ stabilizer G α = ⊥ :=
    le_antisymm (le_trans (inf_le_inf_right _ hNcent)
      (le_of_eq (centralizer_inf_stabilizer_eq_bot (H := N) α))) bot_le
  have hbij : Function.Bijective (smulBase N α) :=
    (bijective_smulBase_iff N α).mpr ⟨hNtrans, hbot⟩
  -- 核心補題で `|N| ≤ 4`, regular ゆえ `|Ω| = |N|`
  have hcardN := card_le_four_of_regular_normal_of_stabilizer_three_transitive hbij h3
  have hcardΩ : Nat.card Ω = Nat.card ↥N :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  omega

/-- 型の同値 `e : α ≃ β` に沿った対称群の同型 (mathlib の `Equiv.permCongr` の乗法版)。 -/
def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toFun p := (e.symm.trans p).trans e
  invFun q := (e.trans q).trans e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_mul' _ _ := by ext; simp

/-- **Isaacs Problem 8A.10** (p. 236) 🎉: **可解な 4-transitive 置換群は `S₄` に同型**。

次数が 4 であること (`card_eq_four_of_solvable_of_stabilizer_three_transitive`) を認めれば,
`MulAction.toPermHom` が単射 (忠実) かつ全射 (4 点の任意の並べ替えは 4-transitivity で
実現できる) なので `G ≃* Sym(Ω) ≃* S₄`。

4-transitivity は「単射な 4-tuple どうしを移す元がある」形 (`h4`) で仮定する。 -/
theorem nonempty_mulEquiv_perm_fin_four_of_four_transitive [FaithfulSMul G Ω]
    (hcard : Nat.card Ω = 4)
    (h4 : ∀ b c : Fin 4 → Ω, Function.Injective b → Function.Injective c →
      ∃ g : G, ∀ i, g • b i = c i) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  haveI : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨e⟩ : Nonempty (Fin 4 ≃ Ω) := Finite.card_eq.mp (by simp [hcard])
  have hbij : Function.Bijective (MulAction.toPermHom G Ω) := by
    refine ⟨MulAction.toPerm_injective, fun σ => ?_⟩
    obtain ⟨g, hg⟩ := h4 (fun i => e i) (fun i => σ (e i)) e.injective
      (σ.injective.comp e.injective)
    refine ⟨g, Equiv.ext fun x => ?_⟩
    have hx : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, hx, hg (e.symm x)]
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (permCongrMulEquiv e.symm)⟩

/-! ### Problem 8A.12 — 置換指標の 2 乗平均 -/

/-- 積作用の固定点集合は各成分の固定点集合の積。 -/
def fixedByProdEquiv {A B : Type*} [MulAction G A] [MulAction G B] (g : G) :
    (MulAction.fixedBy (A × B) g) ≃ (MulAction.fixedBy A g) × (MulAction.fixedBy B g) where
  toFun p := (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2, congrArg Prod.snd p.2⟩)
  invFun q := ⟨(q.1.1, q.2.1), Prod.ext q.1.2 q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 置換指標の 2 乗は積作用 `Ω × Ω` の置換指標。 -/
theorem card_fixedBy_prod (g : G) :
    Nat.card (MulAction.fixedBy (Ω × Ω) g) = Nat.card (MulAction.fixedBy Ω g) ^ 2 := by
  rw [Nat.card_congr (fixedByProdEquiv (A := Ω) (B := Ω) g), Nat.card_prod, sq]

/-- 置換指標の 3 乗は `Ω × Ω × Ω` の置換指標。 -/
theorem card_fixedBy_prod_three (g : G) :
    Nat.card (MulAction.fixedBy (Ω × Ω × Ω) g) = Nat.card (MulAction.fixedBy Ω g) ^ 3 := by
  rw [Nat.card_congr (fixedByProdEquiv (A := Ω) (B := Ω × Ω) g), Nat.card_prod,
    card_fixedBy_prod]
  ring

/-- **Isaacs Problem 8A.12** (p. 236) の骨格: **置換指標 `χ` の 2 乗和は
`Ω × Ω` 上の軌道数 × `|G|`**。したがって `χ(g)²` の平均値は `Ω × Ω` 上の軌道数に等しい。

`χ²` は積作用の置換指標 (`card_fixedBy_prod`) なので, Burnside の補題
(`Ch01.sum_card_fixedBy_nat`) をそのまま `Ω × Ω` に適用すればよい。あとは
「`G` が 2-transitive ⟺ `Ω × Ω` の軌道がちょうど 2 個 (対角線とその外)」を見ればよい。 -/
theorem sum_sq_card_fixedBy [Fintype G] [Finite Ω] :
    ∑ g : G, Nat.card (MulAction.fixedBy Ω g) ^ 2
      = Nat.card (MulAction.orbitRel.Quotient G (Ω × Ω)) * Nat.card G := by
  rw [← OddOrder.Isaacs.Ch01.sum_card_fixedBy_nat (M := G) (β := Ω × Ω)]
  exact (Finset.sum_congr rfl fun g _ => card_fixedBy_prod g).symm

/-- **Isaacs Problem 8A.13** (p. 236) の骨格: 置換指標の 3 乗和は `Ω × Ω × Ω` 上の
軌道数 × `|G|`。

`G` が 3-transitive のとき `Ω³` の軌道は **5 個** — 3 点の一致パターン
(`xxx` / `xxy` / `xyx` / `yxx` / 全相異) がちょうど軌道に対応する (退化 4 パターンは
2-transitivity だけで各 1 軌道)。したがって求める `m` は **5**。 -/
theorem sum_cube_card_fixedBy [Fintype G] [Finite Ω] :
    ∑ g : G, Nat.card (MulAction.fixedBy Ω g) ^ 3
      = Nat.card (MulAction.orbitRel.Quotient G (Ω × Ω × Ω)) * Nat.card G := by
  rw [← OddOrder.Isaacs.Ch01.sum_card_fixedBy_nat (M := G) (β := Ω × Ω × Ω)]
  exact (Finset.sum_congr rfl fun g _ => card_fixedBy_prod_three g).symm

/-- **Isaacs Problem 8A.12** (p. 236) の組合せ部分: 推移的な `G` について
**`Ω × Ω` の `G`-軌道がちょうど 2 個 ⟺ `G` は 2-transitive**。

軌道は「対角線」と「対角線の外」の 2 つ。対角線の類には対角線上の点しか入らないので,
2-transitivity は「対角線外がひとつの軌道」と同値。 -/
theorem card_orbits_prod_eq_two_iff [IsPretransitive G Ω] [Nontrivial Ω] :
    Nat.card (MulAction.orbitRel.Quotient G (Ω × Ω)) = 2 ↔
      ∀ β₁ β₂ γ₁ γ₂ : Ω, β₁ ≠ β₂ → γ₁ ≠ γ₂ → ∃ g : G, g • β₁ = γ₁ ∧ g • β₂ = γ₂ := by
  classical
  obtain ⟨α, β, hαβ⟩ := exists_pair_ne Ω
  have hdiag : ∀ x y : Ω, (Quotient.mk'' (x, y) : MulAction.orbitRel.Quotient G (Ω × Ω))
      = Quotient.mk'' (α, α) → x = y := by
    intro x y h
    rw [Quotient.eq''] at h
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
    have hg' : g • ((α : Ω), (α : Ω)) = (x, y) := hg
    exact (congrArg Prod.fst hg').symm.trans (congrArg Prod.snd hg')
  have hmk : ∀ p q : Ω × Ω, (∃ g : G, g • p = q) →
      (Quotient.mk'' q : MulAction.orbitRel.Quotient G (Ω × Ω)) = Quotient.mk'' p := by
    intro p q hpq
    rw [Quotient.eq'']
    exact MulAction.orbitRel_apply.mpr hpq
  constructor
  · -- 2 軌道 ⟹ 2-transitive
    intro hcard β₁ β₂ γ₁ γ₂ hβ hγ
    obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hcard
    have hmem : ∀ q : MulAction.orbitRel.Quotient G (Ω × Ω), q = x ∨ q = y := fun q => by
      have hq : q ∈ ({x, y} : Set _) := huniv ▸ Set.mem_univ q
      simpa using hq
    have hoff : ∀ (b₁ b₂ : Ω), b₁ ≠ b₂ →
        (Quotient.mk'' (b₁, b₂) : MulAction.orbitRel.Quotient G (Ω × Ω))
          ≠ Quotient.mk'' (α, α) := fun b₁ b₂ hb hc => hb (hdiag b₁ b₂ hc)
    have hsame : (Quotient.mk'' (γ₁, γ₂) : MulAction.orbitRel.Quotient G (Ω × Ω))
        = Quotient.mk'' (β₁, β₂) := by
      rcases hmem (Quotient.mk'' (α, α)) with hα | hα <;>
        rcases hmem (Quotient.mk'' (β₁, β₂)) with hβ' | hβ' <;>
        rcases hmem (Quotient.mk'' (γ₁, γ₂)) with hγ' | hγ' <;>
        first
          | (exact hγ'.trans hβ'.symm)
          | (exact absurd (hβ'.trans hα.symm) (hoff β₁ β₂ hβ))
          | (exact absurd (hγ'.trans hα.symm) (hoff γ₁ γ₂ hγ))
    rw [Quotient.eq''] at hsame
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hsame
    have hg' : g • (β₁, β₂) = (γ₁, γ₂) := hg
    exact ⟨g, congrArg Prod.fst hg', congrArg Prod.snd hg'⟩
  · -- 2-transitive ⟹ 2 軌道
    intro h2
    refine Nat.card_eq_two_iff.mpr ⟨Quotient.mk'' (α, α), Quotient.mk'' (α, β),
      fun hc => hαβ (hdiag α β hc.symm), Set.eq_univ_iff_forall.mpr ?_⟩
    refine Quotient.ind' fun p => ?_
    rcases eq_or_ne p.1 p.2 with hp | hp
    · obtain ⟨g, hg⟩ := exists_smul_eq G α p.1
      exact Set.mem_insert_iff.mpr (Or.inl (hmk (α, α) p ⟨g, Prod.ext hg (hg.trans hp)⟩))
    · obtain ⟨g, hg1, hg2⟩ := h2 α β p.1 p.2 hαβ hp
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
        (hmk (α, β) p ⟨g, Prod.ext hg1 hg2⟩)))

/-- **Isaacs Problem 8A.12** (p. 236) 🎉: 推移的な `G` について
**`G` が 2-transitive ⟺ 置換指標 `χ` の 2 乗の平均値が 2**
(`∑_{g} χ(g)² = 2 |G|`)。

`χ²` は積作用 `Ω × Ω` の置換指標なので, Burnside より `∑ χ² = (Ω×Ω の軌道数)·|G|`。
軌道数が 2 であることが 2-transitivity と同値 (`card_orbits_prod_eq_two_iff`)。 -/
theorem sum_sq_card_fixedBy_eq_two_mul_iff [Fintype G] [Finite Ω] [IsPretransitive G Ω]
    [Nontrivial Ω] :
    (∑ g : G, Nat.card (MulAction.fixedBy Ω g) ^ 2) = 2 * Nat.card G ↔
      ∀ β₁ β₂ γ₁ γ₂ : Ω, β₁ ≠ β₂ → γ₁ ≠ γ₂ → ∃ g : G, g • β₁ = γ₁ ∧ g • β₂ = γ₂ := by
  rw [sum_sq_card_fixedBy, ← card_orbits_prod_eq_two_iff]
  exact ⟨fun h => Nat.eq_of_mul_eq_mul_right Nat.card_pos h, fun h => by rw [h]⟩

/-! ### Problem 8A.14 — 部分群の軌道数は指数以下 -/

/-- **Isaacs Problem 8A.14** (p. 236) 前半: `G` が `Ω` に推移的で `[G : H] = m` なら,
`H` の `Ω` 上の軌道は高々 `m` 個。

`gH ↦ ⟦g⁻¹ • α⟧` が `G ⧸ H` から `H`-軌道の集合への**全射**になる:
`b = a h` (`h ∈ H`) なら `b⁻¹ • α = h⁻¹ • (a⁻¹ • α)` で同じ `H`-軌道, また `G` の推移性から
任意の `ω = g • α` は `g⁻¹H` の像。 -/
def cosetToOrbit (H : Subgroup G) (α : Ω) :
    G ⧸ H → MulAction.orbitRel.Quotient H Ω :=
  Quotient.lift (fun g : G => (Quotient.mk'' ((g : G)⁻¹ • α) :
      MulAction.orbitRel.Quotient H Ω)) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    refine Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨⟨a⁻¹ * b, hmem⟩, ?_⟩)
    change ((a⁻¹ * b : G)) • ((b : G)⁻¹ • α) = (a : G)⁻¹ • α
    rw [← mul_smul]
    group)

@[simp] lemma cosetToOrbit_mk (H : Subgroup G) (α : Ω) (g : G) :
    cosetToOrbit H α (Quotient.mk'' g) = Quotient.mk'' ((g : G)⁻¹ • α) := rfl

lemma cosetToOrbit_surjective [IsPretransitive G Ω] (H : Subgroup G) (α : Ω) :
    Function.Surjective (cosetToOrbit H α) := by
  refine Quotient.ind' fun ω => ?_
  obtain ⟨g, hg⟩ := exists_smul_eq G α ω
  refine ⟨Quotient.mk'' g⁻¹, ?_⟩
  change (Quotient.mk'' ((g⁻¹ : G)⁻¹ • α) : MulAction.orbitRel.Quotient H Ω)
    = Quotient.mk'' ω
  rw [inv_inv, hg]

theorem card_orbits_le_index [Finite G] [Finite Ω] [IsPretransitive G Ω]
    (H : Subgroup G) (α : Ω) :
    Nat.card (MulAction.orbitRel.Quotient H Ω) ≤ H.index := by
  classical
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_surjective _ (cosetToOrbit_surjective H α)

/-- 8A.14 後半の核: `H` が点安定化群 `G_{a⁻¹ • α}` を含まないなら, `aH` と同じ
`H`-軌道を与える別の剰余類 `bH ≠ aH` がある。

`u ∈ a⁻¹ G_α a ∖ H` を取り `b := a u⁻¹` とすると `bH ≠ aH` で
`b⁻¹ • α = u a⁻¹ • α = a⁻¹ • α`。 -/
theorem exists_ne_coset_same_orbit {H : Subgroup G} {α : Ω} (a : G)
    (hns : ¬ (∀ g ∈ MulAction.stabilizer G ((a : G)⁻¹ • α), g ∈ H)) :
    ∃ b : G, (b : G)⁻¹ • α = (a : G)⁻¹ • α ∧ a⁻¹ * b ∉ H := by
  simp only [not_forall] at hns
  obtain ⟨u, hu, huH⟩ := hns
  refine ⟨a * u⁻¹, ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv, mul_smul]
    exact MulAction.mem_stabilizer_iff.mp hu
  · intro hc
    exact huH (by simpa using H.inv_mem hc)

/-- **Isaacs Problem 8A.14** (p. 236) 後半: `H` がどの点安定化群も含まないなら,
`H` の `Ω` 上の軌道は高々 `m/2` 個 (`2 · 軌道数 ≤ [G:H]`)。

全射 `cosetToOrbit` のファイバーが常に 2 元以上 (`exists_ne_coset_same_orbit`) なので,
`|G ⧸ H| = ∑_o |fiber o| ≥ 2 · 軌道数`。 -/
theorem two_mul_card_orbits_le_index [Finite G] [Finite Ω] [IsPretransitive G Ω]
    (H : Subgroup G) (α : Ω) (hns : ∀ ω : Ω, ¬ (MulAction.stabilizer G ω ≤ H)) :
    2 * Nat.card (MulAction.orbitRel.Quotient H Ω) ≤ H.index := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient H Ω) := Fintype.ofFinite _
  have hfib : ∀ o : MulAction.orbitRel.Quotient H Ω,
      2 ≤ (Finset.univ.filter fun c => cosetToOrbit H α c = o).card := by
    intro o
    obtain ⟨c, hc⟩ := cosetToOrbit_surjective H α o
    induction c using Quotient.ind' with
    | _ a =>
      obtain ⟨b, hbα, hbH⟩ := exists_ne_coset_same_orbit (H := H) a (hns ((a : G)⁻¹ • α))
      refine Finset.one_lt_card.mpr ⟨Quotient.mk'' a, by simp [hc], Quotient.mk'' b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, cosetToOrbit_mk, hbα]
        exact hc
      · exact fun hab => hbH (QuotientGroup.leftRel_apply.mp (Quotient.exact' hab))
  calc 2 * Nat.card (MulAction.orbitRel.Quotient H Ω)
      = ∑ _o : MulAction.orbitRel.Quotient H Ω, 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card,
          mul_comm]
    _ ≤ ∑ o : MulAction.orbitRel.Quotient H Ω,
          (Finset.univ.filter fun c => cosetToOrbit H α c = o).card :=
        Finset.sum_le_sum fun o _ => hfib o
    _ = Fintype.card (G ⧸ H) :=
        (Finset.card_eq_sum_card_fiberwise fun c _ => Finset.mem_univ _).symm
    _ = H.index := by rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]

/-! ### Problem 8A.15 — 剰余類への 2-transitivity と二重剰余類 -/

/-- **Isaacs Problem 8A.15** (p. 236): `G` の `H`-剰余類への作用が 2-transitive ⟺
`H × H` の両側作用 `g · (x,y) = x⁻¹ g y` が `G` 上ちょうど 2 軌道をもつ。

`H × H`-軌道は**二重剰余類** `H g H` そのもので, そのひとつは `H` 自身。よって
「ちょうど 2 軌道」= 「`H` の外がひとつの二重剰余類」であり, これが本補題の左辺。
右辺は「点安定化群 `G_{1·H} = H` が `(G ⧸ H) ∖ {H}` に推移的」= 2-transitivity。 -/
theorem doubleCoset_transitive_iff (H : Subgroup G) :
    (∀ a b : G, a ∉ H → b ∉ H → ∃ x ∈ H, ∃ y ∈ H, x * a * y = b) ↔
      (∀ a b : G, (a : G ⧸ H) ≠ ((1 : G) : G ⧸ H) → (b : G ⧸ H) ≠ ((1 : G) : G ⧸ H) →
        ∃ h ∈ H, h • (a : G ⧸ H) = (b : G ⧸ H)) := by
  have hone : ∀ a : G, ((a : G ⧸ H) = ((1 : G) : G ⧸ H)) ↔ a ∈ H := by
    intro a
    rw [QuotientGroup.eq, mul_one, H.inv_mem_iff]
  constructor
  · intro h a b ha hb
    obtain ⟨x, hx, y, hy, hxy⟩ := h a b (fun hc => ha ((hone a).mpr hc))
      (fun hc => hb ((hone b).mpr hc))
    refine ⟨x, hx, ?_⟩
    rw [show x • (a : G ⧸ H) = ((x * a : G) : G ⧸ H) from rfl, QuotientGroup.eq]
    have hy' : (x * a)⁻¹ * b = y := by rw [← hxy]; group
    rw [hy']
    exact hy
  · intro h a b ha hb
    obtain ⟨x, hx, hxa⟩ := h a b (fun hc => ha ((hone a).mp hc)) (fun hc => hb ((hone b).mp hc))
    rw [show x • (a : G ⧸ H) = ((x * a : G) : G ⧸ H) from rfl, QuotientGroup.eq] at hxa
    exact ⟨x, hx, (x * a)⁻¹ * b, hxa, by group⟩

/-! ### Problem 8A.11 — 1 次元アフィン群 `AGL(1, F)` -/

section AffineLine

variable {F : Type*} [Field F]

/-- `x ↦ a * x + b` (`a` は単元) が定める `F` の置換。 -/
def affineLinePerm (a : Fˣ) (b : F) : Equiv.Perm F :=
  (Equiv.mulLeft₀ (a : F) a.ne_zero).trans (Equiv.addRight b)

@[simp] lemma affineLinePerm_apply (a : Fˣ) (b x : F) :
    affineLinePerm a b x = (a : F) * x + b := rfl

/-- **1 次元アフィン群** `AGL(1, F) = {x ↦ a x + b : a ∈ Fˣ, b ∈ F}` — `Sym(F)` の部分群。

`q = |F|` のとき位数は `q(q - 1)` で, `F` 上 sharply 2-transitive
(`existsUnique_affineLineGroup_of_ne`)。 -/
def affineLineGroup (F : Type*) [Field F] : Subgroup (Equiv.Perm F) where
  carrier := {p | ∃ (a : Fˣ) (b : F), p = affineLinePerm a b}
  one_mem' := ⟨1, 0, by ext x; simp⟩
  mul_mem' := by
    rintro - - ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    refine ⟨a * a', (a : F) * b' + b, Equiv.ext fun x => ?_⟩
    simp only [Equiv.Perm.mul_apply, affineLinePerm_apply, Units.val_mul]
    ring
  inv_mem' := by
    rintro - ⟨a, b, rfl⟩
    refine ⟨a⁻¹, -(((a⁻¹ : Fˣ) : F) * b), inv_eq_of_mul_eq_one_right (Equiv.ext fun x => ?_)⟩
    simp only [Equiv.Perm.mul_apply, affineLinePerm_apply, Equiv.Perm.one_apply, mul_add,
      mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
    ring

lemma mem_affineLineGroup_iff {p : Equiv.Perm F} :
    p ∈ affineLineGroup F ↔ ∃ (a : Fˣ) (b : F), p = affineLinePerm a b :=
  ⟨fun h => h, fun h => h⟩

/-- **Isaacs Problem 8A.11** (p. 236): `AGL(1, F)` は `F` 上 **sharply 2-transitive** —
相異なる 2 点の任意の組を相異なる 2 点の任意の組へ移す元がちょうど 1 つある。

`a = (y₁ - y₂)/(x₁ - x₂)`, `b = y₁ - a x₁` が唯一の解 (アフィン写像は 2 点での値で決まる)。
有限体は各素数冪 `q > 1` について存在するので, これで次数 `q` の可解 sharply 2-transitive
置換群の存在が言える (可解性は `affineLineGroup_isSolvable`)。 -/
theorem existsUnique_affineLineGroup_of_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) :
    ∃! p : ↥(affineLineGroup F),
      (p : Equiv.Perm F) x₁ = y₁ ∧ (p : Equiv.Perm F) x₂ = y₂ := by
  have hxsub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hysub : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hy
  set a : Fˣ := Units.mk0 ((y₁ - y₂) / (x₁ - x₂)) (div_ne_zero hysub hxsub) with ha
  have hacoe : (a : F) = (y₁ - y₂) / (x₁ - x₂) := rfl
  have hax : (a : F) * (x₁ - x₂) = y₁ - y₂ := by
    rw [hacoe, div_mul_cancel₀ _ hxsub]
  refine ⟨⟨affineLinePerm a (y₁ - (a : F) * x₁),
    mem_affineLineGroup_iff.mpr ⟨a, _, rfl⟩⟩, ⟨by simp, ?_⟩, ?_⟩
  · simp only [affineLinePerm_apply]
    linear_combination -hax
  · rintro ⟨q, hq⟩ ⟨h1, h2⟩
    obtain ⟨a', b', rfl⟩ := mem_affineLineGroup_iff.mp hq
    simp only [affineLinePerm_apply] at h1 h2
    have hA : (a' : F) = (a : F) := by
      have hthis : (a' : F) * (x₁ - x₂) = y₁ - y₂ := by linear_combination h1 - h2
      rw [hacoe, eq_div_iff hxsub]
      exact hthis
    have hB : b' = y₁ - (a : F) * x₁ := by rw [← hA]; linear_combination h1
    refine Subtype.ext (Equiv.ext fun x => ?_)
    simp only [affineLinePerm_apply, hA, hB]

/-- `AGL(1,F)` の元の**線形部分** `a`。`p x = a x + b` から `a = p 1 - p 0` として取り出す。 -/
def affineLinearPart (p : ↥(affineLineGroup F)) : Fˣ :=
  Units.mk0 ((p : Equiv.Perm F) 1 - (p : Equiv.Perm F) 0) <| by
    obtain ⟨a, b, hab⟩ := mem_affineLineGroup_iff.mp p.2
    rw [show ((p : Equiv.Perm F)) = affineLinePerm a b from hab]
    simp

lemma affineLinearPart_affineLinePerm (a : Fˣ) (b : F)
    (h : affineLinePerm a b ∈ affineLineGroup F) :
    affineLinearPart ⟨affineLinePerm a b, h⟩ = a := by
  refine Units.ext ?_
  simp [affineLinearPart]

/-- 線形部分は準同型 `AGL(1,F) →* Fˣ`。 -/
def affineLinearPartHom : ↥(affineLineGroup F) →* Fˣ where
  toFun := affineLinearPart
  map_one' := by
    refine Units.ext ?_
    simp [affineLinearPart]
  map_mul' p q := by
    obtain ⟨a, b, hab⟩ := mem_affineLineGroup_iff.mp p.2
    obtain ⟨a', b', hab'⟩ := mem_affineLineGroup_iff.mp q.2
    refine Units.ext ?_
    simp only [affineLinearPart, Units.val_mk0, Units.val_mul, Subgroup.coe_mul,
      Equiv.Perm.mul_apply, hab, hab', affineLinePerm_apply]
    ring

/-- 平行移動群 (= 線形部分が `1`) は可換。 -/
instance affineLinearPartHom_ker_isSolvable :
    IsSolvable ↥(MonoidHom.ker (affineLinearPartHom (F := F))) := by
  refine isSolvable_of_comm fun p q => ?_
  obtain ⟨a, b, hab⟩ := mem_affineLineGroup_iff.mp (p : ↥(affineLineGroup F)).2
  obtain ⟨a', b', hab'⟩ := mem_affineLineGroup_iff.mp (q : ↥(affineLineGroup F)).2
  have hlin : ∀ (r : ↥(MonoidHom.ker (affineLinearPartHom (F := F)))) (c : Fˣ) (d : F),
      ((r : ↥(affineLineGroup F)) : Equiv.Perm F) = affineLinePerm c d → c = 1 := by
    intro r c d hr
    have hk : affineLinearPart (r : ↥(affineLineGroup F)) = 1 := MonoidHom.mem_ker.mp r.2
    rw [show (r : ↥(affineLineGroup F)) = ⟨affineLinePerm c d, hr ▸ (r : ↥(affineLineGroup F)).2⟩
      from Subtype.ext hr, affineLinearPart_affineLinePerm] at hk
    exact hk
  have ha : a = 1 := hlin p a b hab
  have ha' : a' = 1 := hlin q a' b' hab'
  refine Subtype.ext (Subtype.ext (Equiv.ext fun x => ?_))
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hab, hab', ha, ha',
    affineLinePerm_apply, Units.val_one, one_mul]
  ring

/-- **Isaacs Problem 8A.11** (p. 236) の可解性: `AGL(1,F)` は metabelian ゆえ**可解**。

線形部分 `p ↦ a` は `Fˣ` への準同型で, その核は平行移動群 `≅ F⁺` (可換)。 -/
instance affineLineGroup_isSolvable : IsSolvable ↥(affineLineGroup F) :=
  solvable_of_ker_le_range (MonoidHom.ker (affineLinearPartHom (F := F))).subtype
    affineLinearPartHom (le_of_eq (Subgroup.range_subtype _).symm)

end AffineLine

end

end OddOrder.Isaacs.Ch08
