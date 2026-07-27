/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import OddOrder.Isaacs.Ch08_PermutationGroups.RegularNormal

/-!
# Isaacs Problems 8A (pp. 235–236) — 正則表現と regular normal 部分群

**Problems 8A.1–8A.4**。「regular 部分群」は `RegularNormal.lean` の流儀に合わせ
**軌道写像 `smulBase N α : ↥N → Ω` が全単射**であることとして扱う (Thm 8.5)。
半正則 (semiregular) は同じく**軌道写像が単射**、同値に `N ⊓ G_α = ⊥`
(`injective_smulBase_iff_disjoint_stabilizer`)。

## Main results

- `regularRep`, `bijective_smulBase_regularRep_range` — 型の同値に沿って運んだ
  左正則表現とその像の regular 性 (8A.1 / 8A.3 / 8A.4 の共通道具)。
- `exists_regular_subgroups_of_equiv`, `exists_regular_subgroups_of_card_eq` —
  **Problem 8A.1** 前半: `|A| = |B|` なら `Sym(A)` は `A`, `B` に同型な regular 部分群を
  ともにもつ。
- `cyclicFourSub`, `kleinFourSub`, `exists_two_nonisomorphic_regular_normal` —
  **Problem 8A.1 後半**: 置換群は同型でない regular normal 部分群をもちうる
  (`Ω = ZMod 4`, `D₈ = T ⊔ V` で `T ≅ Z₄`, `V ≅ Z₂ × Z₂`)。`ZMod 4` 上の等式は
  すべて `decide`。⚠ 8A.4 と矛盾しないのは `T ⊓ V ≠ ⊥` だから。
- `smul_eq_self_of_mem_centralizer`, `centralizer_inf_stabilizer_eq_bot`,
  `bijective_smulBase_top_of_comm` — **Problem 8A.2**: transitive な `H ≤ G` の
  中心化群 `C_G(H)` は半正則。帰結として可換 transitive な置換群は regular。
- `regularRepRight`, `exists_two_distinct_regular_normal_of_center_eq_bot` —
  **Problem 8A.3**: `Z(G) = 1` (かつ非自明) なら `Sym(G)` の中に `G` に同型な相異なる
  regular normal 部分群が 2 つある (左正則表現の像と右正則表現の像)。
- `centralizer_eq_of_regular_of_inf_eq_bot`, `regularPairHom`,
  `mulEquiv_and_center_eq_bot_of_regular_normal` — **Problem 8A.4**: regular normal な
  `U`, `V` が `U ⊓ V = 1` を満たすと `C_G(U) = V` となり, `U ≅ V` で中心はともに自明。
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

/-- `T = ⟨t⟩ = {1, t, t², t³} ≅ Z₄` — `ZMod 4` の平行移動群。 -/
def cyclicFourSub : Subgroup (Equiv.Perm (ZMod 4)) where
  carrier := {p | p = 1 ∨ p = transZFour ∨ p = transZFour ^ 2 ∨ p = transZFour ^ 3}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> decide

/-- `V = {1, t², s, s t²} ≅ Z₂ × Z₂` — Klein 四元群。 -/
def kleinFourSub : Subgroup (Equiv.Perm (ZMod 4)) where
  carrier := {p | p = 1 ∨ p = transZFour ^ 2 ∨ p = flipZFour ∨ p = flipZFour * transZFour ^ 2}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> decide

lemma mem_cyclicFourSub {p : Equiv.Perm (ZMod 4)} :
    p ∈ cyclicFourSub ↔
      p = 1 ∨ p = transZFour ∨ p = transZFour ^ 2 ∨ p = transZFour ^ 3 :=
  ⟨fun h => h, fun h => h⟩

lemma mem_kleinFourSub {p : Equiv.Perm (ZMod 4)} :
    p ∈ kleinFourSub ↔
      p = 1 ∨ p = transZFour ^ 2 ∨ p = flipZFour ∨ p = flipZFour * transZFour ^ 2 :=
  ⟨fun h => h, fun h => h⟩

/-- `T` は `ZMod 4` に regular に作用する。 -/
lemma bijective_smulBase_cyclicFourSub :
    Function.Bijective (smulBase cyclicFourSub (0 : ZMod 4)) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [smulBase, Equiv.Perm.smul_def] at hab
    rcases mem_cyclicFourSub.mp ha with rfl | rfl | rfl | rfl <;>
      rcases mem_cyclicFourSub.mp hb with rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd hab (by decide)
  · intro x
    fin_cases x
    · exact ⟨⟨1, Or.inl rfl⟩, by decide⟩
    · exact ⟨⟨transZFour, Or.inr (Or.inl rfl)⟩, by decide⟩
    · exact ⟨⟨transZFour ^ 2, Or.inr (Or.inr (Or.inl rfl))⟩, by decide⟩
    · exact ⟨⟨transZFour ^ 3, Or.inr (Or.inr (Or.inr rfl))⟩, by decide⟩

/-- `V` も `ZMod 4` に regular に作用する (軌道は `0 ↦ 0, 2, 1, 3`)。 -/
lemma bijective_smulBase_kleinFourSub :
    Function.Bijective (smulBase kleinFourSub (0 : ZMod 4)) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [smulBase, Equiv.Perm.smul_def] at hab
    rcases mem_kleinFourSub.mp ha with rfl | rfl | rfl | rfl <;>
      rcases mem_kleinFourSub.mp hb with rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd hab (by decide)
  · intro x
    fin_cases x
    · exact ⟨⟨1, Or.inl rfl⟩, by decide⟩
    · exact ⟨⟨flipZFour, Or.inr (Or.inr (Or.inl rfl))⟩, by decide⟩
    · exact ⟨⟨transZFour ^ 2, Or.inr (Or.inl rfl)⟩, by decide⟩
    · exact ⟨⟨flipZFour * transZFour ^ 2, Or.inr (Or.inr (Or.inr rfl))⟩, by decide⟩

/-- `T ≇ V`: `V` は指数 2 だが `T` は位数 4 の元をもつ。 -/
lemma not_nonempty_mulEquiv_cyclicFour_kleinFour :
    ¬ Nonempty (↥cyclicFourSub ≃* ↥kleinFourSub) := by
  rintro ⟨φ⟩
  have hV : ∀ v : ↥kleinFourSub, v ^ 2 = 1 := by
    rintro ⟨v, hv⟩
    refine Subtype.ext ?_
    push_cast
    rcases mem_kleinFourSub.mp hv with rfl | rfl | rfl | rfl <;> decide
  have ht : (⟨transZFour, Or.inr (Or.inl rfl)⟩ : ↥cyclicFourSub) ^ 2 ≠ 1 := fun hc =>
    transZFour_sq_ne_one (by simpa using congrArg Subtype.val hc)
  exact ht (φ.injective (by rw [map_pow, hV, map_one]))

/-- `V ≤ N(T)` (`s t s⁻¹ = t⁻¹` の帰結)。 -/
lemma kleinFourSub_le_normalizer_cyclicFourSub :
    kleinFourSub ≤ Subgroup.normalizer (cyclicFourSub : Set (Equiv.Perm (ZMod 4))) := by
  intro v hv
  simp only [Subgroup.mem_normalizer_iff, mem_cyclicFourSub]
  rcases mem_kleinFourSub.mp hv with rfl | rfl | rfl | rfl <;> decide

/-- `T ≤ N(V)` (`t s t⁻¹ = s t²` の帰結)。 -/
lemma cyclicFourSub_le_normalizer_kleinFourSub :
    cyclicFourSub ≤ Subgroup.normalizer (kleinFourSub : Set (Equiv.Perm (ZMod 4))) := by
  intro u hu
  simp only [Subgroup.mem_normalizer_iff, mem_kleinFourSub]
  rcases mem_cyclicFourSub.mp hu with rfl | rfl | rfl | rfl <;> decide

/-- **Isaacs Problem 8A.1** (p. 235), 後半 🎉: 置換群は**同型でない regular normal
部分群**をもちうる。

`Ω = ZMod 4`, `G = T ⊔ V = D₈` (`S₄` の Sylow 2-部分群) で, `T = ⟨x ↦ x+1⟩ ≅ Z₄` と
Klein 群 `V = {1, x↦x+2, x↦1-x, x↦3-x} ≅ Z₂ × Z₂` はともに `Ω` に regular に作用し
`G` に正規だが, 同型でない。

⚠ **8A.4 と矛盾しない**: そちらは `U ⊓ V = 1` を仮定するが, ここでは
`T ⊓ V = {1, x ↦ x+2} ≠ ⊥`。 -/
theorem exists_two_nonisomorphic_regular_normal :
    ∃ T V : Subgroup (Equiv.Perm (ZMod 4)),
      Function.Bijective (smulBase T (0 : ZMod 4)) ∧
      Function.Bijective (smulBase V (0 : ZMod 4)) ∧
      T ⊔ V ≤ Subgroup.normalizer (T : Set (Equiv.Perm (ZMod 4))) ∧
      T ⊔ V ≤ Subgroup.normalizer (V : Set (Equiv.Perm (ZMod 4))) ∧
      ¬ Nonempty (↥T ≃* ↥V) :=
  ⟨cyclicFourSub, kleinFourSub, bijective_smulBase_cyclicFourSub,
    bijective_smulBase_kleinFourSub,
    sup_le Subgroup.le_normalizer kleinFourSub_le_normalizer_cyclicFourSub,
    sup_le cyclicFourSub_le_normalizer_kleinFourSub Subgroup.le_normalizer,
    not_nonempty_mulEquiv_cyclicFour_kleinFour⟩

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

end

end OddOrder.Isaacs.Ch08
