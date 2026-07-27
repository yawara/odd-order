/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
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
- `smul_eq_self_of_mem_centralizer`, `centralizer_inf_stabilizer_eq_bot`,
  `bijective_smulBase_top_of_comm` — **Problem 8A.2**: transitive な `H ≤ G` の
  中心化群 `C_G(H)` は半正則。帰結として可換 transitive な置換群は regular。
- `smul_orbit_eq_orbit_smul`, `card_orbit_eq_of_normal` — **Problem 8A.8**:
  transitive な `G` の正規部分群 `N` について `G` は `N`-軌道を推移的に置換し,
  したがって `N` は half-transitive (すべての `N`-軌道が同じ濃度)。
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

end

end OddOrder.Isaacs.Ch08
