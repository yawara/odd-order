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
