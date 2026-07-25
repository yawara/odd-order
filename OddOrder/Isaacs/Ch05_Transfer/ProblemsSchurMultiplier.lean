/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.CentralTransfer

/-!
# Isaacs Problems 5A.5 / 5A.7 — Schur 乗数の上界 (stem extension の ∀-形)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 5A.5 / 5A.7 (書籍 p. 153)。

書籍は Schur 乗数 `M(G)` を用いて次を述べる。

* **5A.5** `C ⊴ G` cyclic で `G/C` cyclic ⇒ `|M(G)|` は `|C : G'|` を割る。
* **5A.7** `B`, `C` cyclic, `BC = G`, `B ∩ C > 1`, `C ⊴ G`, `|C : G'| = n`
  ⇒ `|M(G)| < n`。

`M(G)` は「`Γ/Z ≅ G` かつ `Z ≤ Γ' ∩ Z(Γ)` なる `Z` のうち位数最大のもの」であり,
その universal object (Schur 表現群) の存在は mathlib にも本リポジトリにも無い (issue 9206)。
しかし **上界の主張はいずれも「そのような `(Γ, Z)` すべてについて」の ∀-形で述べれば
`M(G)` の定義をまったく必要としない**。本ファイルはその ∀-形を証明する。`|M(G)|` は
`Nat.card (ker f)` の最大値にほかならないので, ∀-形は書籍の主張と同値である
(`M(G)` を実現する `Γ` を取れば直ちに書籍の形が出る)。

同じ流儀は既に `CentralTransfer.lean` の Isaacs Thm 5.4 弱形
`not_isMulCommutative_sylow_of_le_commutator_inf_center` が採っている。

## 主な内容

* `IsStemExtension` — 全射 `f : Γ →* G` で `ker f ≤ Γ' ⊓ Z(Γ)` (**stem extension**)。
  `M(G)` は `ker f` の取りうる最大の位数。
* `isMulCommutative_comap_of_isCyclic` — `ker f ≤ Z(Γ)` なら cyclic な `C ≤ G` の
  逆像は可換 (`M(G)` 上界論法の要)。
* `relIndex_commutator_eq_card_inf_center` — Isaacs Lemma 4.6 の指数形
  `|A : Γ'| = |A ∩ Z(Γ)|` (`A ⊴ Γ` 可換, `Γ/A` cyclic)。
* `card_ker_dvd_relIndex_commutator` — **Problem 5A.5** の ∀-形。
* `card_ker_lt_relIndex_commutator` — **Problem 5A.7** の ∀-形。
-/

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

section /- 5A: Schur multiplier bounds (p. 153) -/

/-- **Stem extension** (Isaacs §5A, Schur 乗数の文脈): 全射準同型 `f : Γ →* G` であって
`ker f ≤ Γ' ⊓ Z(Γ)` をみたすもの。

書籍の言い回し「`Γ` は部分群 `Z` を含み `Γ/Z ≅ G` かつ `Z ⊆ Γ' ∩ Z(Γ)`」(Problem 5A.5 の
hint) を, 同型 `Γ/Z ≅ G` を運ぶ代わりに全射 `f` とその核で表したもの。両者は
`f ↦ ker f` / `Z ↦ (Γ →* Γ/Z ≅ G)` で 1:1 対応する。

Schur 乗数 `M(G)` は「`ker f` の取りうる最大位数」であり, その universal な実現
(Schur 表現群) は本リポジトリ未実装 (issue 9206)。上界の主張は `M(G)` を定義せずとも
本述語についての ∀-形で表せる。 -/
structure IsStemExtension {Γ G : Type*} [Group Γ] [Group G] (f : Γ →* G) : Prop where
  /-- `f` は全射 (すなわち `Γ/ker f ≅ G`). -/
  surjective : Function.Surjective f
  /-- 核は交換子群に含まれる. -/
  ker_le_commutator : f.ker ≤ _root_.commutator Γ
  /-- 核は中心に含まれる (中心拡大). -/
  ker_le_center : f.ker ≤ Subgroup.center Γ

/-! ### 逆像の可換性 -/

/-- `ker f ≤ Z(Γ)` のとき, cyclic な部分群 `C ≤ G` の逆像 `f⁻¹(C)` は可換。

`f` を `f⁻¹(C) → C` に制限すると核は `ker f ∩ f⁻¹(C) ≤ Z(Γ) ∩ f⁻¹(C) ≤ Z(f⁻¹(C))` なので
mathlib の `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`
(「cyclic 群への準同型で核が中心に入るなら可換」= Isaacs Lemma 4.5 相当) が使える。

⚠ `f` の全射性は不要 (`f⁻¹(C) → C` の像が cyclic 群の部分群であればよい)。 -/
theorem isMulCommutative_comap_of_isCyclic {Γ G : Type*} [Group Γ] [Group G] {f : Γ →* G}
    (hker : f.ker ≤ Subgroup.center Γ) {C : Subgroup G} (hC : IsCyclic ↥C) :
    IsMulCommutative ↥(C.comap f) := by
  haveI := hC
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (((f.comp (C.comap f).subtype).codRestrict C (fun a => Subgroup.mem_comap.mp a.2))) ?_
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have hfa : f (a : Γ) = 1 := congrArg Subtype.val ha
  have hcent : (a : Γ) ∈ Subgroup.center Γ := hker (MonoidHom.mem_ker.mpr hfa)
  rw [Subgroup.mem_center_iff]
  intro b
  exact Subtype.ext ((Subgroup.mem_center_iff.mp hcent) (b : Γ))

/-- `IsMulCommutative ↥A` を Isaacs Lemma 4.6 が要求する
「`∀ a ∈ A, ∀ b ∈ A, a * b = b * a`」の形に落とす。 -/
theorem forall_mul_comm_of_isMulCommutative {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (hA : IsMulCommutative ↥A) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  exact congrArg Subtype.val (hA.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)

/-! ### Lemma 4.6 の指数形 -/

/-- **Isaacs Lemma 4.6 の指数形**: `A ⊴ Γ` 可換で `Γ/A` cyclic ⇒ `|A : Γ'| = |A ∩ Z(Γ)|`。

書籍 p. 118 の `|A| = |G'| |A ∩ Z(G)|` を `Γ' ≤ A` (`Γ/A` 可換) と Lagrange で割った形。
本リポジトリの位数形は
`Ch04.card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient`。 -/
theorem relIndex_commutator_eq_card_inf_center {Γ : Type*} [Group Γ] [Finite Γ]
    {A : Subgroup Γ} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hCyc : IsCyclic (Γ ⧸ A)) :
    (_root_.commutator Γ).relIndex A = Nat.card (A ⊓ Subgroup.center Γ : Subgroup Γ) := by
  haveI := hCyc
  -- Γ' ≤ A: Γ/A は cyclic ⇒ 可換
  have hle : _root_.commutator Γ ≤ A :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  -- Lagrange: |Γ'| · |A : Γ'| = |A|
  have hlag : Nat.card (_root_.commutator Γ) * (_root_.commutator Γ).relIndex A = Nat.card A := by
    have h1 : Nat.card ((_root_.commutator Γ).subgroupOf A) *
        ((_root_.commutator Γ).subgroupOf A).index = Nat.card A := Subgroup.card_mul_index _
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  -- Lemma 4.6 の位数形
  have h46 := Ch04.card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
    hAb hCyc
  have hpos : 0 < Nat.card (_root_.commutator Γ) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (hlag.trans h46.symm)

/-! ### Problem 5A.5 -/

/-- **Isaacs Problem 5A.5** (∀-形): `f : Γ →* G` が stem extension, `C ⊴ G` は cyclic で
`G/C` も cyclic なら `|ker f|` は `|C : G'|` を割る。

`|M(G)|` は `|ker f|` の最大値なので, これは書籍の `|M(G)| ∣ |C : G'|` と同値。

**証明** (書籍 hint = Lemma 4.6 の適用): `A := f⁻¹(C)` とおく。
`ker f ≤ Z(Γ)` と `C` cyclic から `A` は可換 (`isMulCommutative_comap_of_isCyclic`),
`Γ/A ≅ G/C` は cyclic。Lemma 4.6 より `|A : Γ'| = |A ∩ Z(Γ)|`。
`ker f ≤ Γ' ⊓ Z(Γ)` かつ `ker f ≤ A` なので `ker f ≤ A ∩ Z(Γ)`, Lagrange で
`|ker f| ∣ |A ∩ Z(Γ)| = |A : Γ'| = |C : G'|` (最後は `f` による対応)。 -/
theorem card_ker_dvd_relIndex_commutator {Γ G : Type*} [Group Γ] [Group G] [Finite Γ]
    {f : Γ →* G} (hf : IsStemExtension f) {C : Subgroup G} [C.Normal]
    (hC : IsCyclic ↥C) (hGC : IsCyclic (G ⧸ C)) :
    Nat.card f.ker ∣ (_root_.commutator G).relIndex C := by
  haveI := hGC
  -- A := f⁻¹(C)
  have hAb : ∀ a ∈ C.comap f, ∀ b ∈ C.comap f, a * b = b * a :=
    forall_mul_comm_of_isMulCommutative (isMulCommutative_comap_of_isCyclic hf.ker_le_center hC)
  -- Γ/A ≅ G/C は cyclic
  have hkercomp : ((QuotientGroup.mk' C).comp f).ker = C.comap f := by
    ext x
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp f) :=
    (QuotientGroup.mk'_surjective C).comp hf.surjective
  have hACyc : IsCyclic (Γ ⧸ C.comap f) := by
    have e : Γ ⧸ C.comap f ≃* G ⧸ C :=
      (QuotientGroup.quotientMulEquivOfEq hkercomp.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
    exact isCyclic_of_surjective e.symm e.symm.surjective
  -- Lemma 4.6 の指数形
  have hidx := relIndex_commutator_eq_card_inf_center hAb hACyc
  -- ker f ≤ A ∩ Z(Γ)
  have hkerA : f.ker ≤ C.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact C.one_mem
  have hkerle : f.ker ≤ C.comap f ⊓ Subgroup.center Γ :=
    le_inf hkerA hf.ker_le_center
  -- |C : G'| = |A : Γ'|
  have htrans : (_root_.commutator G).relIndex C = (_root_.commutator Γ).relIndex (C.comap f) := by
    have hmap : (_root_.commutator Γ).map f = _root_.commutator G := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective f hf.surjective]
    have hcomap : (_root_.commutator G).comap f = _root_.commutator Γ := by
      rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.mpr hf.ker_le_commutator]
    rw [← hcomap, Subgroup.relIndex_comap (_root_.commutator G) f (C.comap f),
      Subgroup.map_comap_eq_self_of_surjective hf.surjective C]
  rw [htrans, hidx]
  exact Subgroup.card_dvd_of_le hkerle

/-! ### Problem 5A.7 -/

/-- `B` cyclic かつ `BC = G` (`C ⊴ G`) なら `G/C` は cyclic (`B` の像で生成される)。 -/
theorem isCyclic_quotient_of_mul_eq_top {G : Type*} [Group G] {B C : Subgroup G} [C.Normal]
    (hB : IsCyclic ↥B) (hBC : ∀ g : G, ∃ b ∈ B, ∃ c ∈ C, g = b * c) :
    IsCyclic (G ⧸ C) := by
  haveI := hB
  refine isCyclic_of_surjective ((QuotientGroup.mk' C).comp B.subtype) ?_
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, hb, c, hc, rfl⟩ := hBC g
  refine ⟨⟨b, hb⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq.mpr (by simpa using hc)

/-- **Isaacs Problem 5A.7** (∀-形): `B`, `C` は `G` の cyclic 部分群で `BC = G`,
`B ∩ C ≠ 1`, `C ⊴ G` とする。`f : Γ →* G` が stem extension なら
`|ker f| < |C : G'|` (書籍の `|M(G)| < n`, `n = |C : G'|`)。

**証明**: `A := f⁻¹(C)`, `D := f⁻¹(B)` はいずれも可換 (`isMulCommutative_comap_of_isCyclic`)。
`Γ = D·A` なので, `x ∈ D ∩ A` は `D` の元とも `A` の元とも可換 ⇒ `x ∈ Z(Γ)`。
`B ∩ C > 1` の非自明元 `y` の逆像の元 `x` は `D ∩ A` に属し `f x = y ≠ 1` ゆえ
`x ∉ ker f`。よって `ker f ⊊ A ∩ Z(Γ)` で, 5A.5 の等式
`|A ∩ Z(Γ)| = |A : Γ'| = |C : G'|` と合わせて厳密不等式を得る。

書籍の注: 特に semidihedral 群と generalized quaternion 群の Schur 乗数は自明。 -/
theorem card_ker_lt_relIndex_commutator {Γ G : Type*} [Group Γ] [Group G] [Finite Γ]
    {f : Γ →* G} (hf : IsStemExtension f) {B C : Subgroup G} [C.Normal]
    (hB : IsCyclic ↥B) (hC : IsCyclic ↥C)
    (hBC : ∀ g : G, ∃ b ∈ B, ∃ c ∈ C, g = b * c) (hne : B ⊓ C ≠ ⊥) :
    Nat.card f.ker < (_root_.commutator G).relIndex C := by
  haveI := isCyclic_quotient_of_mul_eq_top hB hBC
  -- A = f⁻¹(C), D = f⁻¹(B) は可換
  have hAcomm := isMulCommutative_comap_of_isCyclic hf.ker_le_center hC
  have hDcomm := isMulCommutative_comap_of_isCyclic hf.ker_le_center hB
  have hAb : ∀ a ∈ C.comap f, ∀ b ∈ C.comap f, a * b = b * a :=
    forall_mul_comm_of_isMulCommutative hAcomm
  have hDb : ∀ a ∈ B.comap f, ∀ b ∈ B.comap f, a * b = b * a :=
    forall_mul_comm_of_isMulCommutative hDcomm
  -- Γ = D · A
  have hprod : ∀ γ : Γ, ∃ d ∈ B.comap f, ∃ a ∈ C.comap f, γ = d * a := by
    intro γ
    obtain ⟨b, hb, c, hc, hbc⟩ := hBC (f γ)
    obtain ⟨β, hβ⟩ := hf.surjective b
    refine ⟨β, Subgroup.mem_comap.mpr (hβ ▸ hb), β⁻¹ * γ, ?_, by group⟩
    rw [Subgroup.mem_comap, map_mul, map_inv, hβ, hbc]
    simpa using hc
  -- Γ/A は cyclic
  have hkercomp : ((QuotientGroup.mk' C).comp f).ker = C.comap f := by
    ext x
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp f) :=
    (QuotientGroup.mk'_surjective C).comp hf.surjective
  have hACyc : IsCyclic (Γ ⧸ C.comap f) := by
    have e : Γ ⧸ C.comap f ≃* G ⧸ C :=
      (QuotientGroup.quotientMulEquivOfEq hkercomp.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have hidx := relIndex_commutator_eq_card_inf_center hAb hACyc
  -- B ∩ C の非自明元を Γ へ持ち上げる
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨x, hx⟩ := hf.surjective (y : G)
  have hxD : x ∈ B.comap f := Subgroup.mem_comap.mpr (hx ▸ y.2.1)
  have hxA : x ∈ C.comap f := Subgroup.mem_comap.mpr (hx ▸ y.2.2)
  -- x は Γ の中心に入る
  have hxZ : x ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro γ
    obtain ⟨d, hd, a, ha, rfl⟩ := hprod γ
    calc d * a * x = d * (a * x) := by group
      _ = d * (x * a) := by rw [hAb _ ha _ hxA]
      _ = (d * x) * a := by group
      _ = (x * d) * a := by rw [hDb _ hd _ hxD]
      _ = x * (d * a) := by group
  -- x ∉ ker f
  have hxnk : x ∉ f.ker := by
    intro hmem
    exact hy (Subtype.ext (hx ▸ MonoidHom.mem_ker.mp hmem))
  -- ker f ⊊ A ∩ Z(Γ)
  have hkerA : f.ker ≤ C.comap f := fun z hz => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact C.one_mem
  have hkerle : f.ker ≤ C.comap f ⊓ Subgroup.center Γ := le_inf hkerA hf.ker_le_center
  have hlt : Nat.card f.ker < Nat.card (C.comap f ⊓ Subgroup.center Γ : Subgroup Γ) := by
    by_contra hcon
    have heq : f.ker = C.comap f ⊓ Subgroup.center Γ :=
      Subgroup.eq_of_le_of_card_ge hkerle (Nat.le_of_not_lt hcon)
    exact hxnk (heq ▸ Subgroup.mem_inf.mpr ⟨hxA, hxZ⟩)
  -- |C : G'| = |A : Γ'| = |A ∩ Z(Γ)|
  have htrans : (_root_.commutator G).relIndex C = (_root_.commutator Γ).relIndex (C.comap f) := by
    have hmap : (_root_.commutator Γ).map f = _root_.commutator G := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective f hf.surjective]
    have hcomap : (_root_.commutator G).comap f = _root_.commutator Γ := by
      rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.mpr hf.ker_le_commutator]
    rw [← hcomap, Subgroup.relIndex_comap (_root_.commutator G) f (C.comap f),
      Subgroup.map_comap_eq_self_of_surjective hf.surjective C]
  rw [htrans, hidx]
  exact hlt

/-! ### Problem 5A.8(a) -/

/-- **Isaacs Problem 5A.8(a)**: `f`, `g` がそれぞれ `A`, `B` の stem extension なら
`f × g` は `A × B` の stem extension。

`ker (f × g) = ker f × ker g` (`MonoidHom.ker_prodMap`) と
`Z(Γ × Δ) = Z(Γ) × Z(Δ)` (`Subgroup.center_prod`),
`(Γ × Δ)' = Γ' × Δ'` (`Subgroup.commutator_prod_prod` の `⊤` 特殊化) から直ちに従う。 -/
theorem isStemExtension_prodMap {Γ A Δ B : Type*} [Group Γ] [Group A] [Group Δ] [Group B]
    {f : Γ →* A} {g : Δ →* B} (hf : IsStemExtension f) (hg : IsStemExtension g) :
    IsStemExtension (f.prodMap g) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b⟩
    obtain ⟨x, hx⟩ := hf.surjective a
    obtain ⟨y, hy⟩ := hg.surjective b
    exact ⟨(x, y), by simp [hx, hy]⟩
  · have htop : ((⊤ : Subgroup Γ).prod (⊤ : Subgroup Δ)) = (⊤ : Subgroup (Γ × Δ)) :=
      Subgroup.top_prod_top
    have hcomm : _root_.commutator (Γ × Δ)
        = (_root_.commutator Γ).prod (_root_.commutator Δ) := by
      rw [_root_.commutator_def, ← htop, Subgroup.commutator_prod_prod, ← _root_.commutator_def,
        ← _root_.commutator_def]
    rw [MonoidHom.ker_prodMap, hcomm]
    exact Subgroup.prod_mono hf.ker_le_commutator hg.ker_le_commutator
  · rw [MonoidHom.ker_prodMap, Subgroup.center_prod]
    exact Subgroup.prod_mono hf.ker_le_center hg.ker_le_center

/-- 直積 stem extension の核の位数は各核の位数の積。

`isStemExtension_prodMap` と併せて **`|M(A × B)| ≥ |M(A)| |M(B)|`** (Problem 5A.8(a)) を与える:
`A`, `B` それぞれで核が最大の stem extension を取れば, その直積が `A × B` の stem extension
で核の位数は `|M(A)| |M(B)|`。 -/
theorem card_ker_prodMap {Γ A Δ B : Type*} [Group Γ] [Group A] [Group Δ] [Group B]
    (f : Γ →* A) (g : Δ →* B) :
    Nat.card (f.prodMap g).ker = Nat.card f.ker * Nat.card g.ker := by
  rw [MonoidHom.ker_prodMap, Nat.card_congr (Subgroup.prodEquiv f.ker g.ker).toEquiv,
    Nat.card_prod]

/-! ### Problem 5A.8(b) の準備 -/

/-- Sylow `p`-部分群が中心に含まれるなら `p ∤ |G'|`。

Burnside (mathlib `MonoidHom.transferSylow`) で `N = ker (transferSylow P)` を取ると
`G/N` は可換 (`↥P` が可換なので交換子は `N` に落ちる) ゆえ `G' ≤ N` で,
`p ∤ |N|` (`MonoidHom.not_dvd_card_ker_transferSylow`)。

Problem 5A.8(b) で「`Z ∩ ⁅Γ_A, Γ_A⁆` の素因数は `|A|` を割る」を示すのに使う。 -/
theorem not_dvd_card_commutator_of_sylow_le_center {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : (P : Subgroup G) ≤ Subgroup.center G) :
    ¬ p ∣ Nat.card (_root_.commutator G) := by
  have hnorm : Subgroup.normalizer (P : Subgroup G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_center_iff.mp (hP hy)) x).symm
  have hker : _root_.commutator G ≤ (MonoidHom.transferSylow P hnorm).ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    haveI : IsMulCommutative (P : Subgroup G) :=
      ⟨⟨fun u v => Subtype.ext (hnorm (Subgroup.le_normalizer v.2) u u.2)⟩⟩
    exact mul_comm (MonoidHom.transferSylow P hnorm a) (MonoidHom.transferSylow P hnorm b)
  intro hdvd
  exact MonoidHom.not_dvd_card_ker_transferSylow P hnorm
    (hdvd.trans (Subgroup.card_dvd_of_le hker))

end

end OddOrder.Isaacs.Ch05
