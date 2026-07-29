/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalClosure

/-!
# Isaacs §9D の演習 (書籍 p. 294)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9D
(subnormal closure / strong conjugacy 周辺)。

* **9D.1** `exists_unique_greatest_isSubnormal_le` — `X ≤ G` に対し「`X` の部分群であって
  `G` に subnormal なもの」のうち一意最大のもの (= **subnormal core** `subnormalCore X`)
  が存在し, それは `X` に normal。
* **9D.2** `isSubnormal_strongCore` / `normal_strongCore_subgroupOf` — `X` の強共役すべての
  交わり `L` (= `strongCore X`) は `X` に normal かつ `G` に **subnormal**。
  書籍 hint の `L^{(G)} ⊆ X` は `strongClosure_strongCore_le`。
* **9D.3** `subnormalCore_ne_sInf_conj` — `G = S₄`, `X = ⟨(0 1 2 3)⟩` では subnormal core
  (`= ⟨(0 2)(1 3)⟩`, 位数 2) は `X` の共役たちのどんな交わりでも書けない。

## 9D.1 について

subnormal closure (`strongClosure`, Thm 9.28 = Bartels) の双対。存在は
**Wielandt の結合定理の族版** (`Ch02.isSubnormal_sSup_of_isSubnormal`: 有限群では
subnormal 部分群の任意集合の `sSup` が subnormal) から直ちに従うので,
`subnormalCore X := sSup {S | S ≤ X ∧ S.IsSubnormal}` と定義してよい。

`X` での正規性は「共役 `(subnormalCore X)^x` (`x ∈ X`) も `X` に含まれる subnormal 部分群
だから最大性で `≤ subnormalCore X`」という定型。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

variable {G : Type*} [Group G]

section /- 9D.1: subnormal core の存在と X-正規性 (p. 294) -/

/-- **subnormal core** `X_{(G)}` (Isaacs Problem 9D.1, p. 294): `X` に含まれ `G` に
subnormal な部分群すべての join。

有限群では Wielandt の結合定理 (族版) によりこれ自身が subnormal なので,
「`X` の subnormal 部分群のうち最大のもの」になる。 -/
def subnormalCore (X : Subgroup G) : Subgroup G :=
  sSup {S : Subgroup G | S ≤ X ∧ S.IsSubnormal}

theorem subnormalCore_le (X : Subgroup G) : subnormalCore X ≤ X :=
  sSup_le fun _ hS => hS.1

/-- 最大性: `X` に含まれる subnormal 部分群は `subnormalCore X` に入る。 -/
theorem le_subnormalCore {X S : Subgroup G} (hSX : S ≤ X) (hS : S.IsSubnormal) :
    S ≤ subnormalCore X :=
  le_sSup ⟨hSX, hS⟩

/-- `subnormalCore X` 自身が `G` に subnormal (Wielandt の結合定理の族版)。 -/
theorem isSubnormal_subnormalCore [Finite G] (X : Subgroup G) :
    (subnormalCore X).IsSubnormal :=
  Ch02.isSubnormal_sSup_of_isSubnormal fun _ hS => hS.2

/-- `X` は `subnormalCore X` を正規化する: `x ∈ X` による共役も `X` に含まれる subnormal
部分群なので最大性で `subnormalCore X` に戻る。 -/
theorem le_normalizer_subnormalCore [Finite G] (X : Subgroup G) :
    X ≤ Subgroup.normalizer (subnormalCore X) := by
  have key : ∀ x ∈ X, (subnormalCore X).map (MulAut.conj x : G →* G) ≤ subnormalCore X := by
    intro x hx
    refine le_subnormalCore ?_
      (Subgroup.IsSubnormal.map (MulAut.conj x).surjective (isSubnormal_subnormalCore X))
    rintro _ ⟨y, hy, rfl⟩
    exact X.mul_mem (X.mul_mem hx (subnormalCore_le X hy)) (X.inv_mem hx)
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  -- 包含は上で得た。共役は単射なので位数が等しく, 包含から等号が出る。
  refine Subgroup.eq_of_le_of_card_ge (key x hx) (ge_of_eq ?_)
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj x : G →* G)
    (MulAut.conj x).injective).toEquiv).symm

/-- **9D.1 の後半**: subnormal core は `X` に normal。 -/
theorem normal_subnormalCore_subgroupOf [Finite G] (X : Subgroup G) :
    ((subnormalCore X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (subnormalCore_le X)).mpr
    (le_normalizer_subnormalCore X)

/-- **Isaacs Problem 9D.1** (書籍 p. 294) ⭐: `X ≤ G` に対し, `X` の部分群であって `G` に
subnormal なもののうち**一意最大**のもの (subnormal core) が存在する。

`subnormalCore X` がそれであり (`subnormalCore_le` / `isSubnormal_subnormalCore` /
`le_subnormalCore`), さらに `X` に normal (`normal_subnormalCore_subgroupOf`)。 -/
theorem exists_unique_greatest_isSubnormal_le [Finite G] (X : Subgroup G) :
    ∃! S : Subgroup G, (S ≤ X ∧ S.IsSubnormal) ∧
      ∀ T : Subgroup G, T ≤ X → T.IsSubnormal → T ≤ S := by
  refine ⟨subnormalCore X,
    ⟨⟨subnormalCore_le X, isSubnormal_subnormalCore X⟩, fun _ h₁ h₂ => le_subnormalCore h₁ h₂⟩,
    fun S hS => ?_⟩
  exact le_antisymm (le_subnormalCore hS.1.1 hS.1.2)
    (hS.2 _ (subnormalCore_le X) (isSubnormal_subnormalCore X))

end -- 9D.1

section /- 9D.2: 強共役全体の交わりは X に normal かつ G に subnormal (p. 294) -/

open scoped Pointwise

/-- **強共役核** `L`: `X` の強共役すべての交わり (`strongClosure` = `X^{(G)}` の双対)。

Isaacs Problem 9D.2 (p. 294) の主役。 -/
def strongCore (X : Subgroup G) : Subgroup G :=
  sInf {Y : Subgroup G | IsStronglyConjugate X Y}

theorem strongCore_le_of_isStronglyConjugate {X Y : Subgroup G}
    (h : IsStronglyConjugate X Y) : strongCore X ≤ Y :=
  sInf_le h

theorem strongCore_le (X : Subgroup G) : strongCore X ≤ X :=
  strongCore_le_of_isStronglyConjugate (IsStronglyConjugate.rfl X)

/-- `x ∈ X` による共役は `X` 自身を保つ。 -/
theorem conjAct_smul_eq_self_of_mem {X : Subgroup G} {y : G} (hy : y ∈ X) :
    ConjAct.toConjAct y • X = X :=
  (conjAct_smul_eq_map y X).trans
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy))

/-- `x ∈ X` による共役は `X` の強共役全体を置換するので, `L` を保つ。 -/
theorem smul_strongCore_le {X : Subgroup G} {x : G} (hx : x ∈ X) :
    ConjAct.toConjAct x • strongCore X ≤ strongCore X := by
  refine le_sInf fun Y hY => ?_
  have hconj : IsStronglyConjugate X (ConjAct.toConjAct x⁻¹ • Y) := by
    have h := hY.conjAct_smul (ConjAct.toConjAct x⁻¹)
    rwa [conjAct_smul_eq_self_of_mem (X.inv_mem hx)] at h
  have hle := (Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := ConjAct.toConjAct x)).mpr (strongCore_le_of_isStronglyConjugate hconj)
  rwa [map_inv, smul_inv_smul] at hle

/-- `X` は `L` を正規化する。 -/
theorem le_normalizer_strongCore (X : Subgroup G) :
    X ≤ Subgroup.normalizer (strongCore X) := by
  intro x hx
  have hge : strongCore X ≤ ConjAct.toConjAct x • strongCore X := by
    have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := ConjAct.toConjAct x)).mpr (smul_strongCore_le (X := X) (X.inv_mem hx))
    rwa [map_inv, smul_inv_smul] at h
  have heq : ConjAct.toConjAct x • strongCore X = strongCore X :=
    le_antisymm (smul_strongCore_le hx) hge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    ((conjAct_smul_eq_map x (strongCore X)).symm.trans heq)

/-- **9D.2 の hint** ⭐: `L^{(G)} ≤ X`。

`M = g • L` が `L` の強共役 (`g ∈ L ⊔ M`) なら, その関係を `g⁻¹` で共役して
`g ∈ L ⊔ (g⁻¹ • L)` を得る。`L ≤ X` なので `g⁻¹ ∈ X ⊔ (g⁻¹ • X)`, すなわち
**`g⁻¹ • X` は `X` の強共役**。ゆえに `L ≤ g⁻¹ • X`, つまり `M = g • L ≤ X`。 -/
theorem strongClosure_strongCore_le (X : Subgroup G) :
    strongClosure (strongCore X) ≤ X := by
  refine strongClosure_le fun M hM => ?_
  obtain ⟨g, hg, rfl⟩ := hM
  set c : ConjAct G := ConjAct.toConjAct g with hc
  -- `g ∈ L ⊔ c • L` を `c⁻¹` で共役して `g ∈ (c⁻¹ • L) ⊔ L`
  have hg' : g ∈ (c⁻¹ • strongCore X) ⊔ strongCore X := by
    have hmem : g ∈ c⁻¹ • (strongCore X ⊔ c • strongCore X) := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hc]
      simpa [ConjAct.toConjAct_smul] using hg
    rwa [conjAct_smul_sup, inv_smul_smul] at hmem
  -- ゆえに `g⁻¹ ∈ X ⊔ c⁻¹ • X`, すなわち `c⁻¹ • X` は `X` の強共役
  have hsub : (c⁻¹ • strongCore X) ⊔ strongCore X ≤ X ⊔ c⁻¹ • X :=
    sup_le (le_sup_of_le_right (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
        (strongCore_le X)))
      (le_sup_of_le_left (strongCore_le X))
  have hgX : g⁻¹ ∈ X ⊔ c⁻¹ • X := Subgroup.inv_mem _ (hsub hg')
  have hSC : IsStronglyConjugate X (c⁻¹ • X) := by
    refine ⟨g⁻¹, hgX, ?_⟩
    rw [hc, ← map_inv]
  -- `L ≤ c⁻¹ • X` を `c` で戻す
  have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := c)).mpr
    (strongCore_le_of_isStronglyConjugate hSC)
  rwa [smul_inv_smul] at h

/-- **Isaacs Problem 9D.2** (書籍 p. 294) ⭐: `X` の強共役すべての交わり `L` は
`X` に normal かつ `G` に **subnormal**。

subnormal 性: `L ≤ L^{(G)} ≤ X` (hint) と `L ◁ X` から `L ◁ L^{(G)}`, そして
`L^{(G)} ◁◁ G` (Theorem 9.28 = Bartels) なので `L ◁◁ G`。 -/
theorem isSubnormal_strongCore [Finite G] (X : Subgroup G) : (strongCore X).IsSubnormal := by
  refine Subgroup.IsSubnormal.step _ (strongClosure (strongCore X))
    (le_strongClosure _) (strongClosure_isSubnormal _) ?_
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (le_strongClosure _)).mpr ?_
  exact (strongClosure_strongCore_le X).trans (le_normalizer_strongCore X)

/-- **9D.2 の前半**: `L` は `X` に normal。 -/
theorem normal_strongCore_subgroupOf (X : Subgroup G) :
    ((strongCore X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (strongCore_le X)).mpr
    (le_normalizer_strongCore X)

end -- 9D.2

section /- 9D.3: subnormal core は共役の交わりでは書けない (S₄ の反例, p. 294) -/

open scoped Pointwise

-- `S₄` (24 元) 上の `decide` は既定の再帰深さを超えるので引き上げる。
set_option maxRecDepth 40000

/-- `S₄` の 4-サイクル `σ = (0 1 2 3)` (書籍 hint の `X` の生成元)。 -/
def sigma4 : Equiv.Perm (Fin 4) := c[(0 : Fin 4), 1, 2, 3]

/-- `τ = σ² = (0 2)(1 3)`。 -/
def tau4 : Equiv.Perm (Fin 4) := c[(0 : Fin 4), 2] * c[(1 : Fin 4), 3]

/-- 共役に使う互換 `(0 1)`。 -/
def swap4 : Equiv.Perm (Fin 4) := c[(0 : Fin 4), 1]

/-- `σ · (0 1)σ(0 1)⁻¹` — 位数 3 の元 (実際は 3-サイクル)。 -/
def order3elt4 : Equiv.Perm (Fin 4) := sigma4 * (swap4 * sigma4 * swap4⁻¹)

/-- `S₄` の Klein 四元群 `V₄` (恒等写像と 3 つの二重互換)。 -/
def kleinFour4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {g | g = 1 ∨ g = c[(0 : Fin 4), 1] * c[(2 : Fin 4), 3] ∨
    g = c[(0 : Fin 4), 2] * c[(1 : Fin 4), 3] ∨ g = c[(0 : Fin 4), 3] * c[(1 : Fin 4), 2]}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

instance : DecidablePred (· ∈ kleinFour4) := fun g =>
  decidable_of_iff (g = 1 ∨ g = c[(0 : Fin 4), 1] * c[(2 : Fin 4), 3] ∨
    g = c[(0 : Fin 4), 2] * c[(1 : Fin 4), 3] ∨ g = c[(0 : Fin 4), 3] * c[(1 : Fin 4), 2]) Iff.rfl

instance : kleinFour4.Normal := ⟨by decide⟩

/-- 書籍 hint の `X`: `S₄` の位数 4 の巡回部分群 `⟨σ⟩`。 -/
def cyclicFour4 : Subgroup (Equiv.Perm (Fin 4)) := Subgroup.zpowers sigma4

theorem sigma4_sq : sigma4 ^ 2 = tau4 := by decide

theorem tau4_ne_one : tau4 ≠ 1 := by decide

theorem tau4_sq : tau4 ^ 2 = 1 := by decide

theorem tau4_mem_kleinFour4 : tau4 ∈ kleinFour4 := by decide

theorem order3elt4_cube : order3elt4 ^ 3 = 1 := by decide

theorem order3elt4_ne_one : order3elt4 ≠ 1 := by decide

theorem orderOf_tau4 : orderOf tau4 = 2 := orderOf_eq_prime tau4_sq tau4_ne_one

theorem orderOf_sigma4 : orderOf sigma4 = 4 := by
  have h1 : ¬ sigma4 ^ (2 ^ 1) = 1 := by rw [pow_one, sigma4_sq]; exact tau4_ne_one
  have h2 : sigma4 ^ (2 ^ (1 + 1)) = 1 := by decide
  simpa using orderOf_eq_prime_pow h1 h2

theorem card_cyclicFour4 : Nat.card ↥cyclicFour4 = 4 := by
  rw [cyclicFour4, Nat.card_zpowers, orderOf_sigma4]

theorem card_zpowers_tau4 : Nat.card ↥(Subgroup.zpowers tau4) = 2 := by
  rw [Nat.card_zpowers, orderOf_tau4]

theorem zpowers_tau4_le_cyclicFour4 : Subgroup.zpowers tau4 ≤ cyclicFour4 :=
  Subgroup.zpowers_le.mpr (by rw [← sigma4_sq]; exact pow_mem (Subgroup.mem_zpowers _) 2)

/-- `V₄` は `⟨τ⟩` を正規化する (`V₄` は可換)。 -/
theorem kleinFour4_le_normalizer_zpowers_tau4 :
    kleinFour4 ≤ Subgroup.normalizer (Subgroup.zpowers tau4) := by
  have hc : ∀ h : Equiv.Perm (Fin 4), h ∈ kleinFour4 → tau4 * h = h * tau4 := by decide
  intro g hg
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨n, rfl⟩
  exact Commute.zpow_left (hc g hg) n

/-- `⟨τ⟩ ◁◁ S₄` (`⟨τ⟩ ◁ V₄ ◁ S₄`)。 -/
theorem isSubnormal_zpowers_tau4 : (Subgroup.zpowers tau4).IsSubnormal := by
  have hle : Subgroup.zpowers tau4 ≤ kleinFour4 :=
    Subgroup.zpowers_le.mpr tau4_mem_kleinFour4
  exact Subgroup.IsSubnormal.step _ kleinFour4 hle
    (Subgroup.Normal.isSubnormal inferInstance)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      kleinFour4_le_normalizer_zpowers_tau4)

/-- **`X = ⟨σ⟩` は `S₄` で subnormal でない**。

subnormal なら `X` は 2-群ゆえ `X ≤ O_2(S₄)` (`le_oPiCore_of_isSubnormal`)。`O_2(S₄)` は
正規なので `σ` の共役も含み, `σ · (0 1)σ(0 1)⁻¹` は **位数 3**。2-群に位数 3 の元は無い。 -/
theorem not_isSubnormal_cyclicFour4 : ¬ cyclicFour4.IsSubnormal := by
  intro hsn
  have hpg4 : IsPGroup 2 ↥cyclicFour4 :=
    IsPGroup.of_card (n := 2) (by rw [card_cyclicFour4]; norm_num)
  have hpi : Subgroup.IsPiSubgroup ({2} : Set ℕ) cyclicFour4 :=
    Subgroup.isPiSubgroup_of_isPGroup_of_mem hpg4 rfl
  have hle := OddOrder.GroupTheory.le_oPiCore_of_isSubnormal hsn hpi
  have hσ : sigma4 ∈ Ch03.oPiCore ({2} : Set ℕ) (Equiv.Perm (Fin 4)) :=
    hle (Subgroup.mem_zpowers _)
  have hconj : swap4 * sigma4 * swap4⁻¹ ∈ Ch03.oPiCore ({2} : Set ℕ) (Equiv.Perm (Fin 4)) :=
    (Ch03.oPiCore.normal _ _).conj_mem _ hσ swap4
  have hz : order3elt4 ∈ Ch03.oPiCore ({2} : Set ℕ) (Equiv.Perm (Fin 4)) :=
    Subgroup.mul_mem _ hσ hconj
  have hpg : IsPGroup 2 ↥(Ch03.oPiCore ({2} : Set ℕ) (Equiv.Perm (Fin 4))) :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton (Ch03.oPiCore.isPiGroup _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hpg ⟨order3elt4, hz⟩
  have hord : orderOf (⟨order3elt4, hz⟩ :
      ↥(Ch03.oPiCore ({2} : Set ℕ) (Equiv.Perm (Fin 4)))) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime order3elt4_cube order3elt4_ne_one
  rw [hord] at hk
  have h3 : (3 : ℕ) ∣ 2 ^ k := hk ▸ dvd_rfl
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

/-- **subnormal core の計算**: `subnormalCore ⟨σ⟩ = ⟨τ⟩` (位数 2)。 -/
theorem subnormalCore_cyclicFour4 : subnormalCore cyclicFour4 = Subgroup.zpowers tau4 := by
  have hle : Subgroup.zpowers tau4 ≤ subnormalCore cyclicFour4 :=
    le_subnormalCore zpowers_tau4_le_cyclicFour4 isSubnormal_zpowers_tau4
  have hdvd1 : (2 : ℕ) ∣ Nat.card ↥(subnormalCore cyclicFour4) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [card_zpowers_tau4] at this
  have hdvd2 : Nat.card ↥(subnormalCore cyclicFour4) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (subnormalCore_le cyclicFour4)
    rwa [card_cyclicFour4] at this
  have hne4 : Nat.card ↥(subnormalCore cyclicFour4) ≠ 4 := by
    intro h4
    refine not_isSubnormal_cyclicFour4 ?_
    have heq : subnormalCore cyclicFour4 = cyclicFour4 :=
      Subgroup.eq_of_le_of_card_ge (subnormalCore_le _) (by rw [h4, card_cyclicFour4])
    rw [← heq]
    exact isSubnormal_subnormalCore _
  have hmem : Nat.card ↥(subnormalCore cyclicFour4) ∈ Nat.divisors 4 :=
    Nat.mem_divisors.mpr ⟨hdvd2, by norm_num⟩
  have hdiv4 : Nat.divisors 4 = {1, 2, 4} := by rfl
  rw [hdiv4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hcard2 : Nat.card ↥(subnormalCore cyclicFour4) = 2 := by
    rcases hmem with h | h | h
    · rw [h] at hdvd1; omega
    · exact h
    · exact absurd h hne4
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, card_zpowers_tau4])).symm

/-- `X` の共役は `⟨gσg⁻¹⟩`。 -/
theorem conjAct_smul_cyclicFour4 (g : Equiv.Perm (Fin 4)) :
    ConjAct.toConjAct g • cyclicFour4 = Subgroup.zpowers (g * sigma4 * g⁻¹) := by
  rw [conjAct_smul_eq_map, cyclicFour4, MonoidHom.map_zpowers]
  rfl

/-- `σ` と可換な位数 `≤ 2` の元は `1` か `τ` (`C_{S₄}(σ) = ⟨σ⟩` の帰結)。 -/
theorem eq_one_or_tau4_of_commute_sigma4 (x : Equiv.Perm (Fin 4))
    (hc : x * sigma4 = sigma4 * x) (h2 : x ^ 2 = 1) : x = 1 ∨ x = tau4 := by
  revert hc h2; revert x; decide

/-- `τ` と可換な元は `σ` を `σ` か `σ⁻¹` に写す (`C_{S₄}(τ) = N_{S₄}(⟨σ⟩)`)。 -/
theorem conj_sigma4_of_commute_tau4 (g : Equiv.Perm (Fin 4)) (hc : g * tau4 = tau4 * g) :
    g * sigma4 * g⁻¹ = sigma4 ∨ g * sigma4 * g⁻¹ = sigma4⁻¹ := by
  revert hc; revert g; decide

/-- **`⟨τ⟩` を含む `X` の共役は `X` 自身だけ** — 9D.3 の要。 -/
theorem conjAct_smul_cyclicFour4_eq (g : Equiv.Perm (Fin 4))
    (h : Subgroup.zpowers tau4 ≤ ConjAct.toConjAct g • cyclicFour4) :
    ConjAct.toConjAct g • cyclicFour4 = cyclicFour4 := by
  rw [conjAct_smul_cyclicFour4] at h ⊢
  -- `τ ∈ ⟨ρ⟩` なので `τ` は `ρ = gσg⁻¹` と可換
  obtain ⟨n, hn⟩ := Subgroup.zpowers_le.mp h
  have hcomm : tau4 * (g * sigma4 * g⁻¹) = (g * sigma4 * g⁻¹) * tau4 := by
    rw [← hn]; exact (Commute.refl _).zpow_left n
  -- `y = g⁻¹τg` は `σ` と可換で位数 2 ⟹ `y = τ` ⟹ `g` は `τ` と可換
  have hy : (g⁻¹ * tau4 * g) * sigma4 = sigma4 * (g⁻¹ * tau4 * g) := by
    have := congrArg (fun z => g⁻¹ * z * g) hcomm
    simpa [mul_assoc] using this
  have hy2 : (g⁻¹ * tau4 * g) ^ 2 = 1 := by
    rw [pow_two]
    calc g⁻¹ * tau4 * g * (g⁻¹ * tau4 * g) = g⁻¹ * (tau4 * tau4) * g := by group
      _ = 1 := by rw [← pow_two, tau4_sq]; group
  have hy1 : g⁻¹ * tau4 * g ≠ 1 := fun hcon => tau4_ne_one (by
    have : tau4 = g * (g⁻¹ * tau4 * g) * g⁻¹ := by group
    rw [this, hcon]; group)
  have hyτ : g⁻¹ * tau4 * g = tau4 :=
    (eq_one_or_tau4_of_commute_sigma4 _ hy hy2).resolve_left hy1
  have hgτ : g * tau4 = tau4 * g := by
    have hstep : g * (g⁻¹ * tau4 * g) = g * tau4 := by rw [hyτ]
    rw [show g * (g⁻¹ * tau4 * g) = tau4 * g by group] at hstep
    exact hstep.symm
  rcases conj_sigma4_of_commute_tau4 g hgτ with h' | h'
  · rw [h']; rfl
  · rw [h', Subgroup.zpowers_inv]; rfl

/-- **Isaacs Problem 9D.3** (書籍 p. 294) ⭐: `G = S₄`, `X = ⟨(0 1 2 3)⟩` (位数 4 の巡回群)
のとき, `X` の **subnormal core は `X` の共役たちのどんな交わりでも書けない**。

`subnormalCore X = ⟨τ⟩` (位数 2, `subnormalCore_cyclicFour4`) である一方,
共役の交わりは「空族なら `⊤`」「そうでなければ `⟨τ⟩` を含む共役はすべて `X` に等しい
(`conjAct_smul_cyclicFour4_eq`) ので `X` そのもの」しかありえず, どちらも位数 2 ではない。 -/
theorem subnormalCore_ne_sInf_conj (𝒞 : Set (Subgroup (Equiv.Perm (Fin 4))))
    (h𝒞 : ∀ Y ∈ 𝒞, ∃ g : Equiv.Perm (Fin 4), Y = ConjAct.toConjAct g • cyclicFour4) :
    sInf 𝒞 ≠ subnormalCore cyclicFour4 := by
  rw [subnormalCore_cyclicFour4]
  intro hcon
  rcases Set.eq_empty_or_nonempty 𝒞 with rfl | ⟨Y₀, hY₀⟩
  · -- 空族: `sInf ∅ = ⊤` は位数 24
    rw [sInf_empty] at hcon
    have h1 : sigma4 ∈ Subgroup.zpowers tau4 := hcon ▸ Subgroup.mem_top sigma4
    have h2 : Subgroup.zpowers sigma4 ≤ Subgroup.zpowers tau4 := Subgroup.zpowers_le.mpr h1
    have := Subgroup.card_dvd_of_le h2
    rw [← cyclicFour4, card_cyclicFour4, card_zpowers_tau4] at this
    omega
  · -- 非空: すべての元が `⟨τ⟩` を含むので `X` に等しく, `sInf = X` (位数 4)
    have hall : ∀ Y ∈ 𝒞, Y = cyclicFour4 := by
      intro Y hY
      obtain ⟨g, rfl⟩ := h𝒞 Y hY
      exact conjAct_smul_cyclicFour4_eq g (hcon ▸ sInf_le hY)
    have hX : sInf 𝒞 = cyclicFour4 :=
      le_antisymm (hall Y₀ hY₀ ▸ sInf_le hY₀) (le_sInf fun Y hY => (hall Y hY).ge)
    rw [hX] at hcon
    have hc2 : Nat.card ↥cyclicFour4 = Nat.card ↥(Subgroup.zpowers tau4) := by rw [hcon]
    rw [card_cyclicFour4, card_zpowers_tau4] at hc2
    omega

end -- 9D.3

end OddOrder.Isaacs.Ch09
