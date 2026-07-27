/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Index
import OddOrder.Isaacs.Ch06_FrobeniusActions.ThompsonPComplement
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_SylowMaximal

/-!
# Isaacs Problem 7C.1 — Thompson の normal `p`-complement 判定条件

**主張** (書籍 p. 210, Thompson): `P ∈ Syl_p(G)`, `p ≠ 2` で, `P` の**任意の**
characteristic 部分群 `X` について `N_G(X)/C_G(X)` が `p`-群なら, `G` は
normal `p`-complement をもつ。

本ファイルはまず, 証明の締めに使う道具

* `hasNormalPComplement_of_normal_pi'_of_isPGroup_quotient`:
  `M ⊴ G` が `p'`-群で `G/M` が `p`-群なら `M` は `G` の normal `p`-complement,

を用意する。
-/

namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section /- 7C.1: normal `p`-complement の組み立て道具 (p. 210) -/

/-- 部分群への `IsPGroup` の遺伝 (`⊤` に使う)。 -/
private theorem isPGroup_subgroup {H : Type*} [Group H] {p : ℕ} (hH : IsPGroup p H)
    (K : Subgroup H) : IsPGroup p K := by
  intro g
  obtain ⟨k, hk⟩ := hH (g : H)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

/-- **`M ⊴ G` が `p'`-群で `G/M` が `p`-群なら, `M` は `G` の normal `p`-complement**。

`G/M` は `p`-群なのでその Sylow `p`-部分群は `⊤` (`hasNormalPComplement_of_sylow_eq_top`),
したがって `G/M` は自明に normal `p`-complement をもち,
`hasNormalPComplement_of_quotient_of_isPiGroup_compl` で `G` に持ち上がる。 -/
theorem hasNormalPComplement_of_normal_pi'_of_isPGroup_quotient
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G} [M.Normal]
    (hM : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} M)
    (hQ : IsPGroup p (G ⧸ M)) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine hasNormalPComplement_of_quotient_of_isPiGroup_compl hM ?_
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p (G ⧸ M)))
  refine hasNormalPComplement_of_sylow_eq_top Q ?_
  exact (Q.is_maximal' (isPGroup_subgroup hQ ⊤) le_top).symm

/-! ### 7C.1 の局所条件 -/

/-- **Isaacs 7C.1 の局所条件**: `P` の characteristic 部分群 `X` すべてについて
`N_G(X)/C_G(X)` が `p`-群。

既存の `HasThompsonLocalPComplements` と同じく **ambient `G` の任意の部分群 `P`** に対して
定義する (Sylow に限定しない) — そうしないと部分群・同型への輸送補題が書けないため。

⚠ 商群 `↥N_G(X) ⧸ C_G(X).subgroupOf N_G(X)` ではなく**元ごとの形**
(`g ∈ N_G(X)` なら `g ^ p ^ k ∈ C_G(X)`) を採る: `Normal` インスタンスの証明を避けられ,
部分群への遺伝が「`N_H(X) ≤ N_G(X)` に仮説を当てるだけ」で済む。有限群では両者は同値。 -/
def CharLocalPControl (p : ℕ) (P : Subgroup G) : Prop :=
  ∀ X : Subgroup ↥P, X.Characteristic →
    ∀ g ∈ Subgroup.normalizer ((X.map P.subtype : Subgroup G) : Set G),
      ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer ((X.map P.subtype : Subgroup G) : Set G)

/-- 局所条件は `C_G(X) ≤ N_G(X)` の元については自明 (`k = 0`)。 -/
theorem CharLocalPControl.trivial_on_centralizer {p : ℕ} {P : Subgroup G}
    {X : Subgroup ↥P} {g : G}
    (hg : g ∈ Subgroup.centralizer ((X.map P.subtype : Subgroup G) : Set G)) :
    ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer ((X.map P.subtype : Subgroup G) : Set G) :=
  ⟨0, by simpa using hg⟩

/-! ### characteristic 部分群の同型による輸送 -/

/-- **群同型に沿って characteristic 部分群は characteristic に移る**。

`ϕ : B ≃* B` に対し `ψ := e.trans (ϕ.trans e.symm) : A ≃* A` を取ると
`X.map ψ = X` (characteristic) で, これを `e` で押し出すと `(X.map e).map ϕ = X.map e`。 -/
theorem characteristic_map_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (X : Subgroup A) [hX : X.Characteristic] : (X.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro ϕ
  have hψ : X.map (e.trans (ϕ.trans e.symm)).toMonoidHom = X :=
    Subgroup.characteristic_iff_map_eq.mp hX (e.trans (ϕ.trans e.symm))
  have hcomp : (ϕ.toMonoidHom.comp e.toMonoidHom) =
      e.toMonoidHom.comp (e.trans (ϕ.trans e.symm)).toMonoidHom := by
    ext x
    simp
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hψ]

/-! ### 局所条件の部分群への遺伝 (Case A で使う) -/

/-- `↥S ≃* ↥(S.map H.subtype)` と包含の合成の一致。 -/
private theorem subtype_comp_equivMapOfInjective (H : Subgroup G) (S : Subgroup ↥H) :
    (S.map H.subtype).subtype.comp
        (Subgroup.equivMapOfInjective S H.subtype H.subtype_injective).toMonoidHom =
      H.subtype.comp S.subtype := by
  ext x
  simp

/-- `X : Subgroup ↥S` の `G` への像は, `↥(S.map H.subtype)` 側へ移してから押し出しても同じ。 -/
private theorem map_equivMapOfInjective_map_subtype (H : Subgroup G) (S : Subgroup ↥H)
    (X : Subgroup ↥S) :
    (X.map (Subgroup.equivMapOfInjective S H.subtype H.subtype_injective).toMonoidHom).map
        (S.map H.subtype).subtype =
      (X.map S.subtype).map H.subtype := by
  rw [Subgroup.map_map, subtype_comp_equivMapOfInjective, ← Subgroup.map_map]

/-- **局所条件は部分群に遺伝する**: `S ≤ H ≤ G` について, ambient `G` での局所条件
(`S` の `G` への像に対するもの) は `↥H` の中での局所条件を導く。

`N_{↥H}(X) ≤ N_G(X^G)` なので仮説をそのまま当て, 得られた `C_G` の元を `↥H` に落とす。
`X : Subgroup ↥S` の characteristic 性は `characteristic_map_of_mulEquiv` で
`↥(S.map H.subtype)` 側へ運ぶ。 -/
theorem CharLocalPControl.of_subgroup {p : ℕ} (H : Subgroup G) {S : Subgroup ↥H}
    (hS : CharLocalPControl p (S.map H.subtype)) :
    CharLocalPControl (G := ↥H) p S := by
  intro X hX g hg
  haveI : X.Characteristic := hX
  set e := Subgroup.equivMapOfInjective S H.subtype H.subtype_injective with he
  haveI hX' : (X.map e.toMonoidHom).Characteristic := characteristic_map_of_mulEquiv e X
  have hmapeq := map_equivMapOfInjective_map_subtype H S X
  -- `g` を `G` に落とすと `N_G` に入る
  have hgG : (g : G) ∈ Subgroup.normalizer
      (((X.map S.subtype).map H.subtype : Subgroup G) : Set G) := by
    have := map_normalizer_le_normalizer_map H.subtype (X.map S.subtype)
      (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
    exact this
  obtain ⟨k, hk⟩ := hS (X.map e.toMonoidHom) hX' (g : G) (by rwa [hmapeq])
  rw [hmapeq] at hk
  refine ⟨k, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro a ha
  have haG : ((a : ↥H) : G) ∈ (((X.map S.subtype).map H.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hcomm := hk _ haG
  have hpow : (((g ^ p ^ k : ↥H)) : G) = (g : G) ^ p ^ k := by push_cast; rfl
  exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hpow]; exact hcomm)

/-! ### 指数の議論 (Case B step 3) -/

/-- **`[K : C ⊓ K]` が `p` 冪で, かつ `p ∤ [K : X]` なる `X ≤ C ⊓ K` があれば `K ≤ C`**。

`[K : C ⊓ K]` は `[K : X]` を割る (`X ≤ C ⊓ K ≤ K`) ので, `p` 冪でありながら `p` と
互いに素 ⟹ `1` ⟹ `K ≤ C`。7C.1 Case B で「`K/(K ⊓ C)` は `p`-群かつ `K/X` の商ゆえ
`p'`-群 ⟹ 自明」に使う。`p` の素数性は不要。 -/
theorem le_of_relIndex_eq_pow_of_not_dvd [Finite G] {K C X : Subgroup G}
    {p k : ℕ} (hXCK : X ≤ C ⊓ K)
    (hpow : C.relIndex K = p ^ k) (hcop : ¬ p ∣ X.relIndex K) :
    K ≤ C := by
  have hmul : X.relIndex (C ⊓ K) * (C ⊓ K).relIndex K = X.relIndex K :=
    Subgroup.relIndex_mul_relIndex X (C ⊓ K) K hXCK inf_le_right
  have hdvd : C.relIndex K ∣ X.relIndex K := by
    rw [← Subgroup.inf_relIndex_right C K, ← hmul]
    exact Dvd.intro_left _ rfl
  have hk0 : k = 0 := by
    by_contra hk
    exact hcop (dvd_trans (hpow ▸ dvd_pow_self p hk) hdvd)
  rw [hk0, pow_zero] at hpow
  exact Subgroup.relIndex_eq_one.mp hpow

end

end OddOrder.Isaacs.Ch07
