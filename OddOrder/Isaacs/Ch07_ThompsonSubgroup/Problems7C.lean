/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Index
import OddOrder.Isaacs.Ch05_Transfer.Problems5C4
import OddOrder.Isaacs.Ch05_Transfer.Problems5C13
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

/-- **`K ⊴ G` からの normal `p`-complement の持ち上げ**: `K` が normal `p`-complement をもち
`G/K` が `p`-群なら, `G` も normal `p`-complement をもつ。

`K` の normal `p`-complement `N` は `p'`-群かつ `K` に正規なので `O_{p'}(K)` に含まれ,
したがって `[K : O_{p'}(K)] ∣ [K : N] = |Syl_p(K)|` は `p`-冪。`O_{p'}(K)` は `K` の
characteristic 部分群ゆえ `G` に正規で, 位数は `p'`, 指数は
`[G : O_{p'}(K)] = [G:K]·[K:O_{p'}(K)]` も `p`-冪。 -/
theorem hasNormalPComplement_of_normal_of_isPGroup_quotient
    [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G} [K.Normal]
    (hK : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥K)
    (hQ : IsPGroup p (G ⧸ K)) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  set O : Subgroup ↥K := OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} ↥K with hO_def
  have hOpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} O :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥K) {q | q ≠ p}
  have hOp : ¬ p ∣ Nat.card ↥O := fun hdvd =>
    hOpi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩) rfl
  -- `[K : O]` は `p`-冪: `N ≤ O` かつ `[K : N] = |Q|`
  obtain ⟨N, hNnormal, hNcompl⟩ := hK
  haveI := hNnormal
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥K))
  have hNpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} N := by
    intro q hq
    rw [← (hNcompl Q).index_eq_card] at hq
    intro hqp
    subst q
    exact Q.not_dvd_index (Nat.dvd_of_mem_primeFactors hq)
  have hNO : N ≤ O := OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore hNpi
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hOidx : ∃ j : ℕ, O.index = p ^ j := by
    have hdvd : O.index ∣ p ^ m := by
      refine dvd_trans (Subgroup.index_dvd_of_le hNO) ?_
      rw [(hNcompl Q).symm.index_eq_card, hm]
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hOidx
  -- `M = O` を `G` の部分群として見る
  haveI hOchar : O.Characteristic := OddOrder.Isaacs.Ch03.oPiCore.characteristic _ _
  set M : Subgroup G := O.map K.subtype with hM_def
  haveI hMnormal : M.Normal := OddOrder.Isaacs.Ch05.normal_map_subtype_of_characteristic
  have hMcard : Nat.card ↥M = Nat.card ↥O :=
    (Nat.card_congr (Subgroup.equivMapOfInjective O K.subtype K.subtype_injective).toEquiv).symm
  have hMK : M ≤ K := Subgroup.map_subtype_le O
  have hMrel : M.relIndex K = O.index := by
    rw [hM_def, Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hMidx : M.index = p ^ (j + n) := by
    rw [← Subgroup.relIndex_mul_index hMK, hMrel, hj, Subgroup.index_eq_card, hn, pow_add]
  exact OddOrder.Isaacs.Ch05.hasNormalPComplement_of_normal_of_index_eq_pow
    (hMcard ▸ hOp) hMidx

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

/-! ### 局所条件の ambient 形 -/

/-- 局所条件を **ambient の部分群 `Y ≤ P`** に対する形で使う (`Subgroup ↥P` を経由しない)。 -/
theorem CharLocalPControl.apply_of_le {p : ℕ} {P : Subgroup G} (h : CharLocalPControl p P)
    {Y : Subgroup G} (hYP : Y ≤ P) (hY : (Y.subgroupOf P).Characteristic)
    {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Y : Set G) := by
  have hmap : (Y.subgroupOf P).map P.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYP
  have := h (Y.subgroupOf P) hY g (by rw [hmap]; exact hg)
  rwa [hmap] at this

/-- ambient 形からの構成: `Y ≤ P` が `↥P` の characteristic 部分群であるものすべてについて
条件を確かめれば局所条件が成り立つ。 -/
theorem CharLocalPControl.of_ambient {p : ℕ} {P : Subgroup G}
    (h : ∀ Y : Subgroup G, Y ≤ P → (Y.subgroupOf P).Characteristic →
      ∀ g ∈ Subgroup.normalizer (Y : Set G),
        ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Y : Set G)) :
    CharLocalPControl p P := by
  intro X hX g hg
  have hsub : (X.map P.subtype).subgroupOf P = X :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective X
  exact h (X.map P.subtype) (Subgroup.map_subtype_le X) (by rw [hsub]; exact hX) g hg

/-! ### 局所条件の商への遺伝 (Case B step 2 で使う) -/

/-- **全射準同型に沿った characteristic 部分群の引き戻し**: `f : A →* B` が全射で `ker f` が
`A` の characteristic 部分群なら, `B` の characteristic 部分群 `K` の引き戻し `K.comap f` は
`A` の characteristic 部分群。

`φ : A ≃* A` は `ker f` を保つので `A ⧸ ker f ≃* B` を経由して `B` の自己同型 `ψ` に降り,
`ψ ∘ f = f ∘ φ` が成り立つ。 -/
theorem characteristic_comap_of_surjective {A B : Type*} [Group A] [Group B]
    {f : A →* B} (hf : Function.Surjective f) (hker : f.ker.Characteristic)
    {K : Subgroup B} (hK : K.Characteristic) : (K.comap f).Characteristic := by
  haveI := hker
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  have hφker : f.ker.map (φ : A →* A) = f.ker := Subgroup.characteristic_iff_map_eq.mp hker φ
  set e := QuotientGroup.quotientKerEquivOfSurjective f hf with he_def
  have he : ∀ a : A, e (QuotientGroup.mk a) = f a := fun _ => rfl
  have hψ : ∀ a : A,
      (e.symm.trans ((QuotientGroup.congr f.ker f.ker φ hφker).trans e)) (f a) = f (φ a) := by
    intro a
    have hsymm : e.symm (f a) = (QuotientGroup.mk a : A ⧸ f.ker) := by
      rw [← he a, e.symm_apply_apply]
    simp only [MulEquiv.trans_apply, hsymm, QuotientGroup.congr_mk, he]
  rintro _ ⟨a, ha, rfl⟩
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at ha ⊢
  have hmem := (Subgroup.characteristic_iff_map_le.mp hK
      (e.symm.trans ((QuotientGroup.congr f.ker f.ker φ hφker).trans e)))
    (Subgroup.mem_map_of_mem _ ha)
  simp only [MulEquiv.coe_toMonoidHom] at hmem
  rwa [hψ a] at hmem

/-- **局所条件は商に遺伝する** (Case B step 2)。

`X ⊴ G` が `P` の characteristic 部分群 (`X ≤ P`) なら, `G` での局所条件から
`G ⧸ X` の `P̄ = P/X` に対する局所条件が従う。

`Ȳ ≤ P̄` が `↥P̄` で characteristic なら, その引き戻し `Y = Ȳ` の `G` への preimage は
`X ≤ Y ≤ P` で `Y.subgroupOf P` は `↥P` で characteristic
(`characteristic_comap_of_surjective` を `↥P ↠ ↥P̄` に適用)。あとは
`N_{G/X}(Ȳ)` の元を `G` に持ち上げて仮説を当て, 得られた冪を商に落とす。 -/
theorem CharLocalPControl.quotient {p : ℕ} {P X : Subgroup G} [X.Normal]
    (hXP : X ≤ P) (hXchar : (X.subgroupOf P).Characteristic)
    (h : CharLocalPControl p P) :
    CharLocalPControl p (P.map (QuotientGroup.mk' X)) := by
  have hπsurj : Function.Surjective (QuotientGroup.mk' X) := QuotientGroup.mk'_surjective X
  have hker : (QuotientGroup.mk' X).ker = X := QuotientGroup.ker_mk' X
  refine CharLocalPControl.of_ambient ?_
  intro Ybar hYbarP hYbarChar gbar hgbar
  set Y : Subgroup G := Ybar.comap (QuotientGroup.mk' X) with hY_def
  -- `Y ≤ P` と `Y.map π = Ȳ`
  have hYP : Y ≤ P := by
    refine le_trans (Subgroup.comap_mono hYbarP) ?_
    rw [Subgroup.comap_map_eq_self (by rw [hker]; exact hXP)]
  have hYmap : Y.map (QuotientGroup.mk' X) = Ybar :=
    Subgroup.map_comap_eq_self_of_surjective hπsurj Ybar
  -- `Y.subgroupOf P` は `↥P` で characteristic
  have hYchar : (Y.subgroupOf P).Characteristic := by
    have hfker : ((QuotientGroup.mk' X).subgroupMap P).ker = X.subgroupOf P := by
      rw [Subgroup.ker_subgroupMap, hker]
    have hcomap : (Ybar.subgroupOf (P.map (QuotientGroup.mk' X))).comap
        ((QuotientGroup.mk' X).subgroupMap P) = Y.subgroupOf P := by
      ext x
      exact Iff.rfl
    rw [← hcomap]
    refine characteristic_comap_of_surjective (MonoidHom.subgroupMap_surjective _ _) ?_ hYbarChar
    rw [hfker]; exact hXchar
  -- `ḡ` を `G` に持ち上げる
  obtain ⟨g, rfl⟩ := hπsurj gbar
  have hgN : g ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hgbar ⊢
    intro n
    have h2 : (g * n * g⁻¹ ∈ Y) ↔
        (QuotientGroup.mk' X) g * (QuotientGroup.mk' X) n * ((QuotientGroup.mk' X) g)⁻¹ ∈ Ybar := by
      rw [hY_def, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    rw [show (n ∈ Y) ↔ (QuotientGroup.mk' X) n ∈ Ybar from Iff.rfl, h2]
    exact hgbar _
  obtain ⟨k, hk⟩ := h.apply_of_le hYP hYchar hgN
  refine ⟨k, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro ybar hybar
  have hmem : ybar ∈ Y.map (QuotientGroup.mk' X) := by rw [hYmap]; exact hybar
  obtain ⟨y, hyY, rfl⟩ := hmem
  rw [← map_pow, ← map_mul, ← map_mul, hk y hyY]

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
