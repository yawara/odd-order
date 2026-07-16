/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Basic

/-!
# Theorem315

Prefix-split from `OddOrder.Isaacs.Ch03_SplitExtensions.Main` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch03
open SemidirectProduct
open scoped Pointwise

section /- 3C: Hall theory (pp. 83-88) -/
variable {G : Type*} [Group G]


/-! **Isaacs Thm 3.15**: 全ての素数 `p` について `p`-complement (i.e., `{p}'`-Hall) が
存在 ⇒ `G` 可解.

**Forward dep**: Burnside `p^a q^b` 経由. Ch.7 完成後に back-fill.
所在: `OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean` (placeholder).
詳細は [`notes/isaacs/ch07_burnside.md`](../../notes/isaacs/ch07_burnside.md). -/

/-- **Isaacs Lemma 3.16**: `|G:H|`, `|G:K|` が coprime ⇒ `G = HK` (i.e., `H ⊔ K = ⊤`).

証明: `(H ⊔ K).index` は `H.index` と `K.index` の両方を割り切るので gcd を割り切る.
gcd は 1 なので `(H ⊔ K).index = 1`, 故に `H ⊔ K = ⊤`. -/
theorem sup_eq_top_of_coprime_index {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) : H ⊔ K = ⊤ := by
  have h1 : (H ⊔ K).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (H ⊔ K).index ∣ K.index := Subgroup.index_dvd_of_le le_sup_right
  have h_dvd : (H ⊔ K).index ∣ 1 := h ▸ Nat.dvd_gcd h1 h2
  exact Subgroup.index_eq_one.mp (Nat.dvd_one.mp h_dvd)

/-- **Isaacs Lemma 3.16 補助**: `|G:H|`, `|G:K|` が coprime なら
`|G : H ∩ K| = |G:H| · |G:K|`.

証明: `|G:H|`, `|G:K|` はともに `|G : H∩K|` を割り切るので coprime より積も割り切る.
逆向きの評価は `G/(H∩K) ↪ G/H × G/K` (mathlib `Subgroup.index_inf_le`). -/
theorem index_inf_eq_mul_of_coprime_index [Finite G] {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) :
    (H ⊓ K).index = H.index * K.index := by
  have h1 : H.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_left
  have h2 : K.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_right
  have h_dvd : H.index * K.index ∣ (H ⊓ K).index :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd h h1 h2
  have h_pos : 0 < (H ⊓ K).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact Nat.le_antisymm Subgroup.index_inf_le (Nat.le_of_dvd h_pos h_dvd)

/-- **Isaacs Lemma 3.16 (index clause)**: `|G:H|`, `|G:K|` が coprime なら
`|H : H ∩ K| = |G:K|` (mathlib 表記では `K.relIndex H`). -/
theorem relIndex_eq_index_of_coprime_index [Finite G] {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) :
    K.relIndex H = K.index := by
  have e1 : K.relIndex H * H.index = (H ⊓ K).index := by
    rw [← Subgroup.inf_relIndex_left]
    exact Subgroup.relIndex_mul_index inf_le_left
  rw [index_inf_eq_mul_of_coprime_index h, Nat.mul_comm H.index K.index] at e1
  have h_pos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact Nat.eq_of_mul_eq_mul_right h_pos e1

/-- **Isaacs Lemma 3.16 (set product)**: `|G:H|`, `|G:K|` が coprime なら `G = HK`
(**集合積**として; `sup_eq_top_of_coprime_index` より強い). Thm 3.17 の
`x = uv` 分解で使う. 証明は書籍どおり計数:
`|HK| · |H∩K| = |H| · |K|` (Ch.2 `card_set_mul_card_inf`) と
`|G : H∩K| = |G:H||G:K|` から `|HK| = |G|`. -/
theorem set_mul_eq_univ_of_coprime_index [Finite G] {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) :
    (H : Set G) * (K : Set G) = Set.univ := by
  have hcard := OddOrder.Isaacs.Ch02.card_set_mul_card_inf H K
  have e1 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
  have e2 : Nat.card ↥K * K.index = Nat.card G := Subgroup.card_mul_index K
  have e3 : Nat.card ↥(H ⊓ K) * (H ⊓ K).index = Nat.card G :=
    Subgroup.card_mul_index (H ⊓ K)
  rw [index_inf_eq_mul_of_coprime_index h] at e3
  have h_idx_pos : 0 < H.index * K.index :=
    Nat.mul_pos (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  -- `|H| · |K| = |G| · |H∩K|`
  have key : Nat.card ↥H * Nat.card ↥K = Nat.card G * Nat.card ↥(H ⊓ K) := by
    have hmul : (Nat.card ↥H * Nat.card ↥K) * (H.index * K.index) =
        (Nat.card G * Nat.card ↥(H ⊓ K)) * (H.index * K.index) := by
      calc (Nat.card ↥H * Nat.card ↥K) * (H.index * K.index)
          = (Nat.card ↥H * H.index) * (Nat.card ↥K * K.index) := by ring
        _ = Nat.card G * Nat.card G := by rw [e1, e2]
        _ = Nat.card G * (Nat.card ↥(H ⊓ K) * (H.index * K.index)) := by rw [e3]
        _ = (Nat.card G * Nat.card ↥(H ⊓ K)) * (H.index * K.index) := by ring
    exact Nat.eq_of_mul_eq_mul_right h_idx_pos hmul
  rw [key] at hcard
  have hHK : Nat.card ↥((H : Set G) * (K : Set G)) = Nat.card G :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
  rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hHK]

/-! **Isaacs Thm 3.17 Wielandt**: 3 部分群 pairwise coprime index + solvable ⇒ G solvable.

**Forward dep**: 単純群の場合分けで Burnside `p^a q^b` 必要. Ch.7 完成後に back-fill.
所在: `OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean` (placeholder). -/

end -- 3C

section /- 3D: π-separable + Hall-Higman (pp. 89-95) -/

variable {G : Type*} [Group G]

/-- **`π`-group**: `G` の全ての素因子が `π` に属す.

mathlib 未収載 (`IsPGroup` の π 版). `IsHallSubgroup π ⊤` と同値だが,
意図 (G 自体が π-group) を明示するため別名を導入. -/
def IsPiGroup (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ p ∈ (Nat.card G).primeFactors, p ∈ π

/-- 部分群版: `H ≤ G` が π-group (= `|H|` の全素因子が π). -/
def Subgroup.IsPiGroup (π : Set ℕ) (H : Subgroup G) : Prop :=
  ∀ p ∈ (Nat.card H).primeFactors, p ∈ π

/-- If `H` is a π-Hall subgroup, every π-subgroup has cardinality dividing `|H|`. -/
theorem IsHallSubgroup.card_dvd_of_isPiGroup [Finite G] {π : Set ℕ} {H S : Subgroup G}
    (hH : IsHallSubgroup π H) (hS : Subgroup.IsPiGroup π S) :
    Nat.card S ∣ Nat.card H := by
  have hS_dvd_G : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  have hcop : Nat.Coprime (Nat.card S) H.index := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hq_dvd
    have hq_S_pf : q ∈ (Nat.card S).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
    have hq_idx_pf : q ∈ H.index.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Subgroup.index_ne_zero_of_finite⟩
    exact hH.2 q hq_idx_pf (hS q hq_S_pf)
  have hG_eq : Nat.card G = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
  rw [hG_eq] at hS_dvd_G
  exact hcop.dvd_of_dvd_mul_right hS_dvd_G

/-- **π-radical** `O_π(G)`: `G` の正規 π-subgroup の sup (= 最大の正規 π-subgroup).

mathlib 未収載 (各 `opCore p G` の π 版 sup). Hall-Higman 1.2.3 で必須.
形式化都合で subtype 上の単層 iSup を採用. -/
def oPiCore (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨆ H : {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H}, (H.val : Subgroup G)

/-- `O_π(G)` は `G` の正規部分群 (正規部分群の sup). -/
instance oPiCore.normal (π : Set ℕ) (G : Type*) [Group G] : (oPiCore π G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ oPiCore π G) hn
    ?mem ?one ?mul
  case mem =>
    rintro ⟨H, hN, _⟩ x hx
    -- x ∈ H 正規 ⇒ g x g⁻¹ ∈ H ≤ oPiCore π G.
    have hHle : H ≤ oPiCore π G :=
      le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
        (K.val : Subgroup G)) ⟨H, hN, ‹_›⟩
    exact hHle (hN.conj_mem x hx g)
  case one => simp
  case mul =>
    intro x y hx hy
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (oPiCore π G).mul_mem hx hy

/-- `O_π(G)` は `G` で characteristic. mathlib `characteristic_iff_le_comap` 経由で
任意の自己同型 `φ : G ≃* G` で `oPiCore` の generator 各 `H` (normal π-group) の像
`H.map φ` も normal π-group ⇒ `≤ oPiCore` を使う.

Hall-Higman 3.21 の K char in C/B + C ⊴ G ⇒ K ⊴ G の経路で必須. -/
instance oPiCore.characteristic (π : Set ℕ) (G : Type*) [Group G] :
    (oPiCore π G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ
  refine iSup_le ?_
  rintro ⟨H, hHN, hHpi⟩ h hh
  rw [Subgroup.mem_comap]
  -- φ h ∈ H.map φ.toMonoidHom (which is normal + π-group) ≤ oPiCore π G.
  haveI hMapN : (H.map φ.toMonoidHom).Normal := hHN.map φ.toMonoidHom φ.surjective
  have hMapPi : Subgroup.IsPiGroup π (H.map φ.toMonoidHom) := by
    intro p hp
    have hcardEq : Nat.card ↥(H.map φ.toMonoidHom) = Nat.card ↥H :=
      Nat.card_congr (Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective).symm.toEquiv
    rw [hcardEq] at hp
    exact hHpi p hp
  have hMapMem : φ h ∈ H.map φ.toMonoidHom := ⟨h, hh, rfl⟩
  exact le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
    (K.val : Subgroup G)) ⟨H.map φ.toMonoidHom, hMapN, hMapPi⟩ hMapMem

/-! ### π-separable 群の正式定義 (Isaacs Def 3.18)

`G` は π-separable とは, 正規列 `⊥ = F₀ ⊴ F₁ ⊴ ... ⊴ Fₙ = ⊤` で各因子 `Fᵢ₊₁/Fᵢ` が
π-group または π'-group となるものが存在する場合をいう (Isaacs FGT p.89).

**実装**: mathlib の `IsSolvable` パターンに準拠して `piFittingSeries` (`⊥` から始まり
各ステップで `G/Fₙ` の π-radical と π'-radical の sup を pull back する) の停留条件として
定式化. `derivedSeries G n = ⊥` パターン参照.

各 `Fₙ` は subtype `{S // S.Normal}` 経由で再帰中に normal instance を確保. -/

private def piFittingSeriesAux (π : Set ℕ) (G : Type*) [Group G] :
    ℕ → {S : Subgroup G // S.Normal}
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let prev := piFittingSeriesAux π G n
    haveI : prev.val.Normal := prev.property
    ⟨Subgroup.comap (QuotientGroup.mk' prev.val)
        (oPiCore π (G ⧸ prev.val) ⊔ oPiCore {p | p ∉ π} (G ⧸ prev.val)),
     inferInstance⟩

/-- **π-Fitting series** of `G`: `F₀ = ⊥` から始まり, `Fₙ₊₁` は `G/Fₙ` 上の
`O_π(G/Fₙ) ⊔ O_{π'}(G/Fₙ)` の pullback. mathlib `derivedSeries`/`lowerCentralSeries`
パターンに準拠. `G` は π-separable iff この series が有限ステップで `⊤` に到達する. -/
def piFittingSeries (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) : Subgroup G :=
  (piFittingSeriesAux π G n).val

instance piFittingSeries.normal (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) :
    (piFittingSeries π G n).Normal :=
  (piFittingSeriesAux π G n).property

@[simp] theorem piFittingSeries_zero (π : Set ℕ) (G : Type*) [Group G] :
    piFittingSeries π G 0 = ⊥ := rfl

theorem piFittingSeries_succ (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) :
    piFittingSeries π G (n + 1) =
      Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
         oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) := rfl

theorem piFittingSeries_le_succ (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) :
    piFittingSeries π G n ≤ piFittingSeries π G (n + 1) := by
  intro g hg
  rw [piFittingSeries_succ, Subgroup.mem_comap]
  rw [show (QuotientGroup.mk' (piFittingSeries π G n) g : G ⧸ piFittingSeries π G n) = 1
        from (QuotientGroup.eq_one_iff g).mpr hg]
  exact (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
         oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)).one_mem

theorem piFittingSeries_monotone (π : Set ℕ) (G : Type*) [Group G] :
    Monotone (piFittingSeries π G) :=
  monotone_nat_of_le_succ (piFittingSeries_le_succ π G)

/-- **π-separable 群** (Isaacs Def 3.18): `G` の π-Fitting series が有限ステップで
`⊤` に到達する. これは `G` が π-group と π'-group の交互の正規列に分解できることと同値.

定式化は mathlib `IsSolvable` パターン (`exists_top : ∃ n, piFittingSeries π G n = ⊤`)
に準拠. -/
class IsPiSeparable (π : Set ℕ) (G : Type*) [Group G] : Prop where
  exists_top : ∃ n : ℕ, piFittingSeries π G n = ⊤

/-- **`IsPiGroup.le_oPiCore`**: 任意の normal π-subgroup は `oPiCore π G` に含まれる.
`le_iSup` の素直な実体化. Hall-Higman 等での頻用 helper. -/
theorem Subgroup.IsPiGroup.le_oPiCore {G : Type*} [Group G] {π : Set ℕ} {H : Subgroup G}
    [H.Normal] (hH : Subgroup.IsPiGroup π H) : H ≤ oPiCore π G :=
  le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
    (K.val : Subgroup G)) ⟨H, ‹_›, hH⟩

/-- **`⊥` は任意 π について π-group**: |⊥| = 1, primeFactors 1 = ∅. -/
theorem Subgroup.IsPiGroup.bot {G : Type*} [Group G] (π : Set ℕ) :
    Subgroup.IsPiGroup π (⊥ : Subgroup G) := by
  intro p hp
  simp at hp

/-- **IsPiGroup は subgroup inclusion で保持**: 有限 G で `H ≤ K` and `K` is π-group
⇒ `H` is π-group. `Nat.card ↥H ∣ Nat.card ↥K` で primeFactors 包含. -/
theorem Subgroup.IsPiGroup.le {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {H K : Subgroup G} (hHK : H ≤ K) (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π H := by
  intro p hp
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hHK
  exact hK p (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hp)

/-- A finite `p`-group is a `π`-group once `p ∈ π`. -/
theorem Subgroup.IsPiGroup.of_isPGroup_of_mem {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hH : IsPGroup p H) (hpπ : p ∈ π) :
    Subgroup.IsPiGroup π H := by
  intro q hq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := H)).mp hH
  rw [hn] at hq
  by_cases hn0 : n = 0
  · simp [hn0] at hq
  · rw [Nat.primeFactors_prime_pow hn0 Fact.out] at hq
    rw [Finset.mem_singleton] at hq
    rw [hq]
    exact hpπ

/-- **`oPiCore π G = ⊥` ⇒ G で normal π-subgroup は ⊥ のみ**.
`Subgroup.IsPiGroup.le_oPiCore` + `oPiCore = ⊥` の chain.

用途: Hall-Higman 3.21 case π' で `H ≤ O_π'(K) ⊴ G` + `O_π'(G) = ⊥` ⇒ `O_π'(K) = ⊥`,
よって H = ⊥ で Schur-Zassenhaus complement の存在と矛盾. -/
theorem eq_bot_of_isPiGroup_of_oPiCore_eq_bot {G : Type*} [Group G] (π : Set ℕ)
    {H : Subgroup G} [H.Normal] (hHpi : Subgroup.IsPiGroup π H)
    (hCore : oPiCore π G = ⊥) :
    H = ⊥ := by
  rw [eq_bot_iff, ← hCore]
  exact hHpi.le_oPiCore

/-- **`π` と `π'` の cardinality は互いに素**: `n` の素因子が全 `π` 内 + `m` の素因子
が全 `π` 外 ⇒ `Coprime n m`.

Hall-Higman 3.21 case π' で B π-group + K/B π'-group のとき Schur-Zassenhaus 適用
の前提 `Nat.Coprime |B| (K.index in K)` を得るための補題. -/
theorem Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {π : Set ℕ}
    (hnPi : ∀ p ∈ n.primeFactors, p ∈ π)
    (hmPi' : ∀ p ∈ m.primeFactors, p ∉ π) :
    Nat.Coprime n m := by
  rw [← Nat.disjoint_primeFactors hn hm, Finset.disjoint_left]
  intro p hp_n hp_m
  exact absurd (hnPi p hp_n) (hmPi' p hp_m)

/-- A `π`-subgroup has trivial intersection with a `p`-group for `p ∉ π`. -/
theorem Subgroup.IsPiGroup.inf_eq_bot_of_isPGroup_not_mem {G : Type*} [Group G]
    [Finite G] {π : Set ℕ} {K M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hK : Subgroup.IsPiGroup π K) (hM : IsPGroup p M) (hp_notπ : p ∉ π) :
    K ⊓ M = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  have hM_pi' : Subgroup.IsPiGroup {q | q ∉ π} M :=
    Subgroup.IsPiGroup.of_isPGroup_of_mem hM hp_notπ
  have hdvdK : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdM : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card K) (Nat.card M) :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hK hM_pi'
  have hdvd_gcd : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.gcd (Nat.card K) (Nat.card M) :=
    Nat.dvd_gcd hdvdK hdvdM
  rw [hcop] at hdvd_gcd
  exact Nat.dvd_one.mp hdvd_gcd

/-- Complementary Hall subgroups have coprime orders. -/
theorem IsHallSubgroup.card_coprime_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Nat.Coprime (Nat.card K) (Nat.card H) := by
  have hHK : Nat.Coprime (Nat.card H) (Nat.card K) :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne'
      hH.1
      (fun p hp => by simpa using hK.1 p hp)
  exact hHK.symm

/-- The index of a `π'`-Hall subgroup and the index of a `π`-Hall subgroup are coprime. -/
theorem IsHallSubgroup.index_coprime_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Nat.Coprime K.index H.index := by
  refine Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite ?_ hH.2
  intro p hp
  by_contra hp_not
  exact hK.2 p hp hp_not

/-- If `K` is Hall `π'` and `H` is Hall `π`, then `|K| * |H| = |G|`. -/
theorem IsHallSubgroup.card_mul_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Nat.card K * Nat.card H = Nat.card G := by
  have h_card_cop : Nat.Coprime (Nat.card K) (Nat.card H) :=
    hK.card_coprime_of_compl hH
  have h_index_cop : Nat.Coprime H.index K.index :=
    (hK.index_coprime_of_compl hH).symm
  have hK_dvd_Hindex : Nat.card K ∣ H.index := by
    have hdiv : Nat.card K ∣ Nat.card H * H.index := by
      rw [Subgroup.card_mul_index H]
      exact Subgroup.card_subgroup_dvd_card K
    rw [mul_comm] at hdiv
    exact h_card_cop.dvd_of_dvd_mul_right hdiv
  have hHindex_dvd_K : H.index ∣ Nat.card K := by
    have hdivG : H.index ∣ Nat.card G :=
      ⟨Nat.card H, by rw [mul_comm, Subgroup.card_mul_index H]⟩
    have hdiv : H.index ∣ Nat.card K * K.index := by
      rwa [← Subgroup.card_mul_index K] at hdivG
    exact h_index_cop.dvd_of_dvd_mul_right hdiv
  have hK_card_eq : Nat.card K = H.index :=
    Nat.dvd_antisymm hK_dvd_Hindex hHindex_dvd_K
  calc
    Nat.card K * Nat.card H = H.index * Nat.card H := by rw [hK_card_eq]
    _ = Nat.card H * H.index := by rw [mul_comm]
    _ = Nat.card G := Subgroup.card_mul_index H

/-- Complementary Hall subgroups form an internal complement pair. -/
theorem IsHallSubgroup.isComplement_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Subgroup.IsComplement' K H :=
  Subgroup.isComplement'_of_coprime (hK.card_mul_of_compl hH)
    (hK.card_coprime_of_compl hH)

/-- **Hall-Higman 3.21 case π core**: `K ⊴ G` π-group + `K ≤ C_G(O_π(G))` ⇒
`K ≤ C_G(O_π(G)) ⊓ O_π(G)`.

`oPiCore π G` の極大性 (`IsPiGroup.le_oPiCore`) で `K ≤ oPiCore π G`,
これと仮定 `K ≤ centralizer` から inf に入る. 1-liner.

**用途**: Hall-Higman 3.21 case π で `K/B ⊆ C/B π-group ⇒ K ⊆ C ⊓ O = B`,
これと `B < K` で矛盾 (K = preimage of nontrivial K' で `B < K` を担保). -/
theorem hall_higman_case_pi_K_le_B {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    {K : Subgroup G} [K.Normal] (hKpi : Subgroup.IsPiGroup π K)
    (hKC : K ≤ Subgroup.centralizer (oPiCore π G : Set G)) :
    K ≤ Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G :=
  le_inf hKC hKpi.le_oPiCore

/-- **IsPiGroup は MulEquiv (group iso) で保持**: `K ≃* K.map φ.toMonoidHom`
(`equivMapOfInjective`) で cardinality 同じ. -/
theorem Subgroup.IsPiGroup.map_equiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {π : Set ℕ} {K : Subgroup G} (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π (K.map φ.toMonoidHom) := by
  intro p hp
  have hcard : Nat.card ↥(K.map φ.toMonoidHom) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective).symm.toEquiv
  rw [hcard] at hp
  exact hK p hp

/-- A `π`-subgroup remains a `π`-subgroup after mapping to a quotient. -/
theorem Subgroup.IsPiGroup.map_quotient {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {N K : Subgroup G} [N.Normal] (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' N)) := by
  intro p hp
  apply hK
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩

/-- **IsPiGroup は subgroupOf で保持**: `B ≤ K ≤ G` で `B` が π-group (as `Subgroup G`)
⇒ `B.subgroupOf K` も π-group (as `Subgroup ↥K`).

mathlib `subgroupOfEquivOfLe` で `↥(B.subgroupOf K) ≃* ↥B`, よって cardinality 同じ
⇒ primeFactors 同じ. -/
theorem Subgroup.IsPiGroup.subgroupOf {G : Type*} [Group G] {π : Set ℕ}
    {B K : Subgroup G} (hBK : B ≤ K) (hB : Subgroup.IsPiGroup π B) :
    Subgroup.IsPiGroup π (B.subgroupOf K) := by
  intro p hp
  have hcard : Nat.card ↥(B.subgroupOf K) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  rw [hcard] at hp
  exact hB p hp

/-- A complement to a `π'`-subgroup is a Hall `π`-subgroup of the ambient subgroup. -/
theorem isHallSubgroup_subgroupOf_of_complement_pi_pi' [Finite G] {π : Set ℕ}
    {U H M : Subgroup G} (hH_le_U : H ≤ U) (hM_le_U : M ≤ U)
    (hH_pi : Subgroup.IsPiGroup π H)
    (hM_pi' : Subgroup.IsPiGroup {p | p ∉ π} M)
    (hComp : Subgroup.IsComplement' (M.subgroupOf U) (H.subgroupOf U)) :
    IsHallSubgroup π (H.subgroupOf U) := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.IsPiGroup.subgroupOf hH_le_U hH_pi
  · have hMsub_pi' : Subgroup.IsPiGroup {p | p ∉ π} (M.subgroupOf U) :=
      Subgroup.IsPiGroup.subgroupOf hM_le_U hM_pi'
    intro q hq hq_pi
    rw [hComp.index_eq_card] at hq
    exact hMsub_pi' q hq hq_pi

/-- **π-group extension**: `N ⊴ H` で `N` も `H/N` も π-group ⇒ `H` は π-group.
mathlib `card_eq_card_quotient_mul_card_subgroup` (`|H| = |H/N| * |N|`) +
`primeFactors_mul` で primes |H| ⊆ primes |H/N| ∪ primes |N| ⊆ π. -/
theorem IsPiGroup.of_normal_quotient {H : Type*} [Group H] [Finite H]
    {π : Set ℕ} (N : Subgroup H) [N.Normal]
    (hN : ∀ p ∈ (Nat.card ↥N).primeFactors, p ∈ π)
    (hQ : ∀ p ∈ (Nat.card (H ⧸ N)).primeFactors, p ∈ π) :
    IsPiGroup π H := by
  intro p hp
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N] at hp
  rw [Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hp
  rcases Finset.mem_union.mp hp with h | h
  · exact hQ p h
  · exact hN p h

/-- **2 つの normal π-subgroup の sup も π-subgroup**: 有限群 `G` で `H₁, H₂ ⊴ G`
が共に π-group ⇒ `H₁ ⊔ H₂` も π-group.

**証明**: `|H₁ ⊔ H₂| · |H₁ ⊓ H₂| = |H₁| · |H₂|` (`card_HK_mul_card_inf_eq_card_mul_card`
in `OddOrder/Mathlib/Subgroup`) + `(H₁ ⊔ H₂ : Set G) = ↑H₁ * ↑H₂` (normal で
`mem_sup_of_normal_left`) で `|H₁ ⊔ H₂| ∣ |H₁| · |H₂|`. primeFactors monotone +
primeFactors_mul で結論.

**用途**: `oPiCore.isPiGroup` (Hall-Higman 3.21 critical bottleneck) の closure step. -/
theorem Subgroup.IsPiGroup.sup_of_normal {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {H K : Subgroup G} [H.Normal] [K.Normal]
    (hH : Subgroup.IsPiGroup π H) (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π (H ⊔ K) := by
  intro p hp
  -- Step 1: Nat.card ↥(H ⊔ K) = Nat.card (↑H * ↑K : Set G) via mem_sup_of_normal_left.
  have hcard_eq : Nat.card ↥(H ⊔ K) = Nat.card (↑H * ↑K : Set G) := by
    refine Nat.card_congr ⟨fun x => ⟨x.val, ?_⟩, fun y => ⟨y.val, ?_⟩,
        fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp x.2
      exact ⟨a, ha, b, hb, hab⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := y.2
      rw [← hab]
      exact Subgroup.mul_mem_sup ha hb
  -- Step 3: Nat.card (↑H * ↑K : Set G) ∣ Nat.card ↥H * Nat.card ↥K.
  have hHKformula : Nat.card (↑H * ↑K : Set G) * Nat.card ↥(H ⊓ K)
      = Nat.card H * Nat.card K :=
    Subgroup.card_HK_mul_card_inf_eq_card_mul_card H K
  have hdvd : Nat.card ↥(H ⊔ K) ∣ Nat.card ↥H * Nat.card ↥K := by
    rw [hcard_eq]
    exact ⟨_, hHKformula.symm⟩
  -- Step 4: primeFactors of |H ⊔ K| ⊆ primeFactors of (|H| * |K|).
  have hne : Nat.card ↥H * Nat.card ↥K ≠ 0 :=
    mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  have hsubset : (Nat.card ↥(H ⊔ K)).primeFactors
      ⊆ (Nat.card ↥H * Nat.card ↥K).primeFactors :=
    Nat.primeFactors_mono hdvd hne
  rw [Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hsubset
  rcases Finset.mem_union.mp (hsubset hp) with hpH | hpK
  · exact hH p hpH
  · exact hK p hpK

/-- A normal π-subgroup is contained in every π-Hall subgroup. -/
theorem Subgroup.IsPiGroup.normal_le_hall {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {N H : Subgroup G} [N.Normal] (hN : Subgroup.IsPiGroup π N)
    (hH : IsHallSubgroup π H) :
    N ≤ H := by
  have hSup_pi : Subgroup.IsPiGroup π (H ⊔ N : Subgroup G) := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq_prime, hq_dvd, _⟩ := hq
    have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) * Nat.card ↥(H ⊓ N : Subgroup G)
        = Nat.card ↥H * Nat.card ↥N := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card H N
      rwa [show (↑H * ↑N : Set G) = ↑(H ⊔ N : Subgroup G) from
        (Subgroup.mul_normal H N).symm] at h_hk
    have h_dvd_prod : q ∣ Nat.card ↥H * Nat.card ↥N := by
      rw [← h_card_eq]
      exact hq_dvd.mul_right _
    rcases hq_prime.dvd_mul.mp h_dvd_prod with hH_dvd | hN_dvd
    · exact hH.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hH_dvd, Nat.card_pos.ne'⟩)
    · exact hN q (Nat.mem_primeFactors.mpr ⟨hq_prime, hN_dvd, Nat.card_pos.ne'⟩)
  have h_card_dvd : Nat.card ↥(H ⊔ N : Subgroup G) ∣ Nat.card ↥H :=
    hH.card_dvd_of_isPiGroup hSup_pi
  have hH_le_sup : H ≤ H ⊔ N := le_sup_left
  have h_card_ge : Nat.card ↥H ≤ Nat.card ↥(H ⊔ N : Subgroup G) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hH_le_sup)
  have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) = Nat.card ↥H :=
    Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_card_dvd) h_card_ge
  have h_sup_eq : (H ⊔ N : Subgroup G) = H :=
    (Subgroup.eq_of_le_of_card_ge hH_le_sup h_card_eq.le).symm
  intro x hx
  have hx_sup : x ∈ (H ⊔ N : Subgroup G) := Subgroup.mem_sup_right hx
  rwa [h_sup_eq] at hx_sup

/-- **`oPiCore.isPiGroup`** ⭐ (Hall-Higman 3.21 critical bottleneck):
有限 `G` で `oPiCore π G` は π-group.

**証明** (~30 LOC): `Finset.sup_induction` を predicate `H ↦ H.Normal ∧ IsPiGroup π H`
で適用.
- iSup = Finset.sup over finite indexing (`Subgroup G` is Fintype for finite G).
- bot: trivially normal + π-group (primeFactors 1 = ∅).
- closure: `H₁, H₂ ⊴ G + π-group ⇒ H₁ ⊔ H₂ ⊴ G + π-group` (mathlib + `IsPiGroup.sup_of_normal`).
- generators: each subtype element has the predicate by construction. -/
theorem oPiCore.isPiGroup [Finite G] (π : Set ℕ) :
    Subgroup.IsPiGroup π (oPiCore π G) := by
  classical
  haveI hSubF : Fintype {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H} :=
    Fintype.ofFinite _
  -- The iSup over the subtype equals Finset.univ.sup.
  set p : Subgroup G → Prop := fun H => H.Normal ∧ Subgroup.IsPiGroup π H with hp_def
  -- Step: show p holds for oPiCore.
  have hgoal : p (oPiCore π G) := by
    change p (⨆ H : {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H},
        (H.val : Subgroup G))
    have hsup : (⨆ H : {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H},
        (H.val : Subgroup G)) =
        (Finset.univ : Finset {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H}).sup
          (fun H => (H.val : Subgroup G)) := by
      rw [Finset.sup_eq_iSup]
      simp [iSup_pos]
    rw [hsup]
    refine Finset.sup_induction (p := p) ?_ ?_ ?_
    · refine ⟨inferInstance, ?_⟩
      intro q hq
      simp at hq
    · rintro a₁ ⟨ha₁N, ha₁Pi⟩ a₂ ⟨ha₂N, ha₂Pi⟩
      haveI := ha₁N
      haveI := ha₂N
      exact ⟨inferInstance, Subgroup.IsPiGroup.sup_of_normal ha₁Pi ha₂Pi⟩
    · intro b _
      exact ⟨b.2.1, b.2.2⟩
  exact hgoal.2

/-- **K.map qmk が π-group ⇒ ↥K ⧸ N.subgroupOf K の primes も π 内**.
`Subgroup.nat_card_quotient_subgroupOf_eq_card_map` 経由で cardinality 経由の primeFactors
転送.

用途: Hall-Higman 3.21 body で `K/B` の π-group 性を `K_GB = K.map qmk` から導出. -/
theorem Subgroup.IsPiGroup.primeFactors_quotient_subgroupOf
    {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {N : Subgroup G} [N.Normal] {K : Subgroup G}
    (hMap : Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' N))) :
    ∀ p ∈ (Nat.card ((↥K) ⧸ (N.subgroupOf K))).primeFactors, p ∈ π := by
  intro p hp
  rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map N K] at hp
  exact hMap p hp

/-- **`oPiCore` は `π` について monotone**: `π₁ ⊆ π₂ ⇒ oPiCore π₁ G ≤ oPiCore π₂ G`.
π を広げると normal π-subgroup の集合は大きくなり, iSup も増える. -/
theorem oPiCore_mono {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) (G : Type*) [Group G] :
    oPiCore π₁ G ≤ oPiCore π₂ G := by
  refine iSup_le ?_
  rintro ⟨H, hHN, hHpi⟩
  exact le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π₂ K} =>
    (K.val : Subgroup G)) ⟨H, hHN, fun p hp => h (hHpi p hp)⟩

/-- **`O_π` 交差補題**: 有限群 `G` と素数集合 `S` について、各 `p ∈ S` の補集合 π-radical
`O_{p'}(G) = oPiCore {p}ᶜ G` の交差は `O_{S'}(G) = oPiCore Sᶜ G` に一致する:
`⨅ p ∈ S, O_{p'}(G) = O_{S'}(G)`.

- `⊇` (`oPiCore Sᶜ G ≤ ⨅ ...`): 各 `p ∈ S` で `Sᶜ ⊆ {p}ᶜ` ゆえ `oPiCore_mono`。
- `⊆` (`⨅ ... ≤ oPiCore Sᶜ G`): 交差 `D` は normal な `Sᶜ`-group。実際 `q ∈ S` を仮に
  `q ∣ |D|` とすると `D ≤ oPiCore {q}ᶜ G` (`q` 番目の項) は `{q}ᶜ`-group (`oPiCore.isPiGroup`)
  なので `q ∤ |D|`、矛盾。よって `IsPiGroup.le_oPiCore`。

用途: BG Lemma 10.8 conjunct 1 (`M_β` が Hall) — `M_β = ⋂_{p∈π(M)−β(M)} (M' の normal
p-complement)` を `O_{(π(M)−β(M))ᶜ}(M')` にまとめる第一ピース (unconditional)。 -/
theorem iInf_oPiCore_compl_singleton {G : Type*} [Group G] [Finite G] (S : Set ℕ) :
    ⨅ p ∈ S, oPiCore ({p}ᶜ : Set ℕ) G = oPiCore Sᶜ G := by
  apply le_antisymm
  · -- `D := ⨅ p ∈ S, O_{p'}(G)` is a normal `Sᶜ`-group.
    haveI hDnormal : (⨅ p ∈ S, oPiCore ({p}ᶜ : Set ℕ) G).Normal :=
      Subgroup.normal_iInf_normal fun _ =>
        Subgroup.normal_iInf_normal fun _ => inferInstance
    refine Subgroup.IsPiGroup.le_oPiCore ?_
    intro q hq
    rw [Set.mem_compl_iff]
    intro hqS
    have hDle : (⨅ p ∈ S, oPiCore ({p}ᶜ : Set ℕ) G) ≤ oPiCore ({q}ᶜ : Set ℕ) G :=
      iInf₂_le q hqS
    have hmem : q ∈ ({q}ᶜ : Set ℕ) :=
      Subgroup.IsPiGroup.le hDle (oPiCore.isPiGroup ({q}ᶜ : Set ℕ)) q hq
    simp at hmem
  · refine le_iInf₂ fun p hp => ?_
    refine oPiCore_mono ?_ G
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    rintro rfl
    exact hx hp

/-- **Hall-Higman prereq**: 有限非自明可解群は π-radical または π'-radical が非自明.

`oPiCore π G ≠ ⊥ ∨ oPiCore {p | p ∉ π} G ≠ ⊥`.

**証明**: minimal normal `M ⊴ G` を取り (Ch.2 `exists_isMinimalNormal_le_of_normal`),
Thm 3.11 で `M` elem abelian `p`-group (for some prime `p`). `IsPGroup p ↥M` から
`|M| = p^n` (`IsPGroup.iff_card`). `n ≥ 1` (`M ≠ ⊥`) で primeFactors `(p^n) = {p}`.
`p ∈ π` or `p ∉ π` で場合分け: 各々 `M ≤ oPiCore (π or π') G`, `M ≠ ⊥` で結論. -/
theorem exists_oPiCore_ne_bot_or_oPi'Core_ne_bot
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSolvable G] (π : Set ℕ) :
    oPiCore π G ≠ ⊥ ∨ oPiCore {p | p ∉ π} G ≠ ⊥ := by
  have hTopNeBot : (⊤ : Subgroup G) ≠ ⊥ := top_ne_bot
  obtain ⟨M, hMin, _⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal _ hTopNeBot
  haveI hMNormal : M.Normal := hMin.1
  have hM_ne_bot : M ≠ ⊥ := hMin.2.1
  obtain ⟨p, hp_prime, hElem⟩ := solvable_minimal_normal_isElementaryAbelian hMin
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  have hIsPGroup : IsPGroup p ↥M := fun x => ⟨1, by
    rw [pow_one]; exact hElem.pow_eq_one x⟩
  obtain ⟨n, hn_card⟩ := (IsPGroup.iff_card (G := ↥M)).mp hIsPGroup
  haveI hMnt : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
  have hM_card_gt : 1 < Nat.card ↥M := Finite.one_lt_card
  have hn_ne : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn_card
    rw [hn_card] at hM_card_gt
    exact absurd hM_card_gt (lt_irrefl _)
  have hPF : (Nat.card ↥M).primeFactors = {p} := by
    rw [hn_card]
    exact Nat.primeFactors_prime_pow hn_ne hp_prime
  by_cases hp_pi : p ∈ π
  · left
    intro hbot
    have hM_isPi : Subgroup.IsPiGroup π M := by
      intro q hq
      rw [hPF, Finset.mem_singleton] at hq
      exact hq ▸ hp_pi
    have hMle : M ≤ oPiCore π G :=
      le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
        (K.val : Subgroup G)) ⟨M, hMNormal, hM_isPi⟩
    have : M = ⊥ := le_antisymm (hbot ▸ hMle) bot_le
    exact hM_ne_bot this
  · right
    intro hbot
    have hM_isPi' : Subgroup.IsPiGroup {q | q ∉ π} M := by
      intro q hq
      rw [hPF, Finset.mem_singleton] at hq
      exact hq ▸ hp_pi
    have hMle : M ≤ oPiCore {q | q ∉ π} G :=
      le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup {q | q ∉ π} K} =>
        (K.val : Subgroup G)) ⟨M, hMNormal, hM_isPi'⟩
    have : M = ⊥ := le_antisymm (hbot ▸ hMle) bot_le
    exact hM_ne_bot this

/-! ### `oPiCore` の写像下振る舞い: surjective map / injective comap

`oPiCore` は normal π-subgroup の sup なので, surjective hom で image-押し出しは
`oPiCore` を超えず, injective hom で comap-引き戻しも `oPiCore` を超えない. これらは
`IsPiSeparable` の quotient / normal subgroup 閉包 instance の主要ステップ. -/

/-- **`oPiCore.map_le_of_surjective`**: surjective hom `f : G →* H` 下で
`oPiCore π G` の像は `oPiCore π H` に含まれる.

理由: 各 normal π-subgroup `K ⊴ G` の image `K.map f ⊴ H` は `Nat.card (K.map f) ∣ Nat.card K`
(`Subgroup.card_map_dvd`) なので π-group. -/
theorem oPiCore.map_le_of_surjective {G H : Type*} [Group G] [Finite G] [Group H] (π : Set ℕ)
    (f : G →* H) (hf : Function.Surjective f) :
    (oPiCore π G).map f ≤ oPiCore π H := by
  rw [oPiCore, Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨K, hKN, hKpi⟩
  haveI hKmapN : (K.map f).Normal := hKN.map f hf
  have hKmapPi : Subgroup.IsPiGroup π (K.map f) :=
    fun p hp => hKpi p (Nat.primeFactors_mono (K.card_map_dvd f) Nat.card_pos.ne' hp)
  exact Subgroup.IsPiGroup.le_oPiCore hKmapPi

/-- The π-Fitting series is contained in the complementary π-Fitting series.

The successor step maps the quotient by `F_n(π)` onto the quotient by `F_n(π')`;
`O_π` and `O_{π'}` are then carried into the two summands on the complementary side. -/
theorem piFittingSeries_le_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G] :
    ∀ n, piFittingSeries π G n ≤ piFittingSeries {p | p ∉ π} G n := by
  intro n
  induction n with
  | zero =>
      rw [piFittingSeries_zero, piFittingSeries_zero]
  | succ n ih =>
      intro x hx
      set π' : Set ℕ := {p | p ∉ π} with hπ'_def
      set F : Subgroup G := piFittingSeries π G n with hF_def
      set F' : Subgroup G := piFittingSeries π' G n with hF'_def
      have hF_le_F' : F ≤ F' := by
        intro y hy
        exact ih hy
      set Q : G ⧸ F →* G ⧸ F' :=
        QuotientGroup.map F F' (MonoidHom.id G) hF_le_F' with hQ_def
      have hQsurj : Function.Surjective Q := by
        intro y
        rcases QuotientGroup.mk'_surjective F' y with ⟨g, rfl⟩
        exact ⟨QuotientGroup.mk' F g, by simp [Q]⟩
      have hQ_eq : (QuotientGroup.mk' F') x = Q ((QuotientGroup.mk' F) x) := by
        simp [Q]
      rw [piFittingSeries_succ, Subgroup.mem_comap] at hx
      rw [piFittingSeries_succ, Subgroup.mem_comap]
      rw [show ({q | q ∉ π'} : Set ℕ) = π by
        ext q
        simp [π']]
      change (QuotientGroup.mk' F') x ∈
        oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F')
      rw [hQ_eq]
      have hxF : (QuotientGroup.mk' F) x ∈
          oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F) := by
        simpa [F, π', hπ'_def] using hx
      have hMapSup :
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q ≤
            oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
        calc
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q =
              (oPiCore π (G ⧸ F)).map Q ⊔ (oPiCore π' (G ⧸ F)).map Q := by
            rw [Subgroup.map_sup]
          _ ≤ oPiCore π (G ⧸ F') ⊔ oPiCore π' (G ⧸ F') :=
            sup_le_sup (oPiCore.map_le_of_surjective π Q hQsurj)
              (oPiCore.map_le_of_surjective π' Q hQsurj)
          _ = oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
            rw [sup_comm]
      exact hMapSup ⟨_, hxF, rfl⟩

/-- π-separability is symmetric under replacing `π` by its complement. -/
theorem isPiSeparable_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (hG : IsPiSeparable π G) : IsPiSeparable {p | p ∉ π} G := by
  rcases hG.exists_top with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hle := piFittingSeries_le_compl π G n
  rw [hn] at hle
  exact top_le_iff.mp hle

/-- `O_π` is invariant under group isomorphism. -/
theorem oPiCore.map_eq_of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (π : Set ℕ) (e : G ≃* H) :
    (oPiCore π G).map e = oPiCore π H := by
  refine le_antisymm (oPiCore.map_le_of_surjective π (e : G →* H) e.surjective) ?_
  intro y hy
  refine ⟨e.symm y, ?_, by simp⟩
  exact oPiCore.map_le_of_surjective π (e.symm : H →* G) e.symm.surjective ⟨y, hy, rfl⟩

/-- **`oPiCore.comap_le_of_injective`**: injective hom `f : G →* H`, `[Finite H]` 下で
`oPiCore π H` の preimage は `oPiCore π G` に含まれる.

理由: `(oPiCore π H).comap f ⊴ G` (Normal.comap instance) で π-group
(injective f で `Subgroup.equivMapOfInjective` により `comap f S ≃* (comap f S).map f`,
さらに `(comap f S).map f ≤ S = oPiCore π H` で cardinality dvd). -/
theorem oPiCore.comap_le_of_injective {G H : Type*} [Group G] [Group H] [Finite H] (π : Set ℕ)
    (f : G →* H) (hf : Function.Injective f) :
    (oPiCore π H).comap f ≤ oPiCore π G := by
  have hN : ((oPiCore π H).comap f).Normal := inferInstance
  have hPi : Subgroup.IsPiGroup π ((oPiCore π H).comap f) := by
    intro p hp
    have hcard_eq : Nat.card ↥((oPiCore π H).comap f) =
        Nat.card ↥(((oPiCore π H).comap f).map f) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ f hf).toEquiv
    have hle : ((oPiCore π H).comap f).map f ≤ oPiCore π H :=
      Subgroup.map_comap_le _ _
    have hdvd : Nat.card ↥((oPiCore π H).comap f) ∣ Nat.card ↥(oPiCore π H) := by
      rw [hcard_eq]; exact Subgroup.card_dvd_of_le hle
    exact (oPiCore.isPiGroup π) p (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hp)
  exact Subgroup.IsPiGroup.le_oPiCore hPi

/-- Quotienting by `O_π(G)` kills the π-radical. -/
theorem oPiCore_quotient_self_eq_bot {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    oPiCore π (G ⧸ oPiCore π G) = ⊥ := by
  let N : Subgroup G := oPiCore π G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := oPiCore π (G ⧸ N)
  let K : Subgroup G := Kbar.comap q
  haveI hN_normal : N.Normal := inferInstance
  haveI hK_normal : K.Normal := inferInstance
  have hN_le_K : N ≤ K := by
    intro x hx
    change q x ∈ Kbar
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact Kbar.one_mem
  have hK_map : K.map q = Kbar := by
    dsimp [K, q]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Kbar
  have hKmap_pi : Subgroup.IsPiGroup π (K.map q) := by
    rw [hK_map]
    exact oPiCore.isPiGroup π
  have hNsub_pi : Subgroup.IsPiGroup π (N.subgroupOf K) :=
    Subgroup.IsPiGroup.subgroupOf hN_le_K (oPiCore.isPiGroup π)
  have hKquot_pi :
      ∀ p ∈ (Nat.card (↥K ⧸ N.subgroupOf K)).primeFactors, p ∈ π :=
    Subgroup.IsPiGroup.primeFactors_quotient_subgroupOf hKmap_pi
  have hK_pi : Subgroup.IsPiGroup π K :=
    IsPiGroup.of_normal_quotient (N.subgroupOf K) hNsub_pi hKquot_pi
  have hK_le_N : K ≤ N := hK_pi.le_oPiCore
  have hK_eq_N : K = N := le_antisymm hK_le_N hN_le_K
  have hN_map_bot : N.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff N]
    dsimp [q]
    rw [QuotientGroup.ker_mk']
  calc
    Kbar = K.map q := hK_map.symm
    _ = N.map q := by rw [hK_eq_N]
    _ = ⊥ := hN_map_bot

/-- **`oPiCore π G ⊓ oPiCore π' G = ⊥`** for finite `G`.

`oPiCore π G` は π-group, `oPiCore π' G` は π'-group なので primeFactors が排他的
⇒ cardinality が coprime ⇒ inf が ⊥ (`Subgroup.disjoint_of_coprime_natCard` 経由).

Hall-Higman π-separable 一般版の Bezout decomposition 前提として必須. -/
theorem oPiCore.coprime_inf {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    oPiCore π G ⊓ oPiCore {p | p ∉ π} G = ⊥ := by
  apply Disjoint.eq_bot
  apply Subgroup.disjoint_of_coprime_natCard
  exact Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Nat.card_pos.ne' Nat.card_pos.ne'
    (oPiCore.isPiGroup π) (oPiCore.isPiGroup _)

/-- **Bezout 分解**: 有限群 `Q` で `A` 正規 π-group, `B` 正規 π'-group, `A ⊓ B = ⊥` のとき,
`x ∈ A ⊔ B` ならば 整数指数 `k₁ + k₂ = 1` で `x^k₁ ∈ A`, `x^k₂ ∈ B`.

数学的内容: `A ⊓ B = ⊥` + normality より `commute_of_normal_of_disjoint` で `A` と `B` の
元は可換, したがって `A ⊔ B ≃ A × B` の内部直積分解が成立. `x = ã * b̃` から各成分を
`x` の整数べきで実現 (`x^(n*β) = ã^(n*β)` (∵ `b̃^n = 1`) で π-部分, 同様に π'-部分). -/
private theorem decompose_pi_pi'_exists_zpow {Q : Type*} [Group Q] [Finite Q] (π : Set ℕ)
    {A B : Subgroup Q} [hAN : A.Normal] [hBN : B.Normal]
    (hA : Subgroup.IsPiGroup π A) (hB : Subgroup.IsPiGroup {p | p ∉ π} B)
    (hAB : A ⊓ B = ⊥) {x : Q} (hx : x ∈ A ⊔ B) :
    ∃ k₁ k₂ : ℤ, k₁ + k₂ = 1 ∧ x^k₁ ∈ A ∧ x^k₂ ∈ B := by
  obtain ⟨aA, haA, bB, hbB, hxeq⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have hdis : Disjoint A B := disjoint_iff.mpr hAB
  have hcomm : Commute aA bB :=
    Subgroup.commute_of_normal_of_disjoint A B hAN hBN hdis aA bB haA hbB
  have hm_dvd : orderOf aA ∣ Nat.card ↥A := A.orderOf_dvd_natCard haA
  have hn_dvd : orderOf bB ∣ Nat.card ↥B := B.orderOf_dvd_natCard hbB
  have hm_pi : ∀ p ∈ (orderOf aA).primeFactors, p ∈ π := fun p hp =>
    hA p (Nat.primeFactors_mono hm_dvd Nat.card_pos.ne' hp)
  have hn_pi' : ∀ p ∈ (orderOf bB).primeFactors, p ∉ π := fun p hp =>
    hB p (Nat.primeFactors_mono hn_dvd Nat.card_pos.ne' hp)
  have hcop : (orderOf aA).Coprime (orderOf bB) :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (orderOf_pos aA).ne' (orderOf_pos bB).ne' hm_pi hn_pi'
  have hbezout : (orderOf aA : ℤ) * (orderOf aA).gcdA (orderOf bB) +
      (orderOf bB : ℤ) * (orderOf aA).gcdB (orderOf bB) = 1 := by
    have h := Nat.gcd_eq_gcd_ab (orderOf aA) (orderOf bB)
    have hg : Nat.gcd (orderOf aA) (orderOf bB) = 1 := hcop
    rw [hg, Nat.cast_one] at h
    linarith
  refine ⟨(orderOf bB : ℤ) * (orderOf aA).gcdB (orderOf bB),
          (orderOf aA : ℤ) * (orderOf aA).gcdA (orderOf bB), ?_, ?_, ?_⟩
  · linarith
  · rw [show x = aA * bB from hxeq.symm, hcomm.mul_zpow]
    have hb_pow : bB ^ ((orderOf bB : ℤ) * (orderOf aA).gcdB (orderOf bB)) = 1 := by
      rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    rw [hb_pow, mul_one]
    exact A.zpow_mem haA _
  · rw [show x = aA * bB from hxeq.symm, hcomm.mul_zpow]
    have ha_pow : aA ^ ((orderOf aA : ℤ) * (orderOf aA).gcdA (orderOf bB)) = 1 := by
      rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    rw [ha_pow, one_mul]
    exact B.zpow_mem hbB _

/-- **Image of `H.subgroupOf N` in `↥N/F'` is contained in `oPiCore π (↥N/F')`**.

仮定: `F ⊴ G` で `F ≤ H ⊴ G`, `H.map (mk' F)` が π-group, `N ⊴ G`, `F' ⊴ ↥N` で
`F.subgroupOf N ≤ F'`.

数学的内容: cardinality chain
- `|image| = |↥(H.subgroupOf N) / F'.subgroupOf|` (`nat_card_quotient_subgroupOf_eq_card_map`)
- `∣ |↥(H.subgroupOf N) / (F.subgroupOf N).subgroupOf|` (`F.subgroupOf N ≤ F'` で分母拡大)
- `= |φ.range|` for `φ := (mk' F).comp (N.subtype.comp S.subtype)` (1st iso)
- `∣ |H.map (mk' F)|` (`φ.range ≤ H.map (mk' F)`).

これで image の primeFactors ⊆ π, normality は image of normal under surjective ⇒
`Subgroup.IsPiGroup.le_oPiCore` で結論. -/
private lemma image_subgroupOf_le_oPiCore (π : Set ℕ) {G : Type*} [Group G] [Finite G]
    {F : Subgroup G} [F.Normal] {H : Subgroup G} [H.Normal] (_hFH : F ≤ H)
    (hH_pi : Subgroup.IsPiGroup π (H.map (QuotientGroup.mk' F)))
    {N : Subgroup G} {F' : Subgroup ↥N} [F'.Normal]
    (hF'_le : F.subgroupOf N ≤ F') :
    (H.subgroupOf N).map (QuotientGroup.mk' F') ≤ oPiCore π (↥N ⧸ F') := by
  apply Subgroup.IsPiGroup.le_oPiCore
  intro p hp
  set S : Subgroup ↥N := H.subgroupOf N with hS_def
  let φ : ↥S →* G ⧸ F := (QuotientGroup.mk' F).comp (N.subtype.comp S.subtype)
  have hφ_range : φ.range ≤ H.map (QuotientGroup.mk' F) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.val.val, x.property, rfl⟩
  have hφ_ker : φ.ker = (F.subgroupOf N).subgroupOf S := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
               QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h_T_eq : Nat.card ↥(S.map (QuotientGroup.mk' F')) = Nat.card (↥S ⧸ F'.subgroupOf S) :=
    (Subgroup.nat_card_quotient_subgroupOf_eq_card_map F' S).symm
  have hKK' : (F.subgroupOf N).subgroupOf S ≤ F'.subgroupOf S := fun x hx => hF'_le hx
  have h_quot_dvd : Nat.card (↥S ⧸ F'.subgroupOf S) ∣
      Nat.card (↥S ⧸ (F.subgroupOf N).subgroupOf S) := by
    apply Subgroup.card_dvd_of_surjective
      (QuotientGroup.map ((F.subgroupOf N).subgroupOf S) (F'.subgroupOf S) (MonoidHom.id ↥S)
        (fun x hx => by simpa using hKK' hx))
    apply QuotientGroup.map_surjective_of_surjective
    exact QuotientGroup.mk_surjective
  have h_ker_eq : Nat.card (↥S ⧸ (F.subgroupOf N).subgroupOf S) = Nat.card (↥S ⧸ φ.ker) := by
    rw [hφ_ker]
  have h_first_iso : Nat.card (↥S ⧸ φ.ker) = Nat.card ↥φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h_range_dvd : Nat.card ↥φ.range ∣ Nat.card ↥(H.map (QuotientGroup.mk' F)) :=
    Subgroup.card_dvd_of_le hφ_range
  have hT_dvd : Nat.card ↥(S.map (QuotientGroup.mk' F')) ∣
      Nat.card ↥(H.map (QuotientGroup.mk' F)) := by
    calc Nat.card ↥(S.map (QuotientGroup.mk' F'))
        = Nat.card (↥S ⧸ F'.subgroupOf S) := h_T_eq
      _ ∣ Nat.card (↥S ⧸ (F.subgroupOf N).subgroupOf S) := h_quot_dvd
      _ = Nat.card (↥S ⧸ φ.ker) := h_ker_eq
      _ = Nat.card ↥φ.range := h_first_iso
      _ ∣ Nat.card ↥(H.map (QuotientGroup.mk' F)) := h_range_dvd
  exact hH_pi p (Nat.primeFactors_mono hT_dvd Nat.card_pos.ne' hp)

/-! ### `IsPiSeparable` の閉包 instance (quotient / normal subgroup)

`piFittingSeries` を quotient map で押し出し / subgroup へ引き戻して長さ保存. -/

/-- **`piFittingSeries` の quotient 押し出し**: `(piFittingSeries π G n).map (mk' N) ≤
piFittingSeries π (G/N) n`. quotient closure instance の主要 step. -/
private theorem piFittingSeries_map_quot_le (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] : ∀ n,
    (piFittingSeries π G n).map (QuotientGroup.mk' N) ≤ piFittingSeries π (G ⧸ N) n := by
  intro n
  induction n with
  | zero => simp [piFittingSeries_zero, Subgroup.map_bot]
  | succ n ih =>
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' : (QuotientGroup.mk' (piFittingSeries π G n)) g ∈
        oPiCore π (G ⧸ piFittingSeries π G n) ⊔
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n) := by
      rw [piFittingSeries_succ] at hg
      exact Subgroup.mem_comap.mp hg
    -- IH gives F^G_n ≤ (F^{G/N}_n).comap (mk' N)
    have hH_le : piFittingSeries π G n ≤
        (piFittingSeries π (G ⧸ N) n).comap (QuotientGroup.mk' N) := by
      intro y hy
      rw [Subgroup.mem_comap]
      exact ih ⟨y, hy, rfl⟩
    -- QuotientGroup.map : G/F^G_n → (G/N)/F^{G/N}_n is surjective.
    set Q : G ⧸ piFittingSeries π G n →* (G ⧸ N) ⧸ piFittingSeries π (G ⧸ N) n :=
      QuotientGroup.map _ _ (QuotientGroup.mk' N) hH_le with hQ_def
    have hQsurj : Function.Surjective Q := by
      apply QuotientGroup.map_surjective_of_surjective
      exact (QuotientGroup.mk_surjective).comp (QuotientGroup.mk'_surjective N)
    -- (mk' F^{G/N}_n) (mk' N g) = Q (mk' F^G_n g)
    have hQ_eq : (QuotientGroup.mk' (piFittingSeries π (G ⧸ N) n)) ((QuotientGroup.mk' N) g) =
        Q ((QuotientGroup.mk' (piFittingSeries π G n)) g) := by
      simp [hQ_def]
    rw [piFittingSeries_succ, Subgroup.mem_comap, hQ_eq]
    -- Q maps sup_G into sup_{G/N} by oPiCore.map_le_of_surjective.
    have hMapSup : (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)).map Q ≤
        oPiCore π ((G ⧸ N) ⧸ piFittingSeries π (G ⧸ N) n) ⊔
        oPiCore {p | p ∉ π} ((G ⧸ N) ⧸ piFittingSeries π (G ⧸ N) n) := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (oPiCore.map_le_of_surjective π Q hQsurj)
                       (oPiCore.map_le_of_surjective {p | p ∉ π} Q hQsurj)
    exact hMapSup ⟨_, hg', rfl⟩

/-- **`IsPiSeparable` の quotient 閉包**: `[IsPiSeparable π G] [N ⊴ G] ⇒ [IsPiSeparable π (G/N)]`. -/
instance quotient_isPiSeparable (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsPiSeparable π G] : IsPiSeparable π (G ⧸ N) where
  exists_top := by
    obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
    refine ⟨n, ?_⟩
    have hmap := piFittingSeries_map_quot_le π G N n
    rw [hn, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hmap
    exact top_le_iff.mp hmap

/-! ### Subgroup 閉包

`[IsPiSeparable π G] {N ≤ G} ⇒ [IsPiSeparable π ↥N]`.

数学的内容 (Isaacs Lem 3.18 piFittingSeries 版): `(piFittingSeries π G n).subgroupOf N`
は `↥N` の正規列で各因子が "A_π ⊔ A_π'" 構造. 各層で Bezout 分解
(`decompose_pi_pi'_exists_zpow`) により `x = x^k₁ * x^k₂` と π-part × π'-part に分け,
`image_subgroupOf_le_oPiCore` で各 part が `oPiCore π` / `oPiCore π'` に入ることを示す. -/

/-- **`piFittingSeries` の subgroup 制限**:
`N ≤ G` で `(piFittingSeries π G n).subgroupOf N ≤ piFittingSeries π N n`.

帰納法: succ ステップで Bezout 分解で `x · F_n = π-part · π'-part` を整数指数で実現,
各 part の image を `image_subgroupOf_le_oPiCore` で `O_π` / `O_π'` に押し込む. -/
private theorem piFittingSeries_subgroupOf_le (π : Set ℕ)
    (G : Type*) [Group G] [Finite G] (N : Subgroup G) : ∀ n,
    (piFittingSeries π G n).subgroupOf N ≤ piFittingSeries π N n := by
  intro n
  induction n with
  | zero =>
    rw [piFittingSeries_zero, Subgroup.bot_subgroupOf, piFittingSeries_zero]
  | succ n ih =>
    intro x hx
    haveI hFn_normal : (piFittingSeries π G n).Normal := piFittingSeries.normal π G n
    haveI hF'n_normal : (piFittingSeries π N n).Normal := piFittingSeries.normal π N n
    rw [Subgroup.mem_subgroupOf, piFittingSeries_succ, Subgroup.mem_comap] at hx
    -- hx : (mk' Fn) (x.val) ∈ oPiCore π (G/Fn) ⊔ oPiCore π' (G/Fn).
    -- Apply Bezout in G/Fn.
    obtain ⟨k₁, k₂, hsum, hk₁mem, hk₂mem⟩ :=
      decompose_pi_pi'_exists_zpow π (oPiCore.isPiGroup π) (oPiCore.isPiGroup _)
        (oPiCore.coprime_inf π) hx
    -- Goal: x ∈ piFittingSeries π N (n+1).
    rw [piFittingSeries_succ, Subgroup.mem_comap]
    -- Express x = x^k₁ * x^k₂ in ↥N (since k₁ + k₂ = 1).
    have hx_zpow : x = x^k₁ * x^k₂ := by
      rw [← zpow_add, hsum, zpow_one]
    rw [hx_zpow, map_mul]
    -- Goal: (mk' F'n) (x^k₁) * (mk' F'n) (x^k₂) ∈ oPiCore π ⊔ oPiCore π'.
    -- Show (mk' F'n) (x^k₁) ∈ oPiCore π via image_subgroupOf_le_oPiCore.
    have hF_le_Hπ : piFittingSeries π G n ≤
        Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore π (G ⧸ piFittingSeries π G n)) := by
      calc
        piFittingSeries π G n = (QuotientGroup.mk' (piFittingSeries π G n)).ker :=
          (QuotientGroup.ker_mk' _).symm
        _ ≤ Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
            (oPiCore π (G ⧸ piFittingSeries π G n)) :=
          Subgroup.ker_le_comap _ _
    have hF_le_Hπ' : piFittingSeries π G n ≤
        Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) := by
      calc
        piFittingSeries π G n = (QuotientGroup.mk' (piFittingSeries π G n)).ker :=
          (QuotientGroup.ker_mk' _).symm
        _ ≤ Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
            (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) :=
          Subgroup.ker_le_comap _ _
    have hHπ_image_eq : (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore π (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n)) =
        oPiCore π (G ⧸ piFittingSeries π G n) := by
      rw [Subgroup.map_comap_eq,
          MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      exact top_inf_eq _
    have hHπ'_image_eq : (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n)) =
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n) := by
      rw [Subgroup.map_comap_eq,
          MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      exact top_inf_eq _
    have hHπ_pi : Subgroup.IsPiGroup π
        ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore π (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n))) := by
      rw [hHπ_image_eq]; exact oPiCore.isPiGroup π
    have hHπ'_pi : Subgroup.IsPiGroup {p | p ∉ π}
        ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n))) := by
      rw [hHπ'_image_eq]; exact oPiCore.isPiGroup _
    have hT1 : ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore π (G ⧸ piFittingSeries π G n))).subgroupOf N).map
        (QuotientGroup.mk' (piFittingSeries π N n)) ≤
        oPiCore π (↥N ⧸ piFittingSeries π N n) :=
      image_subgroupOf_le_oPiCore π hF_le_Hπ hHπ_pi ih
    have hT2 : ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).subgroupOf N).map
        (QuotientGroup.mk' (piFittingSeries π N n)) ≤
        oPiCore {p | p ∉ π} (↥N ⧸ piFittingSeries π N n) :=
      image_subgroupOf_le_oPiCore {p | p ∉ π} hF_le_Hπ' hHπ'_pi ih
    -- y1 := x^k₁, y2 := x^k₂ in ↥N.
    have hy1_in : x^k₁ ∈ (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore π (G ⧸ piFittingSeries π G n))).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_zpow, map_zpow]
      exact hk₁mem
    have hy2_in : x^k₂ ∈ (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_zpow, map_zpow]
      exact hk₂mem
    exact Subgroup.mul_mem_sup
      (hT1 ⟨x^k₁, hy1_in, rfl⟩)
      (hT2 ⟨x^k₂, hy2_in, rfl⟩)

/-- **`IsPiSeparable` の subgroup 閉包**:
`[IsPiSeparable π G] {N ≤ G} ⇒ [IsPiSeparable π ↥N]`. -/
theorem Subgroup.isPiSeparable_of_isPiSeparable (π : Set ℕ)
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [IsPiSeparable π G] :
    IsPiSeparable π ↥N where
  exists_top := by
    obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
    refine ⟨n, ?_⟩
    have hle := piFittingSeries_subgroupOf_le π G N n
    rw [hn, Subgroup.top_subgroupOf] at hle
    exact top_le_iff.mp hle

/-- **`IsPiSeparable` の normal subgroup 閉包**:
`[IsPiSeparable π G] {N ⊴ G} ⇒ [IsPiSeparable π ↥N]`. -/
instance normalSubgroup_isPiSeparable (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsPiSeparable π G] : IsPiSeparable π ↥N :=
  Subgroup.isPiSeparable_of_isPiSeparable π N

/-- 補助: `piFittingSeries π G (n+1)` が `piFittingSeries π G n` を真に拡張する条件は,
`G/Fₙ` 上の `O_π ⊔ O_{π'}` が非自明であることと同値. -/
theorem piFittingSeries_lt_succ_iff (π : Set ℕ) {G : Type*} [Group G] (n : ℕ) :
    piFittingSeries π G n < piFittingSeries π G (n + 1) ↔
      (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) ≠ ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro h_sup_bot
    apply ne_of_lt h
    rw [piFittingSeries_succ, h_sup_bot]
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · refine lt_of_le_of_ne (piFittingSeries_le_succ π G n) ?_
    intro h_eq
    apply h
    have hSurj : Function.Surjective (QuotientGroup.mk' (piFittingSeries π G n)) :=
      QuotientGroup.mk'_surjective _
    apply Subgroup.comap_injective hSurj
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', ← piFittingSeries_succ, h_eq]

end
end OddOrder.Isaacs.Ch03
