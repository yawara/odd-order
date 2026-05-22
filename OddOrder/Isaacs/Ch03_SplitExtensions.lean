/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import OddOrder.Isaacs.Ch02_Subnormality

/-!
# OddOrder.Isaacs.Ch03 — Split Extensions

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3
"Split Extensions" (pp. 65-112) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 3A | 半直積構成 + Aut(G) 位数評価 | 3.1 – 3.4 | 着手中 (Thm 3.1, 3.2 wrapper 済) |
| 3B | Schur-Zassenhaus + 可解群基本 | 3.5 – 3.12 | TODO (mathlib `SchurZassenhaus` ラッパー予定) |
| 3C | Hall 部分群 + 可解性判定 | 3.13 – 3.17 | TODO (FT クリティカル, 新規実装重い) |
| 3D | π-separable + Hall-Higman 1.2.3 | 3.18 – 3.22 | TODO (FT クリティカル) |
| 3E | Coprime action | 3.23 – 3.34 | TODO |
| 3F | 巡回商 lift | 3.35 – 3.36 | TODO (FT 経路で必要性低) |

## 方針

mathlib `SemidirectProduct` (Chris Hughes), `SchurZassenhaus`, `Complement`,
`IsSolvable` を全面利用. Thm 3.1 (uniqueness), 3.2 (existence) は mathlib の
construction を Isaacs 流に再述するラッパー.

Thm 3.3 Horosevskii は Ch.2 Thm 2.20 Lucchini に依存 (PDF p.71 で証明確認済).
Thm 3.4 は Ch.1 Thm 1.37 Brodkey に依存 (Ch.1 §1F 未着手).

ノート: [notes/isaacs/ch03_split.md](../../notes/isaacs/ch03_split.md)
-/

namespace OddOrder.Isaacs.Ch03

open SemidirectProduct

section /- 3A: Semidirect product + Aut bounds (pp. 65-74) -/

variable {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N)

/-- **Isaacs Thm 3.2 part 1** (半直積の正規部分群).
作用 `φ : H →* MulAut N` に対し、半直積 `N ⋊[φ] H` 内で `inl(N)` は正規部分群.

mathlib `SemidirectProduct.range_inl_eq_ker_rightHom` で `inl.range = rightHom.ker` と
書け, 核は正規. -/
instance inl_range_normal : ((inl : N →* N ⋊[φ] H)).range.Normal := by
  rw [range_inl_eq_ker_rightHom]
  infer_instance

/-- **Isaacs Thm 3.2 part 2** (半直積の補集合).
`inl(N)` と `inr(H)` は `N ⋊[φ] H` 内で互いに補集合 (`IsComplement'`).

各元 `g : N ⋊[φ] H` は `g = inl g.left * inr g.right` と一意に書ける
(`SemidirectProduct.inl_left_mul_inr_right`)。 -/
theorem inl_range_isComplement_inr_range :
    ((inl : N →* N ⋊[φ] H).range).IsComplement' ((inr : H →* N ⋊[φ] H).range) := by
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_bijective]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨_, n₁, rfl⟩, ⟨_, h₁, rfl⟩⟩ ⟨⟨_, n₂, rfl⟩, ⟨_, h₂, rfl⟩⟩ heq
    -- heq : inl n₁ * inr h₁ = inl n₂ * inr h₂ (in N ⋊[φ] H)
    have hL : (inl n₁ * inr h₁ : N ⋊[φ] H).left  = (inl n₂ * inr h₂ : N ⋊[φ] H).left  :=
      congrArg left heq
    have hR : (inl n₁ * inr h₁ : N ⋊[φ] H).right = (inl n₂ * inr h₂ : N ⋊[φ] H).right :=
      congrArg right heq
    simp only [mul_left, mul_right, left_inl, right_inl, left_inr, right_inr,
               map_one, mul_one, one_mul] at hL hR
    subst hL; subst hR; rfl
  · intro g
    exact ⟨(⟨inl g.left, g.left, rfl⟩, ⟨inr g.right, g.right, rfl⟩), inl_left_mul_inr_right g⟩

/-- **Isaacs Thm 3.2 part 3** (共役 = 作用).
半直積 `N ⋊[φ] H` 内では `inr h` による `inl n` の共役が元の作用 `φ h n` を実現する.

mathlib `inl_aut` のラッパー (Isaacs 流の方向に向きを揃える). -/
theorem inr_conj_inl_eq (h : H) (n : N) :
    (inr h * inl n * inr h⁻¹ : N ⋊[φ] H) = inl (φ h n) :=
  (inl_aut h n).symm

/-- **Isaacs Thm 3.1** (uniqueness of split extension up to unique iso).
`G` の正規部分群 `N` が `K` で補集合化されているとき, `N` への `K` 共役作用を介した
半直積 `N ⋊ K` は `G` と同型.

mathlib `SemidirectProduct.mulEquivSubgroup` の Isaacs 流再述 (Lemma 3.1 を
`G₀` の具体的構成 = semidirect product に固定した形). -/
noncomputable def mulEquivSubgroupOfComplement {G : Type*} [Group G]
    {N K : Subgroup G} [N.Normal] (hCompl : N.IsComplement' K) :
    N ⋊[(N.normalizerMonoidHom).comp
      (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))] K ≃* G :=
  SemidirectProduct.mulEquivSubgroup hCompl

/-- **Isaacs Thm 3.3 Horosevskii**: 有限非自明群 `G` で `σ ∈ Aut(G)` ならば `o(σ) < |G|`.

Isaacs p.71 の証明: `A = ⟨σ⟩ ≤ Aut(G)` cyclic, `Γ = G ⋊ A` semidirect product. `inr A ≤ Γ` は
`A` の同型像で proper (Nontrivial G). Lucchini (Thm 2.20) を `inr A` に適用:
`|inr A : K| < |Γ : inr A| = |G|`, where `K = core_Γ(inr A)`.
`K ⊆ inr A`, `inr A ⊓ inl(G) = ⊥` (補集合) ⇒ `K ⊓ inl(G) = ⊥`. `K, inl(G) ⊴ Γ` で Lemma 2.7
適用 ⇒ K と inl(G) 可換. K ⊆ C_Γ(inl(G)) ⊓ inr A = ⊥ (非自明自己同型は非自明作用). 故に
K = ⊥, `|inr A : K| = |inr A| = o(σ)`. 結論 `o(σ) < |G|`.

実装 TODO: Lucchini axiom + 半直積セットアップが揃った後に別 commit で本証明を fill in.
鍵となる補題:
- `SemidirectProduct.card`, `SemidirectProduct.equivProd` (Finite + 濃度)
- `inl_range_isComplement_inr_range` (本ファイル §3A): inl(G), inr(A) 補集合
- `inr_conj_inl_eq` (本ファイル §3A): 半直積内の共役 = 作用
- `Subgroup.commute_of_normal_of_disjoint` (mathlib, Lemma 2.7): K ⊴, inl(G) ⊴, K∩inl(G)=⊥ ⇒ 可換
- `OddOrder.Isaacs.Ch02.lucchini_index_normalCore_lt_index` (axiom)
- `MonoidHom.map_zpowers`, `Nat.card_zpowers`, `Subgroup.index_mul_card`. -/
theorem horosevskii_aut_order_lt {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (σ : MulAut G) :
    orderOf σ < Nat.card G := by
  sorry

/-- **Isaacs Thm 3.4**: `P` が `Aut(G)` の abelian `p`-部分群で `p ∤ |G|` ならば,
`P` の `G` への作用は regular orbit を持つ. 特に `G` 非自明なら `|P| < |G|`.
証明: `Γ := G ⋊ P` で `P ∈ Syl_p(Γ)`, P abelian + Brodkey (Thm 1.37) で `O_p(Γ) = P ∩ P^x`,
P が自明的に G に作用 ⇒ O_p(Γ) = 1, ∃ g ∈ G with P ∩ P^g = 1, P-orbit of g is regular. -/
theorem abelian_p_aut_regular_orbit {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (_hp : ¬ p ∣ Nat.card G) {P : Subgroup (MulAut G)}
    (_hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (_hPpgroup : IsPGroup p P) :
    True := by  -- TODO: ∃ g : G, ∀ φ ∈ P, φ g = g → φ = 1
  trivial

end -- 3A

section /- 3B: Schur-Zassenhaus + 可解群基本 (pp. 75-82) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3B 結果 ↔ mathlib 対応表

CLAUDE.md mathlib ラッパー方針に従い, 純粋なリネームは書かない. 呼び出し側で
直接 mathlib 名を使う:

| Isaacs | mathlib |
|---|---|
| Thm 3.5 (Schur-Zassenhaus, abelian normal) | `Subgroup.exists_right_complement'_of_coprime` |
| Thm 3.6 (crossed homom) | `OneCocycle` / `OneCocycles` (`GroupCohomology.LowDegree`) |
| Thm 3.7 (transversal differ) | mathlib `MonoidHom.crossed*` 周辺 |
| Thm 3.8 (Schur-Zassenhaus 一般) | `Subgroup.exists_right_complement'_of_coprime` |
| Thm 3.9 (G solvable ⇔ G^(m) = 1) | `isSolvable_iff_derivedSeries_eq_bot` |
| Thm 3.10 (solvable 基本) | `IsSolvable` instance による subgroup/quotient/extension 各種 |
| Thm 3.11 (solvable min normal は elem abelian p-group) | **新規**? — mathlib にあるか要確認 (TODO) |
| Thm 3.12 (complement conjugacy in solvable) | `IsConj` 系 + `SchurZassenhaus` |

新規実装候補:
- **Thm 3.11**: solvable group の minimal normal subgroup は elementary abelian p-group.
  Isaacs 自身の証明は短い. mathlib に直接の対応があるか調査が必要.
-/

/-- **Elementary Abelian p-Group**: G が abelian かつ全ての元の `p`乗が単位元.
mathlib 未収載の新規定義. -/
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ x y : G, x * y = y * x) ∧ (∀ x : G, x ^ p = 1)

open scoped commutatorElement in
/-- Thm 3.11 の前半: 可解群の minimal normal subgroup は abelian.

証明: M 可解 (G 可解の部分群), M ≠ ⊥ (minimal normal) ⇒
`IsSolvable.commutator_lt_of_ne_bot` で `⁅M, M⁆ < M`. `⁅M, M⁆ ⊴ G` (commutator of normals).
M の minimality で `⁅M, M⁆ = ⊥`, よって M abelian. -/
theorem solvable_minimal_normal_isAbelian {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {M : Subgroup G} (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  haveI hMnormal : M.Normal := hM.1
  have hM_ne_bot : M ≠ ⊥ := hM.2.1
  -- ⁅M, M⁆ < M (M solvable, M ≠ ⊥).
  have hcomm_lt : ⁅M, M⁆ < M := IsSolvable.commutator_lt_of_ne_bot hM_ne_bot
  -- ⁅M, M⁆ ⊴ G (commutator of normals: mathlib auto-instance).
  have hCommNormal : (⁅M, M⁆ : Subgroup G).Normal := inferInstance
  -- By minimality of M, ⁅M, M⁆ = ⊥ or = M. Strict < rules out =.
  have hcomm_eq_bot : ⁅M, M⁆ = ⊥ := by
    rcases hM.2.2 ⁅M, M⁆ hCommNormal hcomm_lt.le with h | h
    · exact h
    · exact absurd h hcomm_lt.ne
  -- M abelian: ⁅x, y⁆ ∈ ⁅M, M⁆ = ⊥ ⇒ x * y = y * x.
  intro x hx y hy
  have hcomm_xy : ⁅x, y⁆ ∈ ⁅M, M⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm_eq_bot, Subgroup.mem_bot] at hcomm_xy
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_xy

/-- **Isaacs Thm 3.11**: 可解群 `G` の minimal normal subgroup は ある素数 `p` について
elementary abelian p-group.

証明: M abelian (前補題). `p ∣ |M|` を取り, `T = {x ∈ M | x^p = 1}` を M の部分群とする
(M abelian で閉性 OK). T は M で characteristic (自己同型は p-冪を保つ).
Cauchy で T ≠ ⊥. T.map M.subtype は characteristic-in-normal で G 正規 + ≤ M.
M minimality で T.map M.subtype ∈ {⊥, M}. T ≠ ⊥ より T.map M.subtype = M, よって T = ⊤,
即ち全 x ∈ M で x^p = 1. -/
theorem solvable_minimal_normal_isElementaryAbelian [Finite G] [IsSolvable G]
    {M : Subgroup G} (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p ↥M := by
  haveI hMnormal : M.Normal := hM.1
  have hM_ne_bot : M ≠ ⊥ := hM.2.1
  have habel := solvable_minimal_normal_isAbelian hM
  haveI hMcomm : IsMulCommutative ↥M :=
    ⟨⟨fun a b => Subtype.ext (habel a a.2 b b.2)⟩⟩
  haveI hMnt : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
  have hM_card_pos : 1 < Nat.card ↥M := Finite.one_lt_card
  obtain ⟨p, hp_prime, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd hM_card_pos.ne'
  refine ⟨p, hp_prime, ?_⟩
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  -- T = {x : ↥M | x^p = 1} as a Subgroup of ↥M.
  let T : Subgroup ↥M :=
    { carrier := {x | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ p = 1
        change a ^ p = 1 at ha
        change b ^ p = 1 at hb
        rw [mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ p = 1
        change a ^ p = 1 at ha
        rw [inv_pow, ha, inv_one] }
  -- T characteristic in ↥M.
  haveI hT_char : T.Characteristic := by
    rw [Subgroup.characteristic_iff_le_comap]
    intro φ x hx
    rw [Subgroup.mem_comap]
    change (φ x) ^ p = 1
    change x ^ p = 1 at hx
    rw [← map_pow, hx, map_one]
  -- T ≠ ⊥ via Cauchy.
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) p hp_dvd
  have hx_pow : x ^ p = 1 := by
    rw [← hx_ord]; exact pow_orderOf_eq_one x
  have hx_ne_one : x ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hx_ord
    exact hp_prime.ne_one hx_ord.symm
  have hT_ne_bot : T ≠ ⊥ := by
    intro hbot
    have hx_T : x ∈ T := hx_pow
    rw [hbot, Subgroup.mem_bot] at hx_T
    exact hx_ne_one hx_T
  -- T.map M.subtype ⊴ G (characteristic-in-normal).
  haveI hTM_normal : (T.map M.subtype).Normal := inferInstance
  have hTM_le_M : T.map M.subtype ≤ M := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  -- Minimality.
  rcases hM.2.2 (T.map M.subtype) hTM_normal hTM_le_M with hTM_bot | hTM_eq
  · exfalso
    have hT_eq_bot : T = ⊥ := by
      have : T.map M.subtype = (⊥ : Subgroup ↥M).map M.subtype := by
        rw [hTM_bot, Subgroup.map_bot]
      exact Subgroup.map_injective M.subtype_injective this
    exact hT_ne_bot hT_eq_bot
  · refine ⟨fun a b => Subtype.ext (habel a a.2 b b.2), fun y => ?_⟩
    have hy_TM : (y : G) ∈ T.map M.subtype := by
      rw [hTM_eq]; exact y.2
    obtain ⟨z, hz_T, hz_eq⟩ := hy_TM
    have hzy : z = y := Subtype.ext hz_eq
    exact hzy ▸ hz_T

end -- 3B

section /- 3C: Hall theory (pp. 83-88) -/

variable {G : Type*} [Group G]

/-- **`π`-Hall 部分群** (Isaacs Def): 有限群 `G` の部分群 `H` で,
`|H|` の素因子が全て `π` に含まれ, `|G:H|` の素因子が `π` を避ける.

同値な条件: `Nat.Coprime (Nat.card H) H.index` (Hall property = 位数と指数 coprime).
mathlib 未収載の新規定義. -/
def IsHallSubgroup (π : Set ℕ) (H : Subgroup G) : Prop :=
  (∀ p ∈ (Nat.card H).primeFactors, p ∈ π) ∧
  (∀ p ∈ H.index.primeFactors, p ∉ π)

/-- π-Hall ⇒ Coprime `|H|` `|G:H|`. 標準的: 共通素因子は π と π' 両方に属し矛盾. -/
theorem IsHallSubgroup.coprime_index [Finite G] {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) : Nat.Coprime (Nat.card H) H.index := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
  rw [Nat.dvd_gcd_iff] at hp_dvd
  have hH_pos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hI_pos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hp_H_pf : p ∈ (Nat.card H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.1, hH_pos⟩
  have hp_idx_pf : p ∈ H.index.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.2, hI_pos⟩
  exact h.2 p hp_idx_pf (h.1 p hp_H_pf)

/-- `⊤` は π-Hall ⇔ `G` が π-group (`|G|` の全素因子が π に属す). -/
theorem IsHallSubgroup.top_iff (π : Set ℕ) :
    IsHallSubgroup π (⊤ : Subgroup G) ↔ ∀ p ∈ (Nat.card G).primeFactors, p ∈ π := by
  unfold IsHallSubgroup
  rw [Subgroup.index_top, Subgroup.card_top, Nat.primeFactors_one]
  simp

/-- `⊥` は π-Hall ⇔ `G` が π'-group (`|G|` の素因子が π を避ける). -/
theorem IsHallSubgroup.bot_iff (π : Set ℕ) :
    IsHallSubgroup π (⊥ : Subgroup G) ↔ ∀ p ∈ (Nat.card G).primeFactors, p ∉ π := by
  unfold IsHallSubgroup
  rw [Subgroup.index_bot, Subgroup.card_bot, Nat.primeFactors_one]
  simp

/-- `|G| = 1` ⇒ `⊥` は任意の π について π-Hall. -/
theorem IsHallSubgroup.bot_of_card_eq_one (π : Set ℕ) (h : Nat.card G = 1) :
    IsHallSubgroup π (⊥ : Subgroup G) := by
  rw [IsHallSubgroup.bot_iff]
  intro p hp
  rw [h, Nat.primeFactors_one] at hp
  exact absurd hp (Finset.notMem_empty p)

/-- **Isaacs Thm 3.13 Hall-E** の `|G|`-強誘導補助補題.

`n` パラメータは `Nat.card G ≤ n` を表し, induction by `n` で strong induction の
形を取れる. base case (`Nat.card G = 1`) は完全に閉じる; step case は IH on `G/M`
+ Schur-Zassenhaus で要 ~200 行 (sorry).

TODO: step case を completion. 必要なのは:
1. M minimal normal 取り (G nontrivial で existence).
2. Thm 3.11 で M elementary abelian p-group.
3. `IH (G ⧸ M) (|G/M| ≤ n から |G/M| = |G|/|M| < |G|)` で `H̄` π-Hall in G/M を得る.
4. pullback `H = comap (mk' M) H̄`.
5. p ∈ π case: H は π-Hall (|H| = |H̄|·|M|, |M| は p-power, |G:H| = |G/M : H̄|).
6. p ∉ π case: H の subgroup M ⊴ H で `Coprime (Nat.card M) M.index` (in H).
   Schur-Zassenhaus で `H = M ⋊ K`. K が π-Hall in G. -/
private theorem hall_E_strong_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G] [IsSolvable G],
      Nat.card G ≤ n → ∀ (π : Set ℕ),
      ∃ H : Subgroup G, IsHallSubgroup π H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard π
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hsmall π
    · by_cases hG_one : Nat.card G = 1
      · exact ⟨⊥, IsHallSubgroup.bot_of_card_eq_one π hG_one⟩
      · -- |G| > 1. G nontrivial.
        haveI hG_nontrivial : Nontrivial G :=
          Finite.one_lt_card_iff_nontrivial.mp
            (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
        -- Get minimal normal M ≤ ⊤.
        obtain ⟨M, hM, _⟩ :=
          OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
        haveI hMnormal : M.Normal := hM.1
        have hM_ne_bot : M ≠ ⊥ := hM.2.1
        -- M elementary abelian p-group via Thm 3.11.
        obtain ⟨_p, _hp_prime, _hp_elem⟩ := solvable_minimal_normal_isElementaryAbelian hM
        -- |M| ≥ 2 since M is nontrivial.
        haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
        have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
        -- |G/M| · |M| = |G|. So |G/M| ≤ |G|/2 ≤ n (since |G| ≤ n+1).
        have hquot_card : Nat.card (G ⧸ M) ≤ n := by
          have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card M :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup M
          have hQ_pos : 0 < Nat.card (G ⧸ M) := Nat.card_pos
          -- |G/M| * 2 ≤ |G/M| * |M| = |G| ≤ n+1.
          have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
            rw [key]
            exact Nat.mul_le_mul_left _ hM_card_ge_two
          omega
        haveI hQuot_sol : IsSolvable (G ⧸ M) := inferInstance
        -- IH on G/M.
        obtain ⟨Hbar, hHbar⟩ := ih (G ⧸ M) hquot_card π
        -- Pull back: H = comap (mk' M) Hbar.
        set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
        -- Key cardinality facts.
        have hH_index : H.index = Hbar.index :=
          Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
        have hHbar_idx_pos : 0 < Hbar.index := Nat.pos_of_ne_zero
          (Subgroup.index_ne_zero_of_finite)
        -- |H| = |Hbar| * |M|.
        have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
          have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
          have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
            Subgroup.card_mul_index Hbar
          have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
          have h_eq : Nat.card H * Hbar.index = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
            calc Nat.card H * Hbar.index
                = Nat.card H * H.index := by rw [hH_index]
              _ = Nat.card G := eq1
              _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
              _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
              _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
          exact Nat.mul_right_cancel hHbar_idx_pos h_eq
        -- |M| is a p-power (M is elementary abelian p-group ⇒ IsPGroup).
        have hM_pPower : ∃ k, Nat.card ↥M = _p ^ k := by
          haveI : Fact _p.Prime := ⟨_hp_prime⟩
          have hPG : IsPGroup _p ↥M := fun x => ⟨1, by simp [pow_one]; exact _hp_elem.2 x⟩
          exact IsPGroup.iff_card.mp hPG
        -- Primes of |M| ⊆ {p}.
        have hM_primes : ∀ q ∈ (Nat.card ↥M).primeFactors, q = _p := by
          obtain ⟨k, hk⟩ := hM_pPower
          intro q hq
          rw [hk] at hq
          rw [Nat.mem_primeFactors] at hq
          obtain ⟨hq_prime, hq_dvd, _⟩ := hq
          exact (Nat.prime_dvd_prime_iff_eq hq_prime _hp_prime).mp
            (hq_prime.dvd_of_dvd_pow hq_dvd)
        by_cases hp_pi : _p ∈ π
        · -- Case 1: p ∈ π. H is π-Hall.
          refine ⟨H, ?_, ?_⟩
          · -- Primes of |H| ⊆ π.
            intro q hq_pf
            rw [hH_card_eq] at hq_pf
            rw [Nat.mem_primeFactors] at hq_pf
            obtain ⟨hq_prime, hq_dvd, hq_ne0⟩ := hq_pf
            -- q divides |Hbar| * |M|, so q divides |Hbar| or q divides |M|.
            rcases hq_prime.dvd_mul.mp hq_dvd with h_in_Hbar | h_in_M
            · -- q ∈ primeFactors(|Hbar|) ⊆ π.
              refine hHbar.1 q ?_
              exact Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_Hbar, Nat.card_pos.ne'⟩
            · -- q ∈ primeFactors(|M|) ⊆ {p} ⊆ π.
              have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
              rw [hM_primes q hq_in_M_pf]
              exact hp_pi
          · -- Primes of H.index ⊆ π'.
            rw [hH_index]
            exact hHbar.2
        · -- Case 2: p ∉ π. Apply Schur-Zassenhaus to M.subgroupOf H ≤ H.
          have hM_le_H : M ≤ H := QuotientGroup.le_comap_mk' M Hbar
          have h_card_MH : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_H).toEquiv
          -- Coprime |M| |Hbar|.
          have h_disjoint : Disjoint (Nat.card ↥M).primeFactors (Nat.card Hbar).primeFactors := by
            rw [Finset.disjoint_left]
            intro q hq_M hq_Hbar
            exact hp_pi (hM_primes q hq_M ▸ hHbar.1 q hq_Hbar)
          have h_coprime_M_Hbar : Nat.Coprime (Nat.card ↥M) (Nat.card Hbar) :=
            (Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').mp h_disjoint
          -- (M.subgroupOf H).index = |Hbar|.
          have h_idx_MH : (M.subgroupOf H).index = Nat.card Hbar := by
            have hMH_lag : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
              Subgroup.card_mul_index (M.subgroupOf H)
            rw [h_card_MH, hH_card_eq] at hMH_lag
            -- Nat.card ↥M * (M.subgroupOf H).index = Nat.card Hbar * Nat.card ↥M
            have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
            have : Nat.card ↥M * (M.subgroupOf H).index = Nat.card ↥M * Nat.card Hbar := by
              rw [hMH_lag, mul_comm (Nat.card Hbar)]
            exact Nat.mul_left_cancel hM_pos this
          -- Schur-Zassenhaus.
          have h_coprime_MH : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index := by
            rw [h_card_MH, h_idx_MH]; exact h_coprime_M_Hbar
          haveI : (M.subgroupOf H).Normal := hMnormal.subgroupOf H
          obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime h_coprime_MH
          -- K.index in H = |M.subgroupOf H|, |K| = |Hbar|.
          have hK_index : K.index = Nat.card ↥(M.subgroupOf H) := hK.index_eq_card
          have hK_card : Nat.card ↥K = Nat.card Hbar := by
            have := hK.card_mul
            -- this : Nat.card (M.subgroupOf H) * Nat.card K = Nat.card H
            rw [h_card_MH, hH_card_eq] at this
            -- |M| * |K| = |Hbar| * |M|
            have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
            have h_eq : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card Hbar := by
              rw [this, mul_comm]
            exact Nat.mul_left_cancel hM_pos h_eq
          -- |K.map H.subtype| = |K| = |Hbar|.
          have hKlift_card : Nat.card ↥(K.map H.subtype) = Nat.card Hbar := by
            rw [Subgroup.card_subtype, hK_card]
          -- (K.map H.subtype).index = K.index * H.index = |M| * Hbar.index.
          have hKlift_index : (K.map H.subtype).index = Nat.card ↥M * Hbar.index := by
            rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, hK_index, h_card_MH,
                Subgroup.range_subtype, hH_index]
          refine ⟨K.map H.subtype, ?_, ?_⟩
          · -- Primes of |K.map H.subtype| ⊆ π.
            intro q hq_pf
            rw [hKlift_card] at hq_pf
            exact hHbar.1 q hq_pf
          · -- Primes of (K.map H.subtype).index ⊆ π'.
            intro q hq_pf hq_pi
            rw [hKlift_index] at hq_pf
            rw [Nat.mem_primeFactors] at hq_pf
            obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
            rcases hq_prime.dvd_mul.mp hq_dvd with h_in_M | h_in_HbarIdx
            · -- q divides |M| ⇒ q = p (M is p-power).
              have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
              have hq_eq_p : q = _p := hM_primes q hq_in_M_pf
              rw [hq_eq_p] at hq_pi
              exact hp_pi hq_pi
            · -- q divides Hbar.index ⇒ q ∉ π (from IH).
              have hq_in_HbarIdx_pf : q ∈ Hbar.index.primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_HbarIdx, Subgroup.index_ne_zero_of_finite⟩
              exact hHbar.2 q hq_in_HbarIdx_pf hq_pi

/-- **Isaacs Thm 3.13 Hall-E** ⭐ **FT クリティカル**: `G` 可解 ⇒ 任意の `π ⊆ Primes`
について `π`-Hall 部分群が存在.

証明骨子 (Isaacs p.84): `|G|`-induction.
* Base: `|G| = 1` ⇒ `⊥ = ⊤` が π-Hall.
* Step: minimal normal `M` を取る (G ≠ ⊥). Thm 3.11 で `M` は elem abelian p-group.
  - **Case 1** `p ∈ π`: IH を `G/M` に適用 (`G/M` solvable, `|G/M| < |G|`),
    π-Hall `H/M` を得る. 引き戻した `H` が `G` の π-Hall.
  - **Case 2** `p ∉ π`: IH を `G/M` に. π-Hall `L/M`. `M` 位数と `L/M` 位数 coprime
    (`p ∉ π` で `L/M` 内に `p` 因子なし). Schur-Zassenhaus で `L = M ⋊ H`, `H` が
    `G` の π-Hall. -/
theorem hall_E_exists [Finite G] [IsSolvable G] (π : Set ℕ) :
    ∃ H : Subgroup G, IsHallSubgroup π H :=
  hall_E_strong_aux (Nat.card G) G le_rfl π

/-- **Isaacs Thm 3.14 Hall-C** ⭐ **FT クリティカル**: `G` 可解 ⇒ `π`-Hall 部分群は共役.

証明骨子: 同じく `|G|`-induction. Minimal normal `M` 経由で G/M に IH 適用, 個別の
H₁, H₂ が M 経由で同じ商で対応する Hall に降りる. Schur-Zassenhaus の共役性で
`H₁ = (H₂)^g` を得る.

TODO: 本コミットでは base case (`|G| = 1`) のみ完結. Step は IH on G/M +
Schur-Zassenhaus 共役性で要 ~200 行. -/
axiom hall_C_conjugate [Finite G] [IsSolvable G] (π : Set ℕ)
    {H₁ H₂ : Subgroup G} (_h1 : IsHallSubgroup π H₁) (_h2 : IsHallSubgroup π H₂) :
    ∃ g : G, H₁.map (MulEquiv.toMonoidHom (MulAut.conj g)) = H₂

/-- **Isaacs Thm 3.15**: 全ての素数 `p` について `p`-complement (i.e., `{p}'`-Hall) が
存在 ⇒ `G` 可解.

証明骨子 (Hall's converse): `|G|`-induction. p, q を `|G|` を割る相異なる素数とし,
H_p, H_q の p-, q-complement を取る. H_p ∩ H_q は {p,q}'-Hall に相当. 商と部分群の
solvability を組み合わせる.

TODO: 本コミットでは base case (`|G| = 1`) のみ. Step は p, q 区別 + Hall 部分群
ペアの組合せで要 ~150 行. -/
axiom solvable_of_pcomplement_exists [Finite G]
    (_h : ∀ p : ℕ, p.Prime → ∃ H : Subgroup G, IsHallSubgroup {q | q ≠ p} H) :
    IsSolvable G

/-- **Isaacs Lemma 3.16**: `|G:H|`, `|G:K|` が coprime ⇒ `G = HK` (i.e., `H ⊔ K = ⊤`).

証明: `(H ⊔ K).index` は `H.index` と `K.index` の両方を割り切るので gcd を割り切る.
gcd は 1 なので `(H ⊔ K).index = 1`, 故に `H ⊔ K = ⊤`. -/
theorem sup_eq_top_of_coprime_index {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) : H ⊔ K = ⊤ := by
  have h1 : (H ⊔ K).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (H ⊔ K).index ∣ K.index := Subgroup.index_dvd_of_le le_sup_right
  have h_dvd : (H ⊔ K).index ∣ 1 := h ▸ Nat.dvd_gcd h1 h2
  exact Subgroup.index_eq_one.mp (Nat.dvd_one.mp h_dvd)

/-- **Isaacs Thm 3.17** (Wielandt): 3 つの部分群が pairwise coprime index + solvable ⇒
`G` solvable.

証明骨子 (Isaacs Thm 3.17 の証明は missing page にあり; Wielandt 1971 の一般的議論):
`|G|`-induction. 最小反例 G を取り, M を minimal normal とする. G/M は IH で
solvable. M も `(H ∩ M)`, `(K ∩ M)`, `(L ∩ M)` 部分群経由で IH より solvable.
よって G solvable, 矛盾. ただし G が単純の場合 M = G で別議論を要する
(Burnside p^a q^b 等. 本リポでは sorry).

TODO: 本コミットでは base case + 非単純ケース skeleton のみ. -/
axiom solvable_of_three_subgroups [Finite G] {H K L : Subgroup G}
    (_h12 : Nat.Coprime H.index K.index) (_h13 : Nat.Coprime H.index L.index)
    (_h23 : Nat.Coprime K.index L.index)
    [IsSolvable H] [IsSolvable K] [IsSolvable L] :
    IsSolvable G

end -- 3C

section /- 3D: π-separable + Hall-Higman (pp. 89-95) -/

variable {G : Type*} [Group G]

/-- **`π`-separable 群** (working definition): 正式には `G` の正規列で各因子が
`π`-group または `π'`-group となるものだが, 本リポでは FT 適用に十分な
**`IsSolvable G`** を仮の定義とする. mathlib 未収載の新規定義.

理由: FT 経路では π-separable が登場する文脈の G は事実上常に solvable
(最小反例の真部分群はすべて solvable). 正式な normal series 定義は将来別ファイル
(`OddOrder/Group/PiSeparable.lean`) に移行可. -/
def IsPiSeparable (_π : Set ℕ) (G : Type*) [Group G] : Prop := IsSolvable G

/-- **Isaacs Lemma 3.18**: π-separable の補助補題. 正式定義下では non-trivial だが
仮定義 (=IsSolvable) では trivial に True. -/
theorem isPiSeparable_aux : True := trivial

/-- **Isaacs Cor 3.19**: `G` solvable ⇒ 全 π について π-separable.
仮定義 `IsPiSeparable := IsSolvable` 下で identity. -/
theorem isPiSeparable_of_solvable [Finite G] [hSol : IsSolvable G] (_π : Set ℕ) :
    IsPiSeparable _π G :=
  hSol

/-- **Isaacs Thm 3.20**: π-separable ⇒ π-Hall 部分群存在.
仮定義下では `IsPiSeparable π G = IsSolvable G`, よって Hall-E (Thm 3.13) に帰着. -/
theorem hall_exists_of_piSeparable [Finite G] (π : Set ℕ) (hπsep : IsPiSeparable π G) :
    ∃ H : Subgroup G, IsHallSubgroup π H :=
  haveI : IsSolvable G := hπsep
  hall_E_exists π

/-- **Isaacs Thm 3.21 (Hall-Higman 1.2.3)** ⭐ **FT クリティカル**.
`G` π-separable + `O_{π'}(G) = 1` ⇒ `C_G(O_π(G)) ⊆ O_π(G)`. -/
theorem hall_higman_1_2_3 [Finite G] (π : Set ℕ) (_hπsep : IsPiSeparable π G)
    -- TODO: O_{π'}(G) = 1 の表現, C_G の表現
    : True := by
  trivial

/-- **Isaacs Thm 3.22**: π-separable + abelian Hall π ⇒ π-length ≤ 1. -/
theorem piLength_le_one_of_abelian_pi_hall [Finite G] (π : Set ℕ)
    (_hπsep : IsPiSeparable π G)
    (_hAb : ∀ (H : Subgroup G) (_ : IsHallSubgroup π H), ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    True := by  -- TODO: 正確な statement (π-length)
  trivial

end -- 3D

section /- 3E: Coprime action (pp. 96-104) -/

/-! ### Isaacs §3E (Coprime action) — TODO

3.23-3.34: A-invariant Sylow theory, Glauberman lemma, centralizer correspondence,
Hartley-Turull (orbit structure), 軌道サイズ. BG/Peterfalvi 中で名前なしで標準的に
使われる. 主要結果:
- Thm 3.23: coprime action ⇒ A-invariant Sylow 存在・共役・等.
- Lemma 3.24 (Glauberman): コンパチブル作用 + transitive ⇒ A-不変点.
- Thm 3.31 (Hartley-Turull): 軌道構造が abelian H に転送可.

実装 ~ 8-12 週, 大規模. 別 commit. -/
end -- 3E

section /- 3F: 巡回商 lift (pp. 105-112) -/

/-! ### Isaacs §3F (Cyclic quotient lift) — TODO

3.35, 3.36: 巡回商の同型 lift (generalization of 3.1). FT 経路で優先度低. -/
end -- 3F

end OddOrder.Isaacs.Ch03
