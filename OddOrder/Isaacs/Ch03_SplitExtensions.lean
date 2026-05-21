/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
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

/-- **Isaacs Thm 3.3 Horosevskii**: 有限群 `G` で `σ ∈ Aut(G)` ならば `o(σ) < |G|`.
証明: `Γ := G ⋊ ⟨σ⟩` で Lucchini (Thm 2.20) を `⟨σ⟩` に適用.
TODO: Ch.2 Thm 2.20 Lucchini stub 完成後. -/
theorem horosevskii_aut_order_lt {G : Type*} [Group G] [Finite G]
    (_σ : MulAut G) [Nontrivial G] :
    True := by  -- TODO: 正しい statement (orderOf σ < Nat.card G) + proof
  trivial

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
| Thm 3.6 (crossed homom) | `OneCocycle` / `OneCocycles` (`Mathlib.RepresentationTheory.GroupCohomology.LowDegree`) |
| Thm 3.7 (transversal differ) | mathlib `MonoidHom.crossed*` 周辺 |
| Thm 3.8 (Schur-Zassenhaus 一般) | `Subgroup.exists_right_complement'_of_coprime` (abelian 不要版) |
| Thm 3.9 (G solvable ⇔ G^(m) = 1) | `isSolvable_iff_derivedSeries_eq_bot` (もしくは `derivedSeries_eq_bot_iff` 等) |
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

/-- **Isaacs Thm 3.11**: 可解群 `G` の minimal normal subgroup は ある素数 `p` について
elementary abelian p-group.

証明骨子 (Isaacs p.79): M minimal normal in G, M solvable (G solvable の部分群).
1. `M' = ⁅M, M⁆` は M で characteristic, M ⊴ G ⇒ M' ⊴ G. M' ≤ M.
2. M' < M (M solvable + M ≠ ⊥), minimality で M' = ⊥. M abelian.
3. p prime ∣ |M| 取り, Sylow_p M 唯一 (M abelian) ⇒ characteristic ⇒ ⊴ G ⇒ = M (minimality).
4. `M^p = {x^p | x ∈ M}` は M で characteristic ⇒ ⊴ G ⇒ = ⊥ or M.
5. M^p = M なら反復で M = ⊥, 矛盾. よって M^p = ⊥, M は p-elementary abelian. -/
theorem solvable_minimal_normal_isElementaryAbelian [Finite G] [IsSolvable G]
    {M : Subgroup G} (_hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p ↥M := by
  sorry

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
    ∃ H : Subgroup G, IsHallSubgroup π H := by
  sorry

/-- **Isaacs Thm 3.14 Hall-C** ⭐ **FT クリティカル**: `G` 可解 ⇒ `π`-Hall 部分群は共役.

証明骨子: 同じく `|G|`-induction. Minimal normal `M` 経由で G/M に IH 適用, 個別の
H₁, H₂ が M 経由で同じ商で対応する Hall に降りる. Schur-Zassenhaus の共役性で
`H₁ = (H₂)^g` を得る. -/
theorem hall_C_conjugate [Finite G] [IsSolvable G] (π : Set ℕ)
    {H₁ H₂ : Subgroup G} (_h1 : IsHallSubgroup π H₁) (_h2 : IsHallSubgroup π H₂) :
    ∃ g : G, H₁.map (MulEquiv.toMonoidHom (MulAut.conj g)) = H₂ := by
  sorry

/-- **Isaacs Thm 3.15**: 全ての素数 `p` について `p`-complement (i.e., `{p}'`-Hall) が
存在 ⇒ `G` 可解.

証明骨子 (Hall's converse): `|G|`-induction. p, q を `|G|` を割る相異なる素数とし,
H_p, H_q の p-, q-complement を取る. H_p ∩ H_q は {p,q}'-Hall に相当. 商と部分群の
solvability を組み合わせる. -/
theorem solvable_of_pcomplement_exists [Finite G]
    (_h : ∀ p : ℕ, p.Prime → ∃ H : Subgroup G, IsHallSubgroup {q | q ≠ p} H) :
    IsSolvable G := by
  sorry

/-- **Isaacs Lemma 3.16**: `|G:H|`, `|G:K|` が coprime ⇒ `G = HK` (i.e., `H ⊔ K = ⊤`).

証明: `(H ⊔ K).index` は `H.index` と `K.index` の両方を割り切るので gcd を割り切る.
gcd は 1 なので `(H ⊔ K).index = 1`, 故に `H ⊔ K = ⊤`. -/
theorem sup_eq_top_of_coprime_index {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) : H ⊔ K = ⊤ := by
  have h1 : (H ⊔ K).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (H ⊔ K).index ∣ K.index := Subgroup.index_dvd_of_le le_sup_right
  have h_dvd : (H ⊔ K).index ∣ 1 := h ▸ Nat.dvd_gcd h1 h2
  exact Subgroup.index_eq_one.mp (Nat.dvd_one.mp h_dvd)

/-- **Isaacs Thm 3.17**: 3 つの部分群が pairwise coprime index + solvable ⇒ `G` solvable. -/
theorem solvable_of_three_subgroups [Finite G] {H K L : Subgroup G}
    (_h12 : Nat.Coprime H.index K.index) (_h13 : Nat.Coprime H.index L.index)
    (_h23 : Nat.Coprime K.index L.index)
    [IsSolvable H] [IsSolvable K] [IsSolvable L] :
    IsSolvable G := by
  sorry

end -- 3C

section /- 3D: π-separable + Hall-Higman (pp. 89-95) -/

variable {G : Type*} [Group G]

/-- **`π`-separable 群** (placeholder): 正式には `G` の正規列で各因子が
`π`-group または `π'`-group となるもの. mathlib 未収載の新規定義.

TODO: 完全な定義 (normal series formulation) は別ファイルで扱う. 当面は文献の
"`π`-separable" を意味する propositional placeholder. 可解群は全 `π` について
`π`-separable (Cor 3.19), Sylow-style `π`-Hall は `π`-separable から復元可 (3.20). -/
def IsPiSeparable (_π : Set ℕ) (G : Type*) [Group G] : Prop :=
  -- TODO: 正式定義 (normal series with π / π' factors).
  -- 仮プレースホルダ: IsSolvable で含意される性質を弱めて記録.
  ∃ _f : ℕ → Subgroup G, True

/-- **Isaacs Lemma 3.18**: π-separable の補助補題. -/
theorem isPiSeparable_aux : True := trivial

/-- **Isaacs Cor 3.19**: `G` solvable ⇒ 全 π について π-separable.
TODO: 現在 IsPiSeparable placeholder def 下では trivial. 正式定義に直したら
derived series 経由の non-trivial 証明が要る. -/
theorem isPiSeparable_of_solvable [Finite G] [IsSolvable G] (_π : Set ℕ) :
    IsPiSeparable _π G :=
  ⟨fun _ => ⊤, trivial⟩

/-- **Isaacs Thm 3.20**: π-separable ⇒ π-Hall 部分群存在. -/
theorem hall_exists_of_piSeparable [Finite G] (π : Set ℕ) (_hπsep : IsPiSeparable π G) :
    ∃ H : Subgroup G, IsHallSubgroup π H := by
  sorry

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
