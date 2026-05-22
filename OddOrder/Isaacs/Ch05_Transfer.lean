/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import OddOrder.Isaacs.Ch03_SplitExtensions

/-!
# OddOrder.Isaacs.Ch05 — Transfer

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 5
"Transfer" (pp. 147-180) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 5A | Transfer 定義・welldefinedness・準同型性 | 5.1 – 5.4 | mathlib `MonoidHom.transfer` 直接 |
| 5B | 中心への transfer = n 乗, Schur, Dietzmann | 5.5 – 5.10 | mathlib 直接 + 5.10 保留 |
| 5C | Hall transfer, Burnside, cyclic / abelian Sylow | 5.11 – 5.19 | mathlib 直接 + 5.18 実装 |
| 5D | Focal subgroup theorem + p-transfer control | 5.20 – 5.24 | mathlib `Focal.lean` 直接 |
| 5E | Frobenius normal p-complement + 系 | 5.25 – 5.30 | docstring + 保留 (FT クリティカル) |

## 方針

mathlib カバレッジは Ch.5 中で最も厚い (`Mathlib/GroupTheory/Transfer.lean` 350 行 +
`Focal.lean` 218 行 + `Schreier.lean` + `SpecificGroups/ZGroup.lean`).
**no-wrapper policy** に従い, mathlib 直接対応の Isaacs 番号は section docstring の
対応表に記録するのみ. Isaacs 流のステートメント (引数特殊化や Isaacs 流の `H/H'` 標的)
が必要な場合のみ別途定理化する.

## Mathlib direct correspondence (no wrapper)

mathlib 既収載で本ファイルでは wrapper を書かないもの:

* `MonoidHom.transfer` (`Transfer.lean:148`) = **Thm 5.1, 5.2** (transfer welldef + 準同型).
* `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot` (`Transfer.lean:161`) = **Thm 5.5**
  (transfer-evaluation lemma; orbital 分解).
* `MonoidHom.transfer_center_eq_pow`, `transferCenterPow` (`Transfer.lean:222, 229`)
  = **Thm 5.6** (中心 transfer = `g ↦ g^|G:Z|`).
* `Subgroup.card_commutator_le_of_finite_commutatorSet` (`Schreier.lean:208`) =
  **Thm 5.7** (Schur, bound 付き強化版).
* `MonoidHom.ker_transferSylow_isComplement'` (`Transfer.lean:275`) = **Thm 5.13 Burnside**.
* `IsCyclic.isComplement'` (`Transfer.lean:339`) = **Cor 5.14** (cyclic Sylow + smallest prime).
* `IsZGroup.isCyclic_commutator` (`ZGroup.lean:144`) = **Thm 5.16 part 1** (G' cyclic).
* `IsZGroup.isCyclic_abelianization` (`ZGroup.lean:134`) = **Thm 5.16 part 2** (G/G' cyclic).
* `IsZGroup.coprime_commutator_index` (`ZGroup.lean:280`) = **Thm 5.16 part 3** (|G'|, |G:G'| coprime).
* `isZGroup_iff_exists_mulEquiv` (`ZGroup.lean:315`) = **Thm 5.16 part 4** (semidirect product 形).
* `IsZGroup → IsSolvable` instance (`ZGroup.lean:102`) = **Cor 5.15** (Z-group solvable).
* `Subgroup.focalSubgroup`, `focalSubgroupOf`, `transferFocal` (`Focal.lean:58, 67, 151`) =
  Focal subgroup の定義 (Isaacs §5D 冒頭).
* `Subgroup.ker_restrict_transferFocal_eq_focalSubgroupOf` (`Focal.lean:191`) = **Thm 5.20**
  に相当 (ker(v) restrict 表示).
* `Subgroup.commutator_inf_eq_focalSubgroup` (`Focal.lean:208`) = **Thm 5.21 Focal Subgroup
  Theorem (D. G. Higman)** ⭐ **FT クリティカル**. BG が独自 Thm 1.17 として再述.
* `Subgroup.transferFocal_surjective` (`Focal.lean:180`) = transfer 全射性 (5.21 系).

## 下流被引用 (FT 経路)

**最重要**: **Focal Subgroup Theorem (5.21)** — BG が独自 Thm 1.17 として再述, 本文 3 箇所
(L2723, L5042, L5068) で使用. **Burnside (5.13)** = BG Thm 1.18 として再述.

Peterfalvi 本体 §4-§16 では transfer / focal を使わず. Suzuki 定理付録 (05.4) のみで
transfer-evaluation を直接利用 (1 件).

ノート: [`notes/isaacs/ch05_transfer.md`](../../notes/isaacs/ch05_transfer.md)
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise

variable {G : Type*} [Group G]

section /- 5A: Transfer definition + homomorphism (pp. 147-153) -/

/-! ### Isaacs §5A (Transfer 定義)

- **Thm 5.1** (transfer welldef): mathlib `MonoidHom.transfer` 構成時点で transversal
  非依存性が組み込み済. wrapper 不要.
- **Thm 5.2** (transfer 準同型性): 同上, 構造の `map_mul'` フィールドで内包.
- **Thm 5.3** (`p ∣ |G' ∩ Z(G)|` ⇒ Sylow_p(G) は非可換): 短い証明 (transfer 計算で
  `z = z^{|G:P|}` を導出して矛盾). Schur multiplier 補論. 形式化保留 (FT 経路で要求なし).
- **Thm 5.4** (Schur multiplier corollary): Schur multiplier 概念自体 mathlib 未収載.
  FT 経路では不要. 保留. -/

end -- 5A

section /- 5B: Central transfer, Schur, Dietzmann (pp. 153-159) -/

/-! ### Isaacs §5B (中心 transfer, Schur, Dietzmann)

- **Thm 5.6** (中心 transfer = `g ↦ g^n`): mathlib `MonoidHom.transferCenterPow` 直接.
- **Lemma 5.8, Cor 5.9** (`Z(G)` transversal commutator 構造 + `|G:Z|`-乗 = 1):
  形式化保留 (`Subgroup.LeftTransversal` projection の精緻化が要る. FT 経路で要求なし).
- **Thm 5.7 Schur** (`|G:Z(G)| < ∞ ⇒ G' 有限`): mathlib
  `Subgroup.card_commutator_le_of_finite_commutatorSet` 直接 (bound 付き強化版).
- **Thm 5.10 Dietzmann** (`X ⊆ G` 有限・共役閉・∃n, x^n=1 ⇒ `⟨X⟩` 有限):
  mathlib 未収載. Schur 5.7 の証明では mathlib `closureCommutatorRepresentatives` 経路
  で代替されているため独立 Dietzmann の必要なし. 形式化保留. -/

end -- 5B

section /- 5C: Hall transfer, Burnside, cyclic / abelian Sylow (pp. 159-167) -/

/-! ### Isaacs §5C (Hall transfer + Burnside)

- **Lemma 5.11** (Hall index transfer): `ker_transfer_sup_eq_top_of_hall` ✅.
  H π-Hall + ϕ : H →* A + |A| ∣ |H| ⇒ ker(transfer ϕ) · H = G. Lem 3.16 経由 ~25 LOC.
- **Lemma 5.12** (`N_G(P)` controls `C_G(P)` fusion): `normalizer_controls_centralizer_fusion`
  ✅ — Sylow II in C_G(y) + 直接計算.
- **Thm 5.13 Burnside**: `MonoidHom.ker_transferSylow_isComplement'` 直接.
- **Cor 5.14**: `IsCyclic.isComplement'` 直接.
- **Cor 5.15** (Z-group solvable): mathlib `IsZGroup` instance 直接.
- **Thm 5.16-5.17** (Z-group 構造): mathlib `IsZGroup` API 直接.
- **Cor 5.19** (Sylow_2 cyclic direct factor ⇒ 非単純): 形式化保留. -/

/-- **Isaacs Lemma 5.11** (Hall transfer index): `H` が π-Hall 部分群 + `ϕ : H →* A`
(`A` 可換有限群, `|A| ∣ |H|`) ⇒ `ker(transfer ϕ) · H = G`.

**証明** (Isaacs p.159): `transfer ϕ : G →* A` の range ⊆ A から `|G:ker(v)| = |range|`
が `|A|` を割り切る. 仮定 `|A| ∣ |H|` から `|G:ker(v)| ∣ |H|`. Hall 性 `gcd(|H|, |G:H|) = 1`
で `gcd(|G:ker(v)|, |G:H|) = 1`. Lemma 3.16 で `ker(v) ⊔ H = ⊤`.

通常 `A := H/H'` で適用するとき `|A| = |H|/|H'| ∣ |H|` が成立. -/
theorem ker_transfer_sup_eq_top_of_hall [Finite G] {π : Set ℕ}
    {H : Subgroup G} (hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) [H.FiniteIndex]
    {A : Type*} [CommGroup A] [Finite A] (ϕ : H →* A)
    (hAH : Nat.card A ∣ Nat.card H) :
    (MonoidHom.transfer ϕ).ker ⊔ H = ⊤ := by
  apply OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index
  -- (transfer ϕ).ker.index ∣ |A| (1st iso + Lagrange in A)
  have h_range_card : (MonoidHom.transfer ϕ).ker.index ∣ Nat.card A := by
    have heq : Nat.card (G ⧸ (MonoidHom.transfer ϕ).ker) =
        Nat.card (MonoidHom.transfer ϕ).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
    rw [Subgroup.index_eq_card] at *
    rw [heq]
    exact Subgroup.card_subgroup_dvd_card _
  have h_dvd_H : (MonoidHom.transfer ϕ).ker.index ∣ Nat.card H :=
    h_range_card.trans hAH
  -- gcd(ker.index, |G:H|) divides gcd(|H|, |G:H|) = 1 (Hall)
  exact Nat.Coprime.coprime_dvd_left h_dvd_H hHall.coprime_index

/-- **Isaacs Lemma 5.12** (`N_G(P)` controls `C_G(P)` fusion):
`P ∈ Syl_p(G)`, `x, y ∈ C_G(P)` が `G` で共役 (∃ g, gxg⁻¹ = y) ⇒ `N_G(P)` で共役.

**証明** (Isaacs p.161): `y = x^g` (g ∈ G). `x ∈ C_G(P)` から `q ∈ P` は `x` と可換 ⇒
`gqg⁻¹` は `gxg⁻¹ = y` と可換 ⇒ `gPg⁻¹ ⊆ C_G(y)`. 一方 `y ∈ C_G(P)` から `P ⊆ C_G(y)`.
ゆえに `P`, `gPg⁻¹` は `C_G(y)` の Sylow_p. Sylow II in `C_G(y)` で `c ∈ C_G(y)` 存在し
`c (gPg⁻¹) c⁻¹ = P`, i.e., `(cg) ∈ N_G(P)`. `(cg) x (cg)⁻¹ = c y c⁻¹ = y`. -/
theorem normalizer_controls_centralizer_fusion
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {x y g : G}
    (hx : x ∈ Subgroup.centralizer (P : Set G))
    (hy : y ∈ Subgroup.centralizer (P : Set G))
    (hgxy : g * x * g⁻¹ = y) :
    ∃ n : G, n ∈ Subgroup.normalizer (P : Subgroup G) ∧ n * x * n⁻¹ = y := by
  set K : Subgroup G := Subgroup.centralizer ({y} : Set G) with hK_def
  -- y ∈ C_G(P) ⇒ P ≤ K = C_G(y)
  have hP_le_K : (P : Subgroup G) ≤ K := by
    intro q hq z hz
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact (Subgroup.mem_centralizer_iff.mp hy q hq).symm
  -- x ∈ C_G(P) ⇒ gPg⁻¹ ≤ K (using Sylow's G-action via MulAut.conj)
  have hPg_le_K : ((g • P : Sylow p G) : Subgroup G) ≤ K := by
    rw [Sylow.coe_subgroup_smul]
    intro w hw
    -- w = g * q * g⁻¹ for some q ∈ P
    obtain ⟨q, hq_mem, hqw⟩ : ∃ q ∈ (P : Subgroup G), g * q * g⁻¹ = w := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hw
      refine ⟨(MulAut.conj g)⁻¹ w, hw, ?_⟩
      have heq : (MulAut.conj g) ((MulAut.conj g)⁻¹ w) = w :=
        MulAut.apply_inv_self G (MulAut.conj g) w
      simpa [MulAut.conj] using heq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz; subst hz
    have hxq : q * x = x * q := Subgroup.mem_centralizer_iff.mp hx q hq_mem
    -- w * y = (g q g⁻¹) * (g x g⁻¹) = g (q x) g⁻¹ = g (x q) g⁻¹ = (g x g⁻¹) * (g q g⁻¹) = y * w
    rw [← hqw, ← hgxy]
    calc (g * x * g⁻¹) * (g * q * g⁻¹)
        = g * (x * q) * g⁻¹ := by group
      _ = g * (q * x) * g⁻¹ := by rw [← hxq]
      _ = (g * q * g⁻¹) * (g * x * g⁻¹) := by group
  -- Promote to Sylow p K
  let P_K : Sylow p K := P.subtype hP_le_K
  let Pg_K : Sylow p K := (g • P).subtype hPg_le_K
  -- Sylow II in K: there exists c : K with c • Pg_K = P_K
  haveI : Finite K := inferInstance
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := K) Pg_K P_K
  -- Translate back: c • Pg_K = P_K via Sylow.smul_subtype ⇒ (c.val • (g • P)).subtype = P.subtype
  have h_subtype_eq : ((c : G) • g • P).subtype (Sylow.smul_le hPg_le_K c) = P_K := by
    rw [show ((c : G) • g • P).subtype (Sylow.smul_le hPg_le_K c) =
        c • (g • P).subtype hPg_le_K from (Sylow.smul_subtype hPg_le_K c).symm]
    exact hc
  have hcgP : (c : G) • g • P = P := Sylow.subtype_injective h_subtype_eq
  -- (c * g) • P = P, so c * g ∈ N_G(P)
  have hcgP_smul : ((c : G) * g) • P = P := by rw [mul_smul]; exact hcgP
  refine ⟨(c : G) * g, ?_, ?_⟩
  · -- (c * g) ∈ N_G(P)
    rw [← Sylow.smul_eq_iff_mem_normalizer]
    exact hcgP_smul
  · -- (cg) * x * (cg)⁻¹ = c * (g x g⁻¹) * c⁻¹ = c * y * c⁻¹ = y (c ∈ K = C_G(y))
    have hcy : y * (c : G) = (c : G) * y := by
      have hcK : (c : G) ∈ K := c.property
      exact Subgroup.mem_centralizer_iff.mp hcK y (Set.mem_singleton y)
    calc ((c : G) * g) * x * ((c : G) * g)⁻¹
        = (c : G) * (g * x * g⁻¹) * (c : G)⁻¹ := by group
      _ = (c : G) * y * (c : G)⁻¹ := by rw [hgxy]
      _ = y * (c : G) * (c : G)⁻¹ := by rw [← hcy]
      _ = y := by group

/-- **Isaacs Thm 5.18**: `P` abelian Sylow_p ⇒ `G' ∩ P = focalSubgroup P` ((Burnside 強化形).

mathlib `commutator_inf_eq_focalSubgroup` の特殊化 (abelian 仮定は計算を簡略化するのみ).

Isaacs 流のフル statement は `G' ∩ P` と `Z(N_G(P)) ∩ P` が direct factor 形分解だが,
mathlib `commutator_inf_eq_focalSubgroup` で得られる `G' ∩ P = focal P` の方が
Focal Subgroup Theorem の特殊化として扱いやすい. -/
theorem abelian_sylow_commutator_inf_eq_focal
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex] :
    _root_.commutator G ⊓ (P : Subgroup G) = P.focalSubgroup :=
  Subgroup.commutator_inf_eq_focalSubgroup P

end -- 5C

section /- 5D: Focal Subgroup theorem (pp. 167-173) -/

/-! ### Isaacs §5D (Focal Subgroup Theorem)

mathlib `Focal.lean` で Focal Subgroup Theorem が完全実装済 (Boyang Hu, 2026):

- `Subgroup.focalSubgroup`, `focalSubgroupOf`: focal subgroup の定義 (Isaacs §5D 冒頭).
- `Subgroup.transferFocal`: `G →* H/H*` の transfer.
- **`Subgroup.commutator_inf_eq_focalSubgroup`** = **Focal Subgroup Theorem (Thm 5.21)** ⭐.

**Thm 5.20** (ker(v) = A^p(G)) = `ker_restrict_transferFocal_eq_focalSubgroupOf` で同等内容
(Isaacs 流は `A^p(G) = O^p(G) · G'` の表示だが, mathlib では `focalSubgroupOf` 表示で同値).

**Cor 5.22, 5.23** (`H controls fusion ⇒ controls p-transfer`): mathlib transferFocal +
Isaacs 流の "controls fusion" 定義の橋渡し. 形式化保留 (FT 経路で BG 直接引用なし).

**Thm 5.24** (G simple, H maximal nilpotent ⇒ H は p-group; Wielandt): BG/Peterfalvi
直接被引用無し. 保留. -/

end -- 5D

section /- 5E: Frobenius normal p-complement (pp. 173-180) -/

/-! ### Isaacs §5E (Frobenius normal p-complement)

**FT クリティカル**. mathlib 未収載で新規実装が必要. -/

/-! **Isaacs Thm 5.26 Frobenius normal p-complement** ⭐ **FT クリティカル**.
`G` は normal p-complement を持つ ⇔ 任意の p-subgroup `X` で `N_G(X)/C_G(X)` が p-group.

3 同値条件のうち本 statement は (1) ⇔ (3). 5.25 経由で (1) ⇔ (2) (全 p-local 部分群
が normal p-comp) も導出. mathlib 未収載 ~200 LOC 推定.

**証明骨子** (Isaacs p.174-177):
- (1) ⇒ (3): normal p-complement N ⇒ G = N · P (P Sylow_p). 任意 p-subgroup X ⊆ P^g
  に対し N_G(X) = N_N(X) · N_P^g(X) で N/C 部分は p-group のみ.
- (3) ⇒ (1): 5.28 lemma で C_G(P∩Q) 内で P, Q ∈ Syl_p 共役 ⇒ 自分自身の fusion 制御 ⇒
  Thm 5.25 で normal p-complement.

statement 形式化保留 (mathlib `Subgroup.normalizerMonoidHom : N(X) →* MulAut X` 経由
で `image` を p-group とする, あるいは centralizer の subgroupOf normalizer 商を取る
形が考えられる). -/

/-- **Isaacs Cor 5.30** (p odd 中心化): ⭐ **FT 経路で奇数位数仮定との親和性**.
`p` odd, 全 order-`p` 元が `Z(G)` 中心 ⇒ `G` は normal p-complement を持つ.

**証明** (Isaacs p.180): Thm 5.26 で any p-subgroup X に対し N_G(X)/C_G(X) が p-group
を示せばよい. `Q := N_G(X)/C_G(X)` 内の p'-部分 A を取り A が trivial に作用することを
**Ch.4 Thm 4.36** (p>2 + p-群 G + p'-A が order-p 元固定 ⇒ A trivial) で示す. 仮定より
order-p 元は中心で A 不変, 中心で固定 ⇒ Thm 4.36 適用条件成立.

**実装状態**: Ch.4 §4D Thm 4.36 完成待ち. -/
theorem normal_p_complement_of_order_p_central_odd
    [Finite G] {p : ℕ} [Fact p.Prime] (_hp_odd : p ≠ 2)
    (_hCent : ∀ g : G, orderOf g = p → g ∈ Subgroup.center G) :
    ∃ N : Subgroup G, N.Normal ∧
      ∀ P : Sylow p G, Subgroup.IsComplement' N (P : Subgroup G) := by
  sorry

/-! **Isaacs Thm 5.25** (Sylow controls own G-fusion ⇔ normal p-complement):
形式化保留. Focal Subgroup Theorem (5.21) + Sylow conjugacy.

**Lemma 5.27, 5.28** (5.26 の補題): 5.26 実装時に同時実装.

**Cor 5.29** (|G| = p^a m, q ∤ p^e-1 ⇒ normal p-complement): 5.26 + p-group action 計算.
形式化保留. -/

end -- 5E

end OddOrder.Isaacs.Ch05
