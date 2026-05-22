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

- **Lemma 5.11** (Hall index transfer): mathlib 直接対応なし. Hall 性 + transfer 計算で
  導出. 形式化保留 (FT 経路で要求軽).
- **Lemma 5.12** (`N_G(P)` controls `C_G(P)` fusion): mathlib 直接対応なし.
  Sylow conjugacy + 直接計算. 形式化保留.
- **Thm 5.13 Burnside**: `MonoidHom.ker_transferSylow_isComplement'` 直接.
- **Cor 5.14**: `IsCyclic.isComplement'` 直接.
- **Cor 5.15** (Z-group solvable): mathlib `IsZGroup` instance 直接.
- **Thm 5.16-5.17** (Z-group 構造): mathlib `IsZGroup` API 直接.
- **Cor 5.19** (Sylow_2 cyclic direct factor ⇒ 非単純): 形式化保留. -/

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

**FT クリティカル**. mathlib 未収載で新規実装が必要.

- **Thm 5.25** (Sylow controls own G-fusion ⇔ normal p-complement)
- **Thm 5.26 Frobenius** (3 同値条件: normal p-comp / 全 p-local が normal p-comp /
  N_G(X)/C_G(X) is p-group ∀ p-subgroup X)
- **Lemma 5.27, 5.28** (5.26 の補題)
- **Cor 5.29** (|G| = p^a m, q ∤ p^e-1 ⇒ normal p-complement)
- **Cor 5.30** (p odd, 全 order-p 元中心 ⇒ normal p-complement) ⭐ **FT 経路で奇数位数仮定との親和性**.
  Isaacs p.180 の証明は **Ch.4 Thm 4.36** (p>2 一般 p-群 + p'-A が order-p 元全部 fix
  ⇒ A trivial) を直接利用.

**所在**: 全 statement docstring レベル. Ch.4 §4D (4.36) 完成後に再着手. -/

end -- 5E

end OddOrder.Isaacs.Ch05
