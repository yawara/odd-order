/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Submodule
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import OddOrder.GroupTheory.IsExtraspecial
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction
import OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector
import OddOrder.GroupTheory.RepresentationTheory.BaseChange
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch05_Transfer.Main

/-!
# S02_RepresentationsBasic

Prefix-split from `OddOrder.BG.Ch1_Preliminary.S02_Representations` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# BG §2: General Results on Representations

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §2 (pp. 9-16), mmd L586-794, **6 結果**
(Proposition 2.1, Proposition 2.2, Lemma 2.3, Proposition 2.4, Theorem 2.5,
Theorem 2.6).

## 構造 (BG §2 全 6 結果)

§2 を結果単位で 6 つの sub-section に整理:

- **§2A** Schur + absolute irreducibility (**Prop 2.1**, 3 parts a/b/c)
- **§2B** Clifford for cyclic quotient (**Prop 2.2**, 2 parts a/b)
  — Isaacs Ch.6 §6F Clifford gate
- **§2C** Fong–Swan: solvable abs.irred. ⇒ dim ∣ |G| (**Lem 2.3**)
  — forward use 0, defer
- **§2D** Eigenspace decomp under cyclic action (**Prop 2.4**, 10 parts a-k)
  — pure linear algebra
- **§2E** Extraspecial p-group with cyclic action (**Thm 2.5**)
  — IsExtraspecial + AutElementaryAbelian
- **§2F** Odd-order two-dimensional representation (**Thm 2.6**, 2 parts a/b)
  — App.A Thm A.1 gate

## Phase 2a 優先度 (2026-05-23 audit 訂正後)

詳細: `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.

**旧評価** (`notes/bg/s02_representations.md` 2026-05-22 作成):
- "§9 周辺 1-2 箇所のみ被引用, optional, skip 推奨" → **完全に逆**

**新評価** (2026-05-23 audit 実測):
- §2 は **8+ cites**: §3 ×5, §4 Lem 4.17, §15 Thm 15.7,
  **App.A Thm A.1 proof L4464**. §9 への §2 cite は **ZERO**.
- §2 は **Phase 2a 第 1 波必須** (§3 Frobenius + App.A p-Stability の前提).
- Lem 2.3 Fong–Swan のみ forward use **= 0**, defer 可.
- Prop 2.1, Prop 2.2, Prop 2.4, Thm 2.5, Thm 2.6 が必須.

## 結果別 mathlib カバレッジ / shared module 依存

| BG §2 | mathlib v4.29.1 | 新規 shared module |
|---|---|---|
| Prop 2.1(a) | `Representation.IsIrreducible` ✓ | `AbsolutelyIrreducible.lean` |
| Prop 2.1(b) | Jacobson Density (mathlib) ✓ | `EnvelopingAlgebra.lean` |
| Prop 2.1(c) | `LittleWedderburn` ✓ + Schur ✓ | (上記流用) |
| Prop 2.2(a)(b) | Clifford **不在** (`Induced` のみ) | `Clifford.lean` (upstream) |
| Lem 2.3 | (上記 abs.irred. 経由) | — |
| Prop 2.4 (a-k) | `Module.End.eigenspace` 基本 | `EigenspaceUnderCyclicAction.lean` |
| Thm 2.5 | `IsExtraspecial` ✓ (本 repo) | `AutElementaryAbelian.lean` + Prop 2.4 |
| Thm 2.6(a)(b) | `Representation` + `Sylow` + GL(2,F) | `PGroupFixedVector.lean` |

主要 cite: Prop 2.1 ← §3 Thm 3.16; Prop 2.2 ← §3 Thm 3.4 ×2;
Thm 2.5 ← §3 Thm 3.4, §15 Thm 15.7;
Thm 2.6 ← §3 ×2, §4 Lem 4.17, **App.A Thm A.1**.

mathlib `Module.Finite.toModuleEnd_moduleEnd_surjective`
(`SimpleModule/Basic.lean:582`) が Jacobson Density 本体.

## 先行章依存 (BG §1, Isaacs Phase 1)

| BG §2 | 依存 | 状態 (2026-05-24) |
|---|---|---|
| Prop 2.2 | **Isaacs Ch.6 §6F Clifford** | ❌ Ch.6 §6A 部分のみ |
| Thm 2.5 | Isaacs Thm 5.5.4-5 (extraspecial repr) | 対応 Ch.6 §6E? 未 |
| Thm 2.6 | G Lem 2.6.3 (Isaacs FGT 不在) | `PGroupFixedVector.lean` 新規 + `Maschke` |
| Prop 2.1 (a)(b) | Jacobson Density | ✅ mathlib 既存 |
| Prop 2.1 (c) | Wedderburn (`LittleWedderburn`) | ✅ mathlib 既存 |

## 実装 status (2026-05-24)

- **Skeleton + 6 sub-section docstring + mapping table** (本ファイル).
- 全 6 結果 **statement stub 未確定** (依存 shared module 未作成 +
  Isaacs Ch.6 §6F Clifford 未完成).
- 着手順 (audit 推奨):
  1. `RepresentationTheory/PGroupFixedVector.lean` 新規 (~30 行)
     → Thm 2.6 着手
  2. `RepresentationTheory/EigenspaceUnderCyclicAction.lean` 新規
     (~100 行, Prop 2.4 10 部)
  3. `RepresentationTheory/AbsolutelyIrreducible.lean` 新規
     → Prop 2.1 (a)(b)(c)
  4. `RepresentationTheory/AutElementaryAbelian.lean` 新規 → Thm 2.5
  5. Lem 2.3 Fong–Swan は forward use 0 ⇒ defer
  6. Prop 2.2 Clifford は **Isaacs Ch.6 §6F 完成待ち**

## Gorenstein (G) ↔ Isaacs FGT / mathlib / shared module 読み替え

CLAUDE.md L20 方針: BG が **G** として引く Gorenstein, *Finite Groups* (1968)
の定理は Isaacs FGT (2008) に読み替えるが, **§2 は representation theory
中心のため Isaacs FGT (群論本, character theory 章なし) に対応定理が
ほとんど存在しない** (`Clifford` 0 hit in Isaacs mmd; Isaacs Ch.6 は
Frobenius Actions であって Clifford 章ではない). したがって本節は
**mathlib 既存 API + 新規 shared module で再構築する方針** を採用.
詳細マップ: `notes/meta/phase2_cross_refs.md` §5 + 本ファイル下表.

**BG §2 内 G 引用 → 代替経路**:

- **G Thm 3.4.1** (Clifford theorem)
  → Isaacs FGT **不在** (Ch.6 = Frobenius Actions ≠ Clifford 章);
  新規 shared module `RepresentationTheory/Clifford.lean` (mathlib upstream candidate).
- **G Thm 3.5.2** (Schur 補題)
  → Isaacs FGT **不在**; mathlib `Representation.IsIrreducible` +
  `algebraMap_intertwiningMap_bijective_of_isAlgClosed`.
- **G Thm 3.5.7** (既約 ⟺ `Hom_{FG}(M,M) = F`, char 0/coprime case)
  → Isaacs FGT **不在**; mathlib `Representation` + 新規
  `RepresentationTheory/AbsolutelyIrreducible.lean`.
- **G Thm 3.6.2** (Jacobson Density)
  → Isaacs FGT **不在**; mathlib
  `Module.Finite.toModuleEnd_moduleEnd_surjective` ✓.
- **G Lem 2.6.3** (p-group on char-p F-vector ⇒ fixed vec ≠ 0)
  → Isaacs FGT **不在**; mathlib `Representation.Coinvariants` partial
  + 新規 `RepresentationTheory/PGroupFixedVector.lean`.
- **G Thm 5.5.4-5.5.5** (faithful irreducible repr of extraspecial,
  `dim = p^n`)
  → Isaacs FGT **不在**; 新規 shared module (extraspecial faithful
  irreducible repr の構造).
- **G, Wedderburn** (finite division ring = field)
  → Isaacs FGT **不在**; mathlib `LittleWedderburn` ✓.

以下 §2A-§2F 内では `(BG 引用 G X.Y.Z; Isaacs FGT 不在 / mathlib `…`)`
の短縮形で個別注記.

## References

- BG mmd `references/bg/local-analysis.mmd` L586-794
- 節ノート: `notes/bg/s02_representations.md`
- Audit: `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`
- Cross-refs: `notes/meta/phase2_cross_refs.md` §5
- Isaacs FGT 章一覧: 1 Sylow / 2 Subnormality / 3 Split Extensions /
  4 Commutators / 5 Transfer / 6 Frobenius Actions / 7 Thompson Subgroup /
  8 Permutation / 9 More Subnormality / 10 More Transfer
  (= 群論本, character/representation theory 章なし)
-/

namespace OddOrder.BG.Ch1.S02

open scoped Pointwise
open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_apply_tmul
  baseChangeRepresentation_faithful)

/-! ## §2A: Schur + Absolute Irreducibility (Prop 2.1, mmd L598-612)

**BG Prop 2.1**: `G` 群, `F` 体, `M` 既約 `FG`-加群. 以下が成立:

(a) `M` absolutely irreducible ⟺ `Hom_{FG}(M, M) = F`;

(b) `G` が `M` に faithful かつ `Hom_{FG}(M, M) = F`
    ⟹ `Hom_F(M, M) = E(G)`
    (`E(G)` は `G` の `F` 上 enveloping algebra
    = `G` を含む `Hom_F(M, M)` の最小 F-subalgebra);

(c) `F` 有限体 + `K = Hom_{FG}(M, M)` ⟹ `K` は体, かつ
    `M` は absolutely irreducible `KG`-加群.

**証明梗概** (BG L604-612):
- (a): char F = 0 or coprime to |G| ⇒ BG が引く G Thm 3.5.7
  (Isaacs FGT 不在; mathlib `Representation` + `AbsolutelyIrreducible.lean`
  新規 で構築). 一般: Jacobson Density (G Thm 3.6.2 = mathlib
  `Module.Finite.toModuleEnd_moduleEnd_surjective` ✓) or Curtis-Reiner
  Thm 29.13.
- (b): Jacobson Density (mathlib 既存) +
  `Hom_{FG}(M,M) = Hom_{E(G)}(M,M)`.
- (c): Schur 補題 (G Thm 3.5.2; Isaacs FGT 不在; mathlib
  `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`)
  ⇒ K division algebra over F. F 有限 + dim M 有限 ⇒ M, K 有限.
  Wedderburn finite division ring = field (mathlib `LittleWedderburn`)
  ⇒ K field. (a) を K 上適用 ⇒ M abs. irreducible KG-module.

**形式化方針**: `IsAbsolutelyIrreducible` / `EnvelopingAlgebra`
共に mathlib 不在. shared module
`OddOrder/GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean`
で predicate 定義 + 同値 characterization
(`Hom_{FG} = F`) を補題化, この §2A は薄い wrapper に.

**下流引用**: §3 Thm 3.16 (Prop 2.1), §2 内部 (Prop 2.2 で
`E(H) = Hom_F(M,M)`, Thm 2.5 で Prop 2.1 適用).

**Lean signature 案** (未確定):
```
theorem absolutely_irreducible_iff_hom_eq_F
    {F : Type*} [Field F] {G : Type*} [Group G] {M : Type*}
    [AddCommGroup M] [Module F M] [Module.Finite F M]
    (ρ : Representation F G M) (hM : ρ.IsIrreducible) :
    IsAbsolutelyIrreducible ρ ↔
      ∀ φ : ρ.asModule →ₗ[MonoidAlgebra F G] ρ.asModule,
        ∃ c : F, φ = c • LinearMap.id
```

(stub 未配置: `IsAbsolutelyIrreducible` shared module 完成後に
statement 確定.)
-/

/-! ## §2B: Clifford for Cyclic Quotient (Prop 2.2, mmd L614-652)

**BG Prop 2.2**: `G` 群, `H ⊴ G`, `G/H` cyclic. `F` 代数閉体,
`M` 既約 `FH`-加群, 全 `x ∈ G` に対し `M ≅ M^x` (共役加群).
以下が成立:

(a) `L` 既約 `FG`-加群 + `M ↪ L_H` (制限の部分加群)
    ⟹ `L_H ≅ M`
    (= 制限が `M` の 1 重複, hence `M` 上 `H`-表現は `G`
    への extension を持つ).

(b) `H` 上 `M` の表現は `G` の表現に拡張可.

**証明梗概** (BG L617-652):
- (a): Clifford theorem (G Thm 3.4.1; **Isaacs FGT 不在** —
  Isaacs Ch.6 は Frobenius Actions であって Clifford 章ではない;
  新規 shared module `RepresentationTheory/Clifford.lean` で構築)
  ⇒ `L_H = M_1 ⊕ ⋯ ⊕ M_k`
  (各 `M_i ≅ M`). `G = ⟨H, x⟩` (`x` cyclic generator).
  `M ≅ M^{x^{-1}}` ⇒ `τ ∈ E(H) = Hom_F(M,M)` で
  `(mh)τ = (mτ)(xhx⁻¹)`. `τ` を `L` に延長 (各 `M_i` で同様),
  `τx ∈ Hom_{FG}(L, L) = F` (Prop 2.1, `F` 代数閉 + `L` 既約
  ⇒ scalar). `M_1·τ = M_1` ⇒ `M_1 = M_1·τx = M_1·x`, よって
  `M_1` は `G`-submodule, `L = M_1`.
- (b): `L` を `M^G` (induced module) の既約 `FG`-submodule
  とすれば (a) より `L_H ≅ M`.

**形式化方針**:
- Clifford theorem (mathlib 不在) は **Isaacs Ch.6 §6F で実装予定**.
- 本節は Isaacs Ch.6 完成 **必須前提** (audit 確認).
- shared module `OddOrder/GroupTheory/RepresentationTheory/Clifford.lean`
  で Clifford decomposition + 引用 wrapper.
- ⊕ 直和分解は mathlib `DirectSum.isInternal_*` API で.
- 共役加群 `M^x`: `Representation` 引数を `g ↦ ρ (x⁻¹ g x)` で twist.

**下流引用**: §3 Thm 3.4 ×2 (BG §3 Frobenius), §2C Lem 2.3 内部
(`Prop 2.2` 直接適用).

**Phase 1 gate**: ❌ **Isaacs Ch.6 §6F Clifford 未完成
(現状 §6A 部分のみ)**. 本節は §2 全体の最後に着手予定.

(stub 未配置: Clifford shared module + Isaacs Ch.6 待ち.)
-/

/-! ## §2C: Fong–Swan (Lem 2.3, mmd L655-668)

**BG Lemma 2.3**: `G` 可解群, `F` 体, `M` absolutely irreducible
`FG`-加群. ⟹ `dim M ∣ |G|`.

**注 (BG L657)**: これは Fong–Swan の有名定理
[5, Thm 72.1, p.473] の系.

**証明梗概** (BG L659-668): 帰納法 (|G| について).
1. `H ⊴ G`, prime index `p` (§1 Lem 1.1 = 可解 ⇒ 任意有限商 abelian).
2. `L ⊆ M_H` 既約 submodule. 帰納仮説 ⇒ `dim L ∣ |H|` ... (2.5).
3. `x ∈ G - H`. Case `L ≅ L^x`: Prop 2.2 ⇒ `L = M_H`
   ⇒ `dim M ∣ |H| · p = |G|`.
4. Case `L ≁ L^x`: `M_H = L ⊕ Lx ⊕ ⋯ ⊕ Lx^{p-1}` (pairwise
   nonisomorphic, sum direct), `dim M = p · dim L ∣ p · |H| = |G|`.

**形式化方針**:
- Prop 2.2 + `IsSolvable` 帰納 + Module restrict/induce で.
- 依存 chain: §2B Prop 2.2 ⟸ Isaacs Ch.6 §6F Clifford 完成必須.

**下流引用**: **0** (audit 実測). §9 にも cite 無し (旧ノート誤り).

**Phase 2a 優先度**: **defer** (Wave 2 以降 or skip 可).
audit 推奨「forward use 0 ⇒ defer」.

(stub 未配置: forward dependent 不在のため §2 完成後または
Phase 2a 完成後に判断.)
-/

/-! ## §2D: Eigenspace Decomposition (Prop 2.4, mmd L670-712)

**BG Prop 2.4** (純粋線型代数): `V` 体 `F` 上, `dim V = q ≥ 2`,
`g : V →L[F] V` 可逆, `g` の位数 `h ≥ 2`, `F` は primitive `h` 乗根
`ε` を含む. 以下を定義:

- `E = End_F(V)`
- `V_i = { v ∈ V | v·g = ε^i · v }` (eigen space for `ε^i`)
- `n_i = dim V_i`
- `E_i = { e ∈ E | e^g = g⁻¹·e·g = ε^i · e }`
- `E_{i,t} = { e ∈ E | V_i · e ⊆ V_t, V_j · e = 0 (j ≠ i) }`

以下が成立 (a-k, 10 部):

(a) `V = V_0 ⊕ V_1 ⊕ ⋯ ⊕ V_{h-1}`;
(b) `n_i = n_{i+h}` for all i;
(c) `E = ⊕_{0≤i,t≤h-1} E_{i,t}`;
(d) `dim E_{i,t} = n_i · n_t`;
(e) `E_{i,t} ⊆ E_{t-i}`;
(f) `E_m = ⊕_{t-i ≡ m (mod h)} E_{i,t}`;
(g) `dim E_m = ∑_i n_i · n_{i+m}`;
(h) `2 dim E_0 - 2 dim E_m = ∑_i (n_i - n_{i+m})²`;
(j) `dim E_0 = dim E_m + 1 (∀ m ≢ 0)` ⟹ ∃ i, n, δ = ±1
    s.t. `q = h·n + δ`, `n_i = n + δ`, `n_j = n (j ≢ i mod h)`;
(k) (j) の仮定下 `dim V_0 = n_0 > 0`
    (例外: `n = 1, i = 0, δ = -1, h = q + 1`).

**証明梗概** (BG L693-712):
- `F` が primitive h 乗根を含む ⟹ char F ∤ h.
- (a)(b) 直接.
- (c)(d) `V_i` の基底をまとめて `V` の基底, 行列の `h × h` ブロック分割.
- (e) 直接計算.
- (f) ← (c) + (e); (g) ← (d) + (f); (h) ← (b) + (g).
- (j) `S_1 = {i : n_i = n_0}`, `S_2 = complement`. (h) m=1 で sum
  制約計算で `|n_0 - n_j| = 1`, `S_1` or `S_2` size = 1
  (size ≥ 2 で矛盾 via m=2 計算).
- (k) `hn + δ = q ≥ 2` ⟹ `n ≥ 1`.

**Curtis Bennett (BG L713)**: 元の証明の簡略化に貢献.

**形式化方針**:
- 純線型代数 (group theory なし). mathlib `Module.End` +
  `Module.End.eigenspace` 既存.
- shared module
  `OddOrder/GroupTheory/RepresentationTheory/EigenspaceUnderCyclicAction.lean`
  で 10 部を順次. (a)(b)(c)(d) は短い, (j)(k) は計算重.
- `Module.End.IsSemisimple` (char F ∤ h で diagonalizable) を経由.

**下流引用**: §2E Thm 2.5 内部 ((j),(k) が鍵).

(stub 未配置: 10 部を個別 lemma 化, shared module 作成後.)
-/

/-! ## §2E: Extraspecial p-Group with Cyclic Action (Thm 2.5, mmd L716-772)

**BG Theorem 2.5**: `P` extraspecial `p`-group of order `p^{2n+1}`
for some prime `p`. `G = P ⋊ H` (semidirect, `P ⊴ G`), `H` cyclic
of order `h`, `gcd(h, p) = 1`, `∀ x ∈ H^#, C_P(x) = Z(P)`
(`H` の非自明元による P 固定点は中心のみ). `F` 体,
`char F ∤ |G|`. 以下が成立:

- `h ∣ p^n + 1` または `h ∣ p^n - 1`;
- `h ≠ p^n + 1` ⟹ 任意の faithful, 既約 `FG`-加群 `V` に対し
  `C_V(H) ≠ 0`.

**注 (BG L724)**: 末尾の `C_V(H) ≠ 0` 部分は `h = p^n + 1` を許すと
反例あり: `p^n = 2, h = 3, G ≅ SL(2,3)`, `F` 素数標数 (`∤ |G|`) or
代数閉零標数.

**証明梗概** (BG L726-772):
1. (L727-735) `Z(P)` 上 nontrivially 作用する既約 `FG`-加群 存在
   (`char F ∤ |G|` + faithful から). `C_V(Z(P)) = 0` (G-invariant),
   `F^* = F̄`, `V^* = F^* ⊗_F V`,
   `dim_{F^*} C_{V^*}(H) = dim_F C_V(H)` (rank 不変),
   `C_{V^*}(Z(P)) = 0`.
2. (L737-744) `W ⊆ V^*` 既約 `G`-submodule, `M ⊆ V^*` 既約 `P`-submodule.
   P extraspecial ⇒ `|Z(P)| = p`, `P` の任意の非自明 normal は `Z(P)`
   含む ⇒ `P` が `M, W` に faithful. `G` も `W` に faithful.
3. (L744-746) `F = F^*` and `W = V` と仮定可.
4. (L747-755) **G Thm 5.5.4-5.5.5** (faithful, irreducible repr of
   extraspecial group; **Isaacs FGT 不在** — 表現論の章なし;
   新規 shared module で「extraspecial の faithful irreducible repr は
   `dim = p^n` で center 作用で一意」を構築): `dim M = p^n` (= `q`).
   `M = V_P` (= `V` の `P` 制限).
5. (L757-762) Prop 2.1 ⇒ `E(P) = Hom_F(V, V)`.
   `E(P) = ⊕_{g ∈ R} F·g` (`R` = coset reps of `Z(P)`).
   `|R| = p^{2n} = q^2 = dim E`, sum direct.
6. (L764-770) BG §1 Prop 1.5: `C_{P/Z}(x) = C_P(x)Z/Z = 1`.
   `a ∈ P - Z` の H-conjugates は別 cosets に. `R` = 1 +
   `(q^2 - 1)/h` `H`-class 代表. `H` の `E` 上 conjugation 作用:
   principal module 1 個 + `(q^2 - 1)/h` 回 regular module.
7. (L770-772) Prop 2.4(j) の仮定確認 ⇒ `p^n = q = hn' + δ`
   (`δ = ±1`), `h ∣ p^n - δ`. Prop 2.4(k) ⇒ `C_V(H) = 0`
   ⟹ `h = q + 1 = p^n + 1`.

**形式化方針**:
- `IsExtraspecial p P` ✓ (本 repo `OddOrder/GroupTheory/IsExtraspecial.lean`
  既存).
- `G = P ⋊ H` は `SemidirectProduct` (mathlib).
- 依存: Prop 2.1 (Schur), Prop 2.4 (j)(k), BG §1 Prop 1.5
  (A-invariant Hall), Isaacs Ch.6 (Thm 5.5.4-5 extraspecial repr
  対応 = Phase 1 Ch.6 §6E?).
- shared module `RepresentationTheory/AutElementaryAbelian.lean`
  (`Aut(elem ab order p^n) ≃ GL(n, F_p)`).

**下流引用**: §3 Thm 3.4 (Frobenius), §15 Thm 15.7.

**Phase 1 gate**: Isaacs Thm 5.5.4-5 対応 (Ch.6 §6E?) + Prop 2.4 完成.

(stub 未配置: 依存定理多数, foundation 整備後に着手.)
-/

/-! ## §2F: Odd-Order Two-Dim Representation (Thm 2.6, mmd L774-793)

**BG Theorem 2.6**: `G` 有限奇数位数群, `F` 体, `V` faithful `FG`-加群
with `dim V = 2`. 以下が成立:

(a) `char F ∤ |G|` ⟹ `G` abelian.

(b) `char F = p ∣ |G|` ⟹ `G` の Sylow `p`-subgroup は abelian かつ
    `G'` を含む.

**証明梗概** (BG L779-793 + PDF p.29 補完): 帰納法 (|G| について).
1. (L779-784) `G ⊆ GL(V, F)`. `G^* = G ∩ SL(V, F)`. `F` 代数閉と仮定可
   (tensor extension). `p = char F`.
2. (L785-787) `O_q(G^*) ≠ 1` を仮定 (some prime q).
   `K = Ω_1(Z(O_q(G^*)))`. `K` elementary abelian q-group, `K ⊴ G`.
   Case 分岐 q = p / q ≠ p.
3. **Case q = p**: `W = C_V(K)`. G Lem 2.6.3 (p-group on char-p F-vector
   ⇒ fixed vector ≠ 0; **Isaacs FGT 不在**; 新規 shared module
   `RepresentationTheory/PGroupFixedVector.lean` で構築 — mathlib
   `Representation.Coinvariants` から partial 構築可) ⟹ `W ≠ 0`.
   `dim V = 2` + `G` faithful ⟹ `dim W = dim V/W = 1`.
   `W` は `G`-invariant. `C = C_G(W) ∩ C_G(V/W)` は elementary abelian
   p-group で, すべての p-element と `G'` を含む. よって (b).
4. **Case q ≠ p**: Maschke + `K` abelian + `F` 代数閉より
   `V = W₁ ⊕ W₂` (one-dimensional `FK`-modules). `x ∈ K#` の
   固定する 1 次元部分空間は `W₁, W₂` のみ. `K ⊴ G` なので各 `g ∈ G`
   はこれらを固定または交換するが, `|G|` が奇数なので交換できず固定する.
   したがって `G` は abelian p'-group となり (a) を適用.
5. 一般に `G^* ≠ 1` なら, `G^*` が p-group の場合は `O_p(G^*) ≠ 1`.
   そうでなければ `q ≠ p` の Sylow `Q ≤ G^*` と `H = N_{G^*}(Q)` を取り,
   `O_q(H) ≠ 1`. 前段落より `H` は abelian なので Burnside (Thm 1.18)
   で `G^*` は `Q` の normal complement `N` を持つ. `N = 1` または
   induction により `O_r(N) ≠ 1`, いずれも前段の normal q/r-core case に帰着.
6. 最後に `G^* = 1` なら determinant で `G ↪ Fˣ`, よって `G` は abelian
   p'-group.

**形式化方針**:
- mathlib `Sylow` ✓, `Matrix.GeneralLinearGroup` ✓, `Module.finrank` ✓.
- 依存: G Lem 2.6.3 (p-group fixed vector; Isaacs FGT 不在;
  mathlib partial), shared module
  `OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean`
  (~30 行) で新規構築.
- 奇数位数: `Odd (Nat.card G)`.
- 帰納構造: `(Nat.card G).strongRecOn` または `WellFoundedLT`.
- PDF p.29 は 2026-05-25 に `pdftotext -f 29 -l 29 -layout` で補完済み.

**下流引用** (audit 実測):
- §3 ×2 (Frobenius)
- §4 Lem 4.17
- **App.A Thm A.1 proof L4464** (BG §6 Thm 6.1, 6.2 の p-stability
  経由証明の前提)

**Phase 2a 第 1 波必須**: App.A → §6 → §7-§16 の長い chain の頂点.

**実装難度**: 中-高 (induction + GL(2,F) 計算 + missing page 補完).

**Lean signature 案** (未確定):
```
theorem odd_two_dim_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hchar : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → ¬ CharP F p) :
    IsMulCommutative G

theorem odd_two_dim_sylow_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    (hchar : CharP F p) (P : Sylow p G) :
    IsMulCommutative P ∧ commutator G ≤ (P : Subgroup G)
```

**Lean status** (2026-05-27): 本節 §2F (Thm 2.6 (a)(b)) は **証明完了**、
本ファイル全体 **sorry-free** (帰納 + GL(2,F) 計算 + 旧 MISSING_PAGE:29 を補完済)。
`PGroupFixedVector` shared module の `IsPGroup.invariants_ne_bot` /
`exists_fixed_vector_ne_zero` も sorry-free
([OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean]
(../../GroupTheory/RepresentationTheory/PGroupFixedVector.lean)).
-/

/-! ### §2F helper lemmas -/

/-- A permutation of a two-point set with odd order is trivial.

Used in BG Thm 2.6: if an odd-order group fixes or interchanges two
one-dimensional subspaces, it must fix both. -/
private theorem perm_fin_two_eq_one_of_odd_order
    (σ : Equiv.Perm (Fin 2)) (hodd : Odd (orderOf σ)) : σ = 1 := by
  have hcard : Nat.card (Equiv.Perm (Fin 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hdvd : orderOf σ ∣ 2 := by
    have h := orderOf_dvd_natCard σ
    rwa [hcard] at h
  have hle : orderOf σ ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  have hpos : 0 < orderOf σ := orderOf_pos σ
  have hne2 : orderOf σ ≠ 2 := by
    intro h
    exact hodd.not_two_dvd_nat (by rw [h])
  have horder : orderOf σ = 1 := by omega
  exact orderOf_eq_one_iff.mp horder

/-- An odd-order finite group acts trivially on any two-point set.

This formalizes the BG p.29 step: an element of `G` cannot interchange the
two one-dimensional `K`-submodules because that would induce a nontrivial
permutation of order two. -/
theorem smul_fin_two_eq_self_of_odd_card
    {G : Type*} [Group G] [Finite G] [MulAction G (Fin 2)]
    (hodd : Odd (Nat.card G)) (g : G) (i : Fin 2) : g • i = i := by
  let σ : Equiv.Perm (Fin 2) := MulAction.toPermHom G (Fin 2) g
  have hgo : Odd (orderOf g) := hodd.of_dvd_nat (orderOf_dvd_natCard g)
  have hσ_dvd : orderOf σ ∣ orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    change (MulAction.toPermHom G (Fin 2) g) ^ orderOf g = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hσodd : Odd (orderOf σ) := hgo.of_dvd_nat hσ_dvd
  have hσ : σ = 1 := perm_fin_two_eq_one_of_odd_order σ hσodd
  change σ i = i
  rw [hσ]
  rfl

/-- In characteristic `p`, a field element whose `p^n`-th power is `1` is `1`.

This is the scalar calculation used in BG Thm 2.6, q = p: the multiplicative
group of a characteristic-`p` field has no nontrivial `p`-power torsion. -/
private theorem eq_one_of_pow_prime_pow_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    (x : F) {n : ℕ} (hx : x ^ p ^ n = 1) : x = 1 := by
  have hsub : (x - 1) ^ p ^ n = 0 := by
    rw [sub_pow_char_pow_of_commute p n (Commute.one_right x), hx, one_pow, sub_self]
  have hxsub : x - 1 = 0 := eq_zero_of_pow_eq_zero hsub
  exact sub_eq_zero.mp hxsub

/-- Unit-valued version of `eq_one_of_pow_prime_pow_eq_one`. -/
private theorem unit_eq_one_of_pow_prime_pow_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    (u : Fˣ) {n : ℕ} (hu : u ^ p ^ n = 1) : u = 1 := by
  ext
  exact eq_one_of_pow_prime_pow_eq_one (p := p) (u : F) (by
    simpa using congrArg Units.val hu)

/-- A p-group has no nontrivial scalar characters over a characteristic-`p` field. -/
private theorem monoidHom_units_eq_one_of_isPGroup_charP
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (hG : IsPGroup p G) {F : Type*} [Field F] [CharP F p]
    (φ : G →* Fˣ) : φ = 1 := by
  ext g
  obtain ⟨n, hg⟩ := hG g
  exact congrArg Units.val <|
    unit_eq_one_of_pow_prime_pow_eq_one (p := p) (φ g) (n := n) (by
      rw [← map_pow, hg, map_one])

/-- Pointwise form of `monoidHom_units_eq_one_of_isPGroup_charP`. -/
theorem monoidHom_units_apply_eq_one_of_isPGroup_charP
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (hG : IsPGroup p G) {F : Type*} [Field F] [CharP F p]
    (φ : G →* Fˣ) (g : G) : φ g = 1 :=
  congrArg (fun ψ : G →* Fˣ => ψ g)
    (monoidHom_units_eq_one_of_isPGroup_charP hG φ)

/-- The image of a p-group scalar character is the trivial subgroup in characteristic `p`. -/
private theorem monoidHom_units_range_eq_bot_of_isPGroup_charP
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (hG : IsPGroup p G) {F : Type*} [Field F] [CharP F p]
    (φ : G →* Fˣ) : φ.range = ⊥ := by
  rw [monoidHom_units_eq_one_of_isPGroup_charP hG φ]
  simp

/-- Sylow-subgroup specialization of `monoidHom_units_eq_one_of_isPGroup_charP`. -/
private theorem sylow_monoidHom_units_eq_one_of_charP
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (P : Sylow p G) {F : Type*} [Field F] [CharP F p]
    (φ : P →* Fˣ) : φ = 1 :=
  monoidHom_units_eq_one_of_isPGroup_charP P.isPGroup' φ

/-- A nonzero proper submodule of a two-dimensional vector space has dimension one,
and so does its quotient. -/
theorem rank_one_subquotients_of_finrank_two
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (hdim : Module.finrank F V = 2)
    (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    Module.finrank F W = 1 ∧ Module.finrank F (V ⧸ W) = 1 := by
  have hW_pos : 1 ≤ Module.finrank F W := by
    rw [Submodule.one_le_finrank_iff]
    exact hW_ne_bot
  have hW_lt : Module.finrank F W < 2 := by
    have hlt : Module.finrank F W < Module.finrank F V :=
      Submodule.finrank_lt hW_ne_top
    simpa [hdim] using hlt
  have hdimW : Module.finrank F W = 1 := by
    omega
  have hsum : Module.finrank F (V ⧸ W) + Module.finrank F W = 2 := by
    simpa [hdim] using W.finrank_quotient_add_finrank
  refine ⟨hdimW, ?_⟩
  omega

/-- If a rank-one submodule has a complement in a two-dimensional space, then
the complementary submodule and its quotient are rank one as well. -/
private theorem complement_rank_one_right_subquotients_of_finrank_two
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U : Submodule F V) (hdim : Module.finrank F V = 2)
    (hcompl : IsCompl W U) (hWdim : Module.finrank F W = 1) :
    Module.finrank F U = 1 ∧ Module.finrank F (V ⧸ U) = 1 := by
  have hsum : Module.finrank F W + Module.finrank F U = Module.finrank F V := by
    simpa using Submodule.finrank_add_eq_of_isCompl hcompl
  have hUdim : Module.finrank F U = 1 := by
    omega
  have hU_ne_bot : U ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  have hU_ne_top : U ≠ ⊤ := by
    intro hU_top
    have h12 : (1 : ℕ) = 2 := by
      calc
        1 = Module.finrank F U := hUdim.symm
        _ = Module.finrank F (⊤ : Submodule F V) := by rw [hU_top]
        _ = Module.finrank F V := finrank_top F V
        _ = 2 := hdim
    omega
  exact ⟨hUdim,
    (rank_one_subquotients_of_finrank_two U hdim hU_ne_bot hU_ne_top).2⟩

/-- Two rank-one submodules with nonzero intersection are equal. -/
private theorem eq_of_rank_one_submodules_inf_ne_bot
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {W U : Submodule F V}
    (hWdim : Module.finrank F W = 1) (hUdim : Module.finrank F U = 1)
    (hinf : W ⊓ U ≠ ⊥) :
    W = U := by
  have hinf_pos : 1 ≤ Module.finrank F (W ⊓ U : Submodule F V) := by
    rw [Submodule.one_le_finrank_iff]
    exact hinf
  have hinf_le_W :
      Module.finrank F (W ⊓ U : Submodule F V) ≤ Module.finrank F W :=
    Submodule.finrank_mono inf_le_left
  have hinf_le_U :
      Module.finrank F (W ⊓ U : Submodule F V) ≤ Module.finrank F U :=
    Submodule.finrank_mono inf_le_right
  have hinf_dim_W :
      Module.finrank F (W ⊓ U : Submodule F V) = Module.finrank F W := by
    omega
  have hinf_dim_U :
      Module.finrank F (W ⊓ U : Submodule F V) = Module.finrank F U := by
    omega
  have hW : W ⊓ U = W :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left hinf_dim_W
  have hU : W ⊓ U = U :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right hinf_dim_U
  exact hW.symm.trans hU

/-- A rank-one invariant submodule of a two-line diagonal action lies on one
of the two eigenspaces.

This is the linear-algebra core of the BG Thm 2.6 q≠p sentence that, after
choosing `x ∈ K#` with distinct eigenvalues on the two Maschke lines, those
two lines are the only one-dimensional `K`-submodules. -/
theorem rank_one_invariant_submodule_eq_left_or_right_of_distinct_scalars
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U L : Submodule F V) (f : Module.End F V)
    (hcompl : IsCompl W U)
    (hWdim : Module.finrank F W = 1) (hUdim : Module.finrank F U = 1)
    (hLdim : Module.finrank F L = 1)
    (hLstable : L ≤ L.comap f)
    (a b : F) (hab : a ≠ b)
    (hWscalar : ∀ w ∈ W, f w = a • w)
    (hUscalar : ∀ u ∈ U, f u = b • u) :
    L = W ∨ L = U := by
  have hL_ne_bot : L ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  rcases Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hL_ne_bot) with
    ⟨l, hl_ne_zero⟩
  let v : V := l
  have hvL : v ∈ L := l.2
  obtain ⟨w, u, hv, _huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
  have hab_sub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba_sub : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hw_mem_L : (w : V) ∈ L := by
    have hdiff_mem : f v - b • v ∈ L :=
      L.sub_mem (hLstable hvL) (L.smul_mem b hvL)
    have hdiff_eq : f v - b • v = (a - b) • (w : V) := by
      rw [← hv, map_add, hWscalar (w : V) w.2, hUscalar (u : V) u.2]
      module
    have hscaled : (a - b) • (w : V) ∈ L := by
      simpa [hdiff_eq] using hdiff_mem
    exact (L.smul_mem_iff hab_sub).mp hscaled
  have hu_mem_L : (u : V) ∈ L := by
    have hdiff_mem : f v - a • v ∈ L :=
      L.sub_mem (hLstable hvL) (L.smul_mem a hvL)
    have hdiff_eq : f v - a • v = (b - a) • (u : V) := by
      rw [← hv, map_add, hWscalar (w : V) w.2, hUscalar (u : V) u.2]
      module
    have hscaled : (b - a) • (u : V) ∈ L := by
      simpa [hdiff_eq] using hdiff_mem
    exact (L.smul_mem_iff hba_sub).mp hscaled
  by_cases hw_zero : (w : V) = 0
  · right
    have hvU : v ∈ U := by
      rw [← hv, hw_zero, zero_add]
      exact u.2
    apply eq_of_rank_one_submodules_inf_ne_bot hLdim hUdim
    intro hbot
    have hv_inf : v ∈ L ⊓ U := ⟨hvL, hvU⟩
    have hv_zero : v = 0 := by
      have : v ∈ (⊥ : Submodule F V) := by simpa [hbot] using hv_inf
      simpa using this
    exact hl_ne_zero (Subtype.ext hv_zero)
  by_cases hu_zero : (u : V) = 0
  · left
    have hvW : v ∈ W := by
      rw [← hv, hu_zero, add_zero]
      exact w.2
    apply eq_of_rank_one_submodules_inf_ne_bot hLdim hWdim
    intro hbot
    have hv_inf : v ∈ L ⊓ W := ⟨hvL, hvW⟩
    have hv_zero : v = 0 := by
      have : v ∈ (⊥ : Submodule F V) := by simpa [hbot] using hv_inf
      simpa using this
    exact hl_ne_zero (Subtype.ext hv_zero)
  · have hLW : L = W := by
      apply eq_of_rank_one_submodules_inf_ne_bot hLdim hWdim
      intro hbot
      have hw_inf : (w : V) ∈ L ⊓ W := ⟨hw_mem_L, w.2⟩
      have hw_bot : (w : V) ∈ (⊥ : Submodule F V) := by
        simpa [hbot] using hw_inf
      exact hw_zero (by simpa using hw_bot)
    have hLU : L = U := by
      apply eq_of_rank_one_submodules_inf_ne_bot hLdim hUdim
      intro hbot
      have hu_inf : (u : V) ∈ L ⊓ U := ⟨hu_mem_L, u.2⟩
      have hu_bot : (u : V) ∈ (⊥ : Submodule F V) := by
        simpa [hbot] using hu_inf
      exact hu_zero (by simpa using hu_bot)
    have hWU : W = U := hLW.symm.trans hLU
    have hW_ne_bot : W ≠ ⊥ := by
      rw [← Submodule.one_le_finrank_iff]
      omega
    have hW_eq_bot : W = ⊥ := by
      have hWinf : W ⊓ U = W := by rw [hWU, inf_idem]
      simpa [hcompl.inf_eq_bot] using hWinf.symm
    exact False.elim (hW_ne_bot hW_eq_bot)

/-- Pointwise scalar form of the rank-one endomorphism theorem. -/
private theorem exists_scalar_apply_of_finrank_eq_one
    {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (f : Module.End F M) :
    ∃ c : F, ∀ m : M, f m = c • m := by
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim f
  refine ⟨c, ?_⟩
  intro m
  simpa using congrArg (fun u : Module.End F M => u m) hc

/-- A representation on a one-dimensional module has a scalar monoid character. -/
private noncomputable def scalarMonoidHomOfFinrankEqOne
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) : G →* F where
  toFun g := (LinearEquiv.smul_id_of_finrank_eq_one hdim).symm (ρ g)
  map_one' := by
    let e := LinearEquiv.smul_id_of_finrank_eq_one hdim
    apply e.injective
    ext m
    simp [e]
  map_mul' g h := by
    let e := LinearEquiv.smul_id_of_finrank_eq_one hdim
    let cg : F := e.symm (ρ g)
    let ch : F := e.symm (ρ h)
    have hg_apply : ∀ m : M, ρ g m = cg • m := by
      intro m
      have hg_eq : e cg = ρ g := by simp [cg]
      simpa [e] using congrArg (fun u : Module.End F M => u m) hg_eq.symm
    have hh_apply : ∀ m : M, ρ h m = ch • m := by
      intro m
      have hh_eq : e ch = ρ h := by simp [ch]
      simpa [e] using congrArg (fun u : Module.End F M => u m) hh_eq.symm
    apply e.injective
    change e (e.symm (ρ (g * h))) = e (cg * ch)
    rw [e.apply_symm_apply]
    ext m
    change ρ (g * h) m = (cg * ch) • m
    rw [map_mul]
    change ρ g (ρ h m) = (cg * ch) • m
    rw [hh_apply, hg_apply]
    exact (mul_smul cg ch m).symm

/-- The scalar monoid character indeed describes the representation action. -/
private theorem scalarMonoidHomOfFinrankEqOne_apply_smul
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) (g : G) (m : M) :
    ρ g m = (scalarMonoidHomOfFinrankEqOne hdim ρ g : F) • m := by
  let e := LinearEquiv.smul_id_of_finrank_eq_one hdim
  change ρ g m = e (e.symm (ρ g)) m
  rw [e.apply_symm_apply]

/-- The scalar monoid character of a group representation on a one-dimensional module
lands in units. -/
noncomputable def scalarCharacterOfFinrankEqOne
    {F : Type*} [Field F] {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) : G →* Fˣ :=
  let ψ := scalarMonoidHomOfFinrankEqOne hdim ρ
  { toFun := fun g =>
      { val := ψ g
        inv := ψ g⁻¹
        val_inv := by
          have h := map_mul ψ g g⁻¹
          simpa using h.symm
        inv_val := by
          have h := map_mul ψ g⁻¹ g
          simpa using h.symm }
    map_one' := by
      ext
      simp [ψ]
    map_mul' := by
      intro g h
      ext
      exact map_mul ψ g h }

/-- The unit-valued scalar character describes the representation action. -/
theorem scalarCharacterOfFinrankEqOne_apply_smul
    {F : Type*} [Field F] {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) (g : G) (m : M) :
    ρ g m = (scalarCharacterOfFinrankEqOne hdim ρ g : F) • m :=
  scalarMonoidHomOfFinrankEqOne_apply_smul hdim ρ g m

/-- A scalar endomorphism of a one-dimensional module has that scalar as determinant. -/
theorem det_eq_scalar_of_finrank_eq_one
    {F : Type*} [Field F]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (f : Module.End F M) (c : F)
    (hf : ∀ m : M, f m = c • m) :
    LinearMap.det f = c := by
  have hf_eq : f = c • (LinearMap.id : Module.End F M) := by
    ext m
    simpa using hf m
  calc
    LinearMap.det f = LinearMap.det (c • (LinearMap.id : Module.End F M)) := by
      rw [hf_eq]
    _ = c := by
      simp [hdim]

open scoped IsMulCommutative in
/-- Irreducible representations of an abelian group over an algebraically closed
field are one-dimensional.

This is the BG Thm 2.6 q≠p input from **G**, Thm 3.2.4, expressed for
mathlib `Representation`s.  The proof crosses to the group algebra module and
uses the commutativity of the group algebra, so it is not just a theorem rename. -/
private theorem finrank_eq_one_of_irreducible_representation_of_commutative_group
    {F : Type*} [Field F] [IsAlgClosed F] {K : Type*} [Group K]
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Finite F M]
    (σ : Representation F K M) [Representation.IsIrreducible σ] :
    Module.finrank F M = 1 := by
  haveI : IsMulCommutative K := ⟨hKcomm⟩
  letI : AddCommGroup σ.asModule := Representation.instAddCommGroupAsModule σ
  letI : Module F σ.asModule := Representation.instModuleAsModule σ
  letI : Module (MonoidAlgebra F K) σ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule σ
  have hfinite : Module.Finite F σ.asModule := inferInstance
  haveI : IsMulCommutative (MonoidAlgebra F K) := inferInstance
  have hmodule :
      Module.finrank F σ.asModule = 1 :=
    @IsSimpleModule.finrank_eq_one_of_isMulCommutative
      (MonoidAlgebra F K) σ.asModule F
      inferInstance inferInstance inferInstance
      (Representation.instAddCommGroupAsModule σ)
      (Representation.instModuleAsModule σ)
      (Representation.instModuleMonoidAlgebraAsModule σ)
      inferInstance inferInstance hfinite inferInstance inferInstance
  exact σ.asModuleEquiv.symm.finrank_eq.trans hmodule

/-- Characteristic-away bridge for Maschke in the BG Thm 2.6 q≠p branch.

If `K` is a finite q-group and the field has characteristic `p ≠ q`, then
`|K|` is nonzero in the field.  This is the exact typeclass premise needed by
mathlib's Maschke theorem. -/
private theorem neZero_nat_card_cast_of_isPGroup_ne_char
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p]
    {K : Type*} [Group K] [Finite K]
    (hK : IsPGroup q K) (hq_ne_p : q ≠ p) :
    NeZero (Nat.card K : F) := by
  refine ⟨?_⟩
  intro hzero
  have hp_dvd_card : p ∣ Nat.card K :=
    (CharP.cast_eq_zero_iff F p (Nat.card K)).mp hzero
  rcases (IsPGroup.iff_card (p := q) (G := K)).mp hK with ⟨n, hcard⟩
  rw [hcard] at hp_dvd_card
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hp_dvd_q : p ∣ q := hp_prime.dvd_of_dvd_pow hp_dvd_card
  exact hq_ne_p ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hp_dvd_q).symm

/-- Maschke cardinality bridge from a theorem-level characteristic-away
hypothesis.

If no prime divisor of `|K|` is the characteristic of `F`, then `|K|` is
nonzero in `F`.  This is the exact bridge from BG Thm 2.6(a)'s hypothesis to
Maschke's typeclass premise. -/
private theorem neZero_nat_card_cast_of_forall_prime_not_char
    {F : Type*} [Field F] {K : Type*} [Group K] [Finite K]
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → ¬ CharP F q) :
    NeZero (Nat.card K : F) := by
  rcases CharP.exists' F with hzero | hpos
  · haveI : CharZero F := hzero
    refine ⟨?_⟩
    intro hcast
    exact (Nat.card_pos (α := K)).ne' (Nat.cast_eq_zero.mp hcast)
  · rcases hpos with ⟨p, hp_prime, hp_char⟩
    haveI : CharP F p := hp_char
    refine NeZero.of_not_dvd (R := F) (p := p) (n := Nat.card K) ?_
    intro hp_dvd
    exact (hchar p hp_prime.out hp_dvd) hp_char

/-- Subgroup form of `neZero_nat_card_cast_of_forall_prime_not_char`.

The theorem-level hypothesis in BG Thm 2.6(a) is stated for `G`; Maschke is
applied to normal q-subgroups `K ≤ G`. -/
theorem neZero_nat_card_cast_of_subgroup_forall_prime_not_char
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q)
    (K : Subgroup G) :
    NeZero (Nat.card K : F) := by
  exact neZero_nat_card_cast_of_forall_prime_not_char
    (F := F) (K := K)
    (fun q hq_prime hq_dvd =>
      hchar q hq_prime (hq_dvd.trans (Subgroup.card_subgroup_dvd_card K)))

/-- Maschke simple-constituent extraction from the exact cardinality premise.

This is the Maschke core needed in BG Thm 2.6: if `|K|` is nonzero in the
field, then the group-algebra module attached to a nonzero representation has
a simple submodule.  Characteristic-specific lemmas below only have to supply
this `NeZero` instance. -/
private theorem exists_simple_submodule_of_neZero_card
    {F : Type*} [Field F]
    {K : Type*} [Group K] [Finite K]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    [NeZero (Nat.card K : F)]
    (σ : Representation F K V) :
    ∃ N : Submodule (MonoidAlgebra F K) σ.asModule,
      IsSimpleModule (MonoidAlgebra F K) N := by
  letI : AddCommGroup σ.asModule := Representation.instAddCommGroupAsModule σ
  letI : Module F σ.asModule := Representation.instModuleAsModule σ
  letI : Module (MonoidAlgebra F K) σ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule σ
  letI : IsScalarTower F (MonoidAlgebra F K) σ.asModule := inferInstance
  have hnontriv : Nontrivial σ.asModule := by
    change Nontrivial V
    infer_instance
  have hsemi :
      @IsSemisimpleModule (MonoidAlgebra F K) inferInstance σ.asModule
        (Representation.instAddCommGroupAsModule σ)
        (Representation.instModuleMonoidAlgebraAsModule σ) := by
    infer_instance
  exact @IsSemisimpleModule.exists_simple_submodule
      (MonoidAlgebra F K) inferInstance σ.asModule
      (Representation.instAddCommGroupAsModule σ)
      (Representation.instModuleMonoidAlgebraAsModule σ) hsemi hnontriv

/-- Maschke simple-constituent extraction for the BG Thm 2.6 q≠p branch.

For a finite q-group acting on a nonzero vector space over a field of
characteristic `p ≠ q`, the corresponding group-algebra module has a simple
submodule.  This packages the q-group/characteristic-away check with mathlib's
Maschke theorem and the `Representation.asModule` bridge. -/
private theorem exists_simple_submodule_of_isPGroup_ne_char
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p]
    {K : Type*} [Group K] [Finite K]
    (hKq : IsPGroup q K) (hq_ne_p : q ≠ p)
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    (σ : Representation F K V) :
    ∃ N : Submodule (MonoidAlgebra F K) σ.asModule,
      IsSimpleModule (MonoidAlgebra F K) N := by
  haveI : NeZero (Nat.card K : F) :=
    neZero_nat_card_cast_of_isPGroup_ne_char (F := F) (K := K) hKq hq_ne_p
  exact exists_simple_submodule_of_neZero_card (K := K) σ

open scoped IsMulCommutative in
/-- Scalar-instance bridge for a simple group-algebra submodule of an abelian group.

The simple object naturally lives as a `MonoidAlgebra F K`-submodule of
`σ.asModule`, whereas the BG line argument needs its underlying
`F`-subrepresentation.  This lemma performs that transport and applies the
commutative Schur finrank-one result at the group-algebra level. -/
private theorem finrank_eq_one_of_simple_submodule_of_commutative_group
    {F : Type*} [Field F] [IsAlgClosed F] {K : Type*} [Group K]
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (σ : Representation F K V)
    (N : Submodule (MonoidAlgebra F K) σ.asModule)
    (hNsimple : IsSimpleModule (MonoidAlgebra F K) N) :
    Module.finrank F (Subrepresentation.ofSubmodule' N).toSubmodule = 1 := by
  haveI : IsSimpleModule (MonoidAlgebra F K) N := hNsimple
  letI : Module F N :=
    @Submodule.module' F (MonoidAlgebra F K) σ.asModule
      inferInstance inferInstance
      (Representation.instModuleMonoidAlgebraAsModule σ)
      N inferInstance inferInstance (Representation.instModuleAsModule σ) inferInstance
  letI : IsScalarTower F (MonoidAlgebra F K) N :=
    @Submodule.isScalarTower F (MonoidAlgebra F K) σ.asModule
      inferInstance inferInstance (Representation.instModuleMonoidAlgebraAsModule σ)
      N inferInstance inferInstance inferInstance
  have hfiniteN : Module.Finite F N := by
    let NF : Submodule F σ.asModule :=
      @Submodule.restrictScalars F (MonoidAlgebra F K) σ.asModule
        inferInstance inferInstance inferInstance
        (Representation.instModuleAsModule σ)
        (Representation.instModuleMonoidAlgebraAsModule σ)
        inferInstance inferInstance N
    have hfiniteAs : Module.Finite F σ.asModule := .equiv σ.asModuleEquiv.symm
    have hfiniteTop : Module.Finite F (⊤ : Submodule F σ.asModule) :=
      @Module.Finite.top F σ.asModule inferInstance inferInstance
        (Representation.instModuleAsModule σ) hfiniteAs
    have hfiniteNF : Module.Finite F NF :=
      @Submodule.finiteDimensional_of_le F σ.asModule
        inferInstance inferInstance (Representation.instModuleAsModule σ)
        NF ⊤ hfiniteTop le_top
    exact hfiniteNF.equiv
      ((Submodule.restrictScalarsEquiv F (MonoidAlgebra F K) σ.asModule N).restrictScalars F)
  haveI : IsMulCommutative K := ⟨hKcomm⟩
  haveI : IsMulCommutative (MonoidAlgebra F K) := inferInstance
  have hNdim : Module.finrank F N = 1 :=
    @IsSimpleModule.finrank_eq_one_of_isMulCommutative
      (MonoidAlgebra F K) N F
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance hfiniteN inferInstance inferInstance
  let W : Subrepresentation σ := Subrepresentation.ofSubmodule' N
  change Module.finrank F W.toSubmodule = 1
  let eW : W.toSubmodule ≃ₗ[F] N :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [eW.finrank_eq]
  exact hNdim

/-- A simple group-algebra submodule for an abelian group gives a rank-one
subrepresentation over an algebraically closed field.

This is the scalar-instance bridge after Maschke in the BG Thm 2.6 q≠p branch:
mathlib's commutative Schur result applies to the group-algebra submodule, then
`Subrepresentation.ofSubmodule'` transports it back to the representation. -/
private theorem exists_rank_one_subrepresentation_of_simple_submodule_of_commutative_group
    {F : Type*} [Field F] [IsAlgClosed F] {K : Type*} [Group K]
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (σ : Representation F K V)
    (N : Submodule (MonoidAlgebra F K) σ.asModule)
    (hNsimple : IsSimpleModule (MonoidAlgebra F K) N) :
    ∃ W : Subrepresentation σ, W ≠ ⊥ ∧ Module.finrank F W.toSubmodule = 1 := by
  let W : Subrepresentation σ := Subrepresentation.ofSubmodule' N
  haveI : IsSimpleModule (MonoidAlgebra F K) N := hNsimple
  have hWdim :
      Module.finrank F W.toSubmodule = 1 :=
    finrank_eq_one_of_simple_submodule_of_commutative_group hKcomm σ N hNsimple
  refine ⟨W, ?_, ?_⟩
  · have hN_nontrivial : Nontrivial N :=
      IsSimpleModule.nontrivial (MonoidAlgebra F K) N
    have hW_nontrivial : Nontrivial W.toSubmodule := by
      change Nontrivial N
      exact hN_nontrivial
    have hW_ne_bot : W.toSubmodule ≠ ⊥ :=
      W.toSubmodule.nontrivial_iff_ne_bot.mp hW_nontrivial
    intro hW_bot
    exact hW_ne_bot (congrArg Subrepresentation.toSubmodule hW_bot)
  · exact hWdim

/-- Maschke + algebraic-closedness line extraction for the BG Thm 2.6 q≠p branch.

For an abelian finite q-group acting on a nonzero finite-dimensional vector
space over an algebraically closed field of characteristic `p ≠ q`, there is a
nonzero one-dimensional subrepresentation. -/
private theorem exists_rank_one_subrepresentation_of_commutative_isPGroup_ne_char
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {K : Type*} [Group K] [Finite K]
    (hKq : IsPGroup q K) (hq_ne_p : q ≠ p)
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    (σ : Representation F K V) :
    ∃ W : Subrepresentation σ, W ≠ ⊥ ∧ Module.finrank F W.toSubmodule = 1 := by
  rcases exists_simple_submodule_of_isPGroup_ne_char hKq hq_ne_p σ with
    ⟨N, hNsimple⟩
  exact exists_rank_one_subrepresentation_of_simple_submodule_of_commutative_group
    hKcomm σ N hNsimple

/-- Maschke complement extraction from the exact cardinality premise.

For a two-dimensional representation of an abelian finite group whose order is
nonzero in the field, Maschke gives an invariant complement to a simple
rank-one constituent.  This is the characteristic-free core behind both the
q≠p branch and the characteristic-away branch of BG Thm 2.6(a). -/
private theorem exists_rank_one_complement_subrepresentations_of_commutative_of_neZero_card
    {F : Type*} [Field F] [IsAlgClosed F]
    {K : Type*} [Group K] [Finite K]
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    [NeZero (Nat.card K : F)]
    (σ : Representation F K V) (hdim : Module.finrank F V = 2) :
    ∃ W U : Subrepresentation σ,
      W ≠ ⊥ ∧ IsCompl W.toSubmodule U.toSubmodule ∧
        Module.finrank F W.toSubmodule = 1 ∧
        Module.finrank F (V ⧸ W.toSubmodule) = 1 := by
  letI : AddCommGroup σ.asModule := Representation.instAddCommGroupAsModule σ
  letI : Module F σ.asModule := Representation.instModuleAsModule σ
  letI : Module (MonoidAlgebra F K) σ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule σ
  letI : IsScalarTower F (MonoidAlgebra F K) σ.asModule := inferInstance
  rcases exists_simple_submodule_of_neZero_card (K := K) σ with
    ⟨N, hNsimple⟩
  rcases (@MonoidAlgebra.Submodule.exists_isCompl F inferInstance K inferInstance
      inferInstance inferInstance σ.asModule (Representation.instAddCommGroupAsModule σ)
      (Representation.instModuleMonoidAlgebraAsModule σ) N) with
    ⟨Q, hNQ⟩
  let W : Subrepresentation σ := Subrepresentation.ofSubmodule' N
  let U : Subrepresentation σ := Subrepresentation.ofSubmodule' Q
  have hWdim :
      Module.finrank F W.toSubmodule = 1 :=
    finrank_eq_one_of_simple_submodule_of_commutative_group hKcomm σ N hNsimple
  have hsubrep_compl : IsCompl W U :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)).symm.isCompl hNQ
  have hcompl : IsCompl W.toSubmodule U.toSubmodule := by
    refine IsCompl.of_eq ?_ ?_
    · have h := congrArg Subrepresentation.toSubmodule hsubrep_compl.inf_eq_bot
      rw [Subrepresentation.toSubmodule_inf] at h
      exact h
    · have h := congrArg Subrepresentation.toSubmodule hsubrep_compl.sup_eq_top
      rw [Subrepresentation.toSubmodule_sup] at h
      exact h
  haveI : IsSimpleModule (MonoidAlgebra F K) N := hNsimple
  have hW_ne_bot_sub : W.toSubmodule ≠ ⊥ := by
    have hN_nontrivial : Nontrivial N :=
      IsSimpleModule.nontrivial (MonoidAlgebra F K) N
    have hW_nontrivial : Nontrivial W.toSubmodule := by
      change Nontrivial N
      exact hN_nontrivial
    exact W.toSubmodule.nontrivial_iff_ne_bot.mp hW_nontrivial
  have hW_ne_bot : W ≠ ⊥ := by
    intro hW_bot
    exact hW_ne_bot_sub (congrArg Subrepresentation.toSubmodule hW_bot)
  have hW_ne_top_sub : W.toSubmodule ≠ ⊤ := by
    intro hW_top
    have h12 : (1 : ℕ) = 2 := by
      calc
        1 = Module.finrank F W.toSubmodule := hWdim.symm
        _ = Module.finrank F (⊤ : Submodule F V) := by rw [hW_top]
        _ = Module.finrank F V := finrank_top F V
        _ = 2 := hdim
    omega
  have hQdim :
      Module.finrank F (V ⧸ W.toSubmodule) = 1 :=
    (rank_one_subquotients_of_finrank_two W.toSubmodule hdim hW_ne_bot_sub
      hW_ne_top_sub).2
  exact ⟨W, U, hW_ne_bot, hcompl, hWdim, hQdim⟩

/-- Maschke complement extraction for the BG Thm 2.6 q≠p branch.

For a two-dimensional representation of an abelian finite q-group in
characteristic `p ≠ q`, Maschke gives an invariant complement to a simple
rank-one constituent.  This is the `K`-module form of the textbook line
`V = W₁ ⊕ W₂`; the remaining ambient step is proving that normality of `K`
makes `G` permute these two lines. -/
private theorem exists_rank_one_complement_subrepresentations_of_commutative_isPGroup_ne_char
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {K : Type*} [Group K] [Finite K]
    (hKq : IsPGroup q K) (hq_ne_p : q ≠ p)
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    (σ : Representation F K V) (hdim : Module.finrank F V = 2) :
    ∃ W U : Subrepresentation σ,
      W ≠ ⊥ ∧ IsCompl W.toSubmodule U.toSubmodule ∧
        Module.finrank F W.toSubmodule = 1 ∧
        Module.finrank F (V ⧸ W.toSubmodule) = 1 := by
  haveI : NeZero (Nat.card K : F) :=
    neZero_nat_card_cast_of_isPGroup_ne_char (F := F) (K := K) hKq hq_ne_p
  exact
    exists_rank_one_complement_subrepresentations_of_commutative_of_neZero_card
      (K := K) hKcomm σ hdim

/-- Maschke complement extraction packaged in the theorem-facing data shape.

This is the cardinality-premise version of the rank-one data bridge.  It
keeps the linear-algebra input aligned with Maschke's actual hypothesis,
allowing theorem-level characteristic-away assumptions to supply `NeZero`
without manufacturing a separate characteristic prime. -/
theorem exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hdim : Module.finrank F V = 2)
    (K : Subgroup G) [NeZero (Nat.card K : F)]
    (hKcomm : Std.Commutative (· * · : K → K → K)) :
    ∃ W : Subrepresentation (ρ.comp K.subtype),
    ∃ U : Subrepresentation (ρ.comp K.subtype),
      Nonempty (Module.Free F W.toSubmodule) ∧
      Nonempty (Module.Free F U.toSubmodule) ∧
      Nonempty (Module.Finite F W.toSubmodule) ∧
      Nonempty (Module.Finite F U.toSubmodule) ∧
      Nonempty (Module.Free F (V ⧸ W.toSubmodule)) ∧
      Nonempty (Module.Free F (V ⧸ U.toSubmodule)) ∧
      IsCompl W.toSubmodule U.toSubmodule ∧
      Module.finrank F W.toSubmodule = 1 ∧
      Module.finrank F U.toSubmodule = 1 ∧
      Module.finrank F (V ⧸ W.toSubmodule) = 1 ∧
      Module.finrank F (V ⧸ U.toSubmodule) = 1 := by
  have hVpos : 0 < Module.finrank F V := by
    rw [hdim]
    norm_num
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) hVpos
  rcases exists_rank_one_complement_subrepresentations_of_commutative_of_neZero_card
      (F := F) (K := K) hKcomm (ρ.comp K.subtype) hdim with
    ⟨W, U, _hW_ne_bot, hcompl, hdimW, hdimQW⟩
  rcases complement_rank_one_right_subquotients_of_finrank_two
      W.toSubmodule U.toSubmodule hdim hcompl hdimW with
    ⟨hdimU, hdimQU⟩
  exact ⟨W, U, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
    ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, hcompl, hdimW,
    hdimU, hdimQW, hdimQU⟩

/-- q≠p Maschke complement extraction packaged in the theorem-facing data shape.

This strengthens `exists_rank_one_complement_subrepresentations_of_commutative_isPGroup_ne_char`
by also supplying the symmetric rank-one data for the complementary line and
the local `Free`/`Finite` evidence needed by the determinant-kernel uniqueness
bridges.  It is the exact input shape consumed by
`commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules`. -/
theorem exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hdim : Module.finrank F V = 2)
    (K : Subgroup G) (hKq : IsPGroup q K) (hq_ne_p : q ≠ p)
    (hKcomm : Std.Commutative (· * · : K → K → K)) :
    ∃ W : Subrepresentation (ρ.comp K.subtype),
    ∃ U : Subrepresentation (ρ.comp K.subtype),
      Nonempty (Module.Free F W.toSubmodule) ∧
      Nonempty (Module.Free F U.toSubmodule) ∧
      Nonempty (Module.Finite F W.toSubmodule) ∧
      Nonempty (Module.Finite F U.toSubmodule) ∧
      Nonempty (Module.Free F (V ⧸ W.toSubmodule)) ∧
      Nonempty (Module.Free F (V ⧸ U.toSubmodule)) ∧
      IsCompl W.toSubmodule U.toSubmodule ∧
      Module.finrank F W.toSubmodule = 1 ∧
      Module.finrank F U.toSubmodule = 1 ∧
      Module.finrank F (V ⧸ W.toSubmodule) = 1 ∧
      Module.finrank F (V ⧸ U.toSubmodule) = 1 := by
  haveI : NeZero (Nat.card K : F) :=
    neZero_nat_card_cast_of_isPGroup_ne_char (F := F) (K := K) hKq hq_ne_p
  exact exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
    ρ hdim K hKcomm

/-- Conjugating a `K`-subrepresentation by an ambient element of `G`.

This is the normality bridge in the q≠p branch of BG Thm 2.6: if `K ⊴ G`,
then the image of a `K`-stable line under any `g : G` is again `K`-stable.
The next step is to combine this with uniqueness of the two rank-one
`K`-submodules. -/
def conjugateSubrepresentationOfNormal
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W : Subrepresentation (ρ.comp K.subtype)) (g : G) :
    Subrepresentation (ρ.comp K.subtype) where
  toSubmodule := W.toSubmodule.map (ρ g)
  apply_mem_toSubmodule k {v} hv := by
    rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
    let kg : K := ⟨g⁻¹ * (k : G) * g, hKnormal.conj_mem' (k : G) k.2 g⟩
    refine Submodule.mem_map.mpr ⟨ρ (kg : G) w, W.apply_mem_toSubmodule kg hw, ?_⟩
    have hmul : g * (kg : G) = (k : G) * g := by
      dsimp [kg]
      group
    calc
      ρ g (ρ (kg : G) w) = ρ (g * (kg : G)) w := by
        simp [← Module.End.mul_apply, ← map_mul]
      _ = ρ ((k : G) * g) w := by rw [hmul]
      _ = ρ (k : G) (ρ g w) := by
        simp [← Module.End.mul_apply, ← map_mul]

/-- Conjugating a subrepresentation by a group element preserves finrank. -/
private theorem finrank_conjugateSubrepresentationOfNormal
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W : Subrepresentation (ρ.comp K.subtype)) (g : G) :
    Module.finrank F (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule =
      Module.finrank F W.toSubmodule := by
  let e : V ≃ₗ[F] V := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  have hcoe : (e : V →ₗ[F] V) = ρ g := LinearMap.ext fun x => by simp [e]
  have h := LinearEquiv.finrank_map_eq e W.toSubmodule
  rw [hcoe] at h
  exact h

/-- Conjugating complementary `K`-subrepresentations by an ambient element
preserves complementarity. -/
theorem isCompl_conjugateSubrepresentationOfNormal
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W U : Subrepresentation (ρ.comp K.subtype)) (g : G)
    (hcompl : IsCompl W.toSubmodule U.toSubmodule) :
    IsCompl
      (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule
      (conjugateSubrepresentationOfNormal K hKnormal ρ U g).toSubmodule := by
  have hinj : Function.Injective (ρ g) := (ρ.apply_bijective g).1
  have hsurj : Function.Surjective (ρ g) := (ρ.apply_bijective g).2
  refine IsCompl.of_eq ?_ ?_
  · change W.toSubmodule.map (ρ g) ⊓ U.toSubmodule.map (ρ g) =
      (⊥ : Submodule F V)
    rw [← Submodule.map_inf (ρ g) hinj, hcompl.inf_eq_bot, Submodule.map_bot]
  · change W.toSubmodule.map (ρ g) ⊔ U.toSubmodule.map (ρ g) =
      (⊤ : Submodule F V)
    rw [← (Submodule.map_sup (p := W.toSubmodule) (p' := U.toSubmodule) (f := ρ g)),
      hcompl.sup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hsurj

/-- If the rank-one `K`-subrepresentations are exhausted by a pair `W, U`,
then every conjugate of `W` is one of that pair. -/
theorem conjugateSubrepresentation_eq_left_or_right_of_rank_one_unique
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V)
    (W U : Subrepresentation (ρ.comp K.subtype))
    (hWdim : Module.finrank F W.toSubmodule = 1)
    (hunique : ∀ L : Subrepresentation (ρ.comp K.subtype),
      Module.finrank F L.toSubmodule = 1 → L = W ∨ L = U)
    (g : G) :
    conjugateSubrepresentationOfNormal K hKnormal ρ W g = W ∨
      conjugateSubrepresentationOfNormal K hKnormal ρ W g = U := by
  apply hunique
  exact (finrank_conjugateSubrepresentationOfNormal K hKnormal ρ W g).trans hWdim

/-- Equality of a conjugate line with a target line gives the `comap` form used
by `RankOneLinePairData.permutes`. -/
theorem le_comap_of_conjugateSubrepresentation_eq
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W T : Subrepresentation (ρ.comp K.subtype)) {g : G}
    (hconj : conjugateSubrepresentationOfNormal K hKnormal ρ W g = T) :
    W.toSubmodule ≤ T.toSubmodule.comap (ρ g) := by
  intro w hw
  have hmem :
      ρ g w ∈ (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule :=
    Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have hsub :=
    congrArg Subrepresentation.toSubmodule hconj
  simpa [hsub] using hmem

/-- In characteristic `p`, a p-group acts trivially on every one-dimensional representation. -/
private theorem isPGroup_rank_one_representation_trivial_of_charP
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] (hG : IsPGroup p G)
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) :
    ∀ g : G, ∀ m : M, ρ g m = m := by
  let φ := scalarCharacterOfFinrankEqOne hdim ρ
  have hφ : φ = 1 := monoidHom_units_eq_one_of_isPGroup_charP hG φ
  intro g m
  calc
    ρ g m = (φ g : F) • m := scalarCharacterOfFinrankEqOne_apply_smul hdim ρ g m
    _ = m := by simp [hφ]

/-- Submodule form of `isPGroup_rank_one_representation_trivial_of_charP`. -/
theorem isPGroup_rank_one_submodule_action_trivial_of_charP
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) [Module.Free F W] (hdimW : Module.finrank F W = 1)
    (ρ : Representation F G V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∀ g : G, ∀ w ∈ W, ρ g w = w := by
  have htriv := isPGroup_rank_one_representation_trivial_of_charP hG hdimW
    (ρ.subrepresentation W hW)
  intro g w hw
  have hsub := htriv g ⟨w, hw⟩
  exact congrArg Subtype.val hsub

/-- Quotient form of `isPGroup_rank_one_representation_trivial_of_charP`. -/
theorem isPGroup_rank_one_quotient_action_trivial_of_charP
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) [Module.Free F (V ⧸ W)]
    (hdimQ : Module.finrank F (V ⧸ W) = 1)
    (ρ : Representation F G V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∀ g : G, ∀ v : V, ρ g v - v ∈ W := by
  have htriv := isPGroup_rank_one_representation_trivial_of_charP hG hdimQ
    (ρ.quotient W hW)
  intro g v
  have hq := htriv g (Submodule.Quotient.mk v : V ⧸ W)
  change Submodule.Quotient.mk (ρ g v) = Submodule.Quotient.mk v at hq
  simpa [Submodule.Quotient.eq] using hq

/-- If two endomorphisms are trivial on a submodule and on the quotient by it,
then they commute.

This is the linear-algebra core of BG Thm 2.6, q = p: the subgroup
`C_G(W) ∩ C_G(V/W)` acts by maps `1 + n` where `n` kills `W` and has image in
`W`; products of two such nilpotent parts vanish. -/
private theorem end_commute_of_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (f g : Module.End F V)
    (hfW : ∀ w ∈ W, f w = w) (hfQ : ∀ v, f v - v ∈ W)
    (hgW : ∀ w ∈ W, g w = w) (hgQ : ∀ v, g v - v ∈ W) :
    f * g = g * f := by
  ext v
  calc
    (f * g) v = f (g v) := rfl
    _ = f (v + (g v - v)) := by congr 1; abel
    _ = f v + (g v - v) := by rw [map_add, hfW (g v - v) (hgQ v)]
    _ = g v + (f v - v) := by abel
    _ = g (v + (f v - v)) := by rw [map_add, hgW (f v - v) (hfQ v)]
    _ = g (f v) := by congr 1; abel
    _ = (g * f) v := rfl

/-- Submonoid-level wrapper for
`end_commute_of_fixed_on_submodule_and_quotient`. -/
private theorem submonoid_commutative_of_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (S : Submonoid (Module.End F V))
    (hS : ∀ f ∈ S, (∀ w ∈ W, f w = w) ∧ (∀ v, f v - v ∈ W)) :
    Std.Commutative (· * · : S → S → S) := by
  constructor
  intro f g
  apply Subtype.ext
  exact end_commute_of_fixed_on_submodule_and_quotient W (f : Module.End F V)
    (g : Module.End F V) (hS f f.2).1 (hS f f.2).2 (hS g g.2).1 (hS g g.2).2

/-- Representation-range wrapper for
`submonoid_commutative_of_fixed_on_submodule_and_quotient`.

For monoid homs into `Module.End`, mathlib's range object is
`MonoidHom.mrange` (a `Submonoid`). -/
private theorem representation_mrange_commutative_of_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hρ : ∀ g : G, (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W)) :
    Std.Commutative
      (· * · : MonoidHom.mrange ρ → MonoidHom.mrange ρ → MonoidHom.mrange ρ) := by
  apply submonoid_commutative_of_fixed_on_submodule_and_quotient W (MonoidHom.mrange ρ)
  intro f hf
  obtain ⟨g, rfl⟩ := MonoidHom.mem_mrange.mp hf
  exact hρ g

/-- A faithful representation reflects commutativity from its endomorphism image. -/
private theorem commutative_of_injective_representation_mrange_commutative
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hrange : Std.Commutative
      (· * · : MonoidHom.mrange ρ → MonoidHom.mrange ρ → MonoidHom.mrange ρ)) :
    Std.Commutative (· * · : G → G → G) := by
  constructor
  intro x y
  apply hfaithful
  have hcomm := hrange.comm
    (⟨ρ x, MonoidHom.mem_mrange.mpr ⟨x, rfl⟩⟩ : MonoidHom.mrange ρ)
    (⟨ρ y, MonoidHom.mem_mrange.mpr ⟨y, rfl⟩⟩ : MonoidHom.mrange ρ)
  calc
    ρ (x * y) = ρ x * ρ y := map_mul ρ x y
    _ = ρ y * ρ x := congrArg Subtype.val hcomm
    _ = ρ (y * x) := (map_mul ρ y x).symm

/-- Faithful-representation form of the `C_G(W) ∩ C_G(V/W)` commutativity
calculation used in BG Thm 2.6, q = p. -/
private theorem commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hρ : ∀ g : G, (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W)) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_injective_representation_mrange_commutative ρ hfaithful
    (representation_mrange_commutative_of_fixed_on_submodule_and_quotient W ρ hρ)

/-- Subgroup-restriction form of
`commutative_of_faithful_representation_fixed_on_submodule_and_quotient`.

This is the shape needed for BG Thm 2.6, q = p, where
`H = C_G(W) ∩ C_G(V/W)`. -/
theorem subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hH : ∀ h : H, (∀ w ∈ W, ρ h w = w) ∧ (∀ v, ρ h v - v ∈ W)) :
    Std.Commutative (· * · : H → H → H) := by
  apply commutative_of_faithful_representation_fixed_on_submodule_and_quotient W
    (ρ.comp H.subtype)
  · intro x y hxy
    apply Subtype.ext
    exact hfaithful hxy
  · exact hH

/-- The subgroup acting trivially on `W` and on `V/W`.

This is the Lean version of the `C_G(W) ∩ C_G(V/W)` subgroup appearing in
BG Thm 2.6, q = p.  The quotient condition is written without choosing a
quotient representation: `ρ g v - v ∈ W` for every `v`. -/
def fixedOnSubmoduleAndQuotientSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V) : Subgroup G where
  carrier := {g | (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W)}
  one_mem' := by
    constructor
    · intro w _hw
      simp
    · intro v
      simp
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro w hw
      simpa [map_mul, hb.1 w hw] using ha.1 w hw
    · intro v
      have haW : ρ a (ρ b v) - ρ b v ∈ W := ha.2 (ρ b v)
      have hbW : ρ b v - v ∈ W := hb.2 v
      have hsum : (ρ a (ρ b v) - ρ b v) + (ρ b v - v) ∈ W := W.add_mem haW hbW
      have htarget :
          ρ (a * b) v - v = (ρ a (ρ b v) - ρ b v) + (ρ b v - v) := by
        rw [map_mul]
        change ρ a (ρ b v) - v = (ρ a (ρ b v) - ρ b v) + (ρ b v - v)
        abel
      rwa [htarget]
  inv_mem' := by
    intro a ha
    constructor
    · intro w hw
      have hdiff : w - ρ a⁻¹ w ∈ W := by
        simpa [map_mul] using ha.2 (ρ a⁻¹ w)
      have hinvW : ρ a⁻¹ w ∈ W := by
        have htmp : w - (w - ρ a⁻¹ w) ∈ W := W.sub_mem hw hdiff
        convert htmp using 1
        abel
      have hleft : ρ a (ρ a⁻¹ w) = w := by
        calc
          ρ a (ρ a⁻¹ w) = ((ρ a) * (ρ a⁻¹)) w := rfl
          _ = ρ (a * a⁻¹) w := by rw [map_mul]
          _ = w := by simp
      have hfix := ha.1 (ρ a⁻¹ w) hinvW
      rw [hleft] at hfix
      exact hfix.symm
    · intro v
      have hdiff : v - ρ a⁻¹ v ∈ W := by
        simpa [map_mul] using ha.2 (ρ a⁻¹ v)
      simpa [sub_eq_add_neg, add_comm] using W.neg_mem hdiff

end OddOrder.BG.Ch1.S02
