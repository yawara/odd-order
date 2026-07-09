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
private theorem smul_fin_two_eq_self_of_odd_card
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
private theorem monoidHom_units_apply_eq_one_of_isPGroup_charP
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
private theorem rank_one_subquotients_of_finrank_two
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
private theorem rank_one_invariant_submodule_eq_left_or_right_of_distinct_scalars
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
private noncomputable def scalarCharacterOfFinrankEqOne
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
private theorem scalarCharacterOfFinrankEqOne_apply_smul
    {F : Type*} [Field F] {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) (g : G) (m : M) :
    ρ g m = (scalarCharacterOfFinrankEqOne hdim ρ g : F) • m :=
  scalarMonoidHomOfFinrankEqOne_apply_smul hdim ρ g m

/-- A scalar endomorphism of a one-dimensional module has that scalar as determinant. -/
private theorem det_eq_scalar_of_finrank_eq_one
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
private theorem neZero_nat_card_cast_of_subgroup_forall_prime_not_char
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
private theorem exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
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
private theorem exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
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
private def conjugateSubrepresentationOfNormal
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
private theorem isCompl_conjugateSubrepresentationOfNormal
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
private theorem conjugateSubrepresentation_eq_left_or_right_of_rank_one_unique
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
private theorem le_comap_of_conjugateSubrepresentation_eq
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
private theorem isPGroup_rank_one_submodule_action_trivial_of_charP
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
private theorem isPGroup_rank_one_quotient_action_trivial_of_charP
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
private theorem subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient
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
private def fixedOnSubmoduleAndQuotientSubgroup
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

private theorem mem_fixedOnSubmoduleAndQuotientSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    {W : Submodule F V} {ρ : Representation F G V} {g : G} :
    g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ ↔
      (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W) :=
  Iff.rfl

/-- If `g` acts trivially on `W` and on `V/W`, then `ρ g - 1` squares to zero.

This is the unipotent calculation behind BG Thm 2.6(b), q = p. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_sub_pow_two_eq_zero
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V)
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    (((ρ g : Module.End F V) - 1) ^ 2 : Module.End F V) = 0 := by
  rw [pow_two]
  ext v
  rw [Module.End.mul_apply]
  change ρ g (ρ g v - v) - (ρ g v - v) = 0
  have hmem := (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).2 v
  have hfix := (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).1 (ρ g v - v) hmem
  rw [hfix, sub_self]

/-- In characteristic `p`, every element of `C_G(W) ∩ C_G(V/W)` acts with
p-th power identity under the representation. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_rep_pow_prime_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Nontrivial V]
    (W : Submodule F V) (ρ : Representation F G V)
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    (ρ g : Module.End F V) ^ p = 1 := by
  haveI : CharP (Module.End F V) p := IsPGroup.charP_End_of_field
  have hsq :
      (((ρ g : Module.End F V) - 1) ^ 2 : Module.End F V) = 0 :=
    fixedOnSubmoduleAndQuotientSubgroup_sub_pow_two_eq_zero W ρ hg
  have hpow_zero :
      (((ρ g : Module.End F V) - 1) ^ p : Module.End F V) = 0 :=
    pow_eq_zero_of_le (Nat.Prime.two_le (Fact.out : p.Prime)) hsq
  have hsub :
      (((ρ g : Module.End F V) - 1) ^ p : Module.End F V) =
        (ρ g : Module.End F V) ^ p - 1 := by
    rw [sub_pow_char_of_commute p (Commute.one_right (ρ g : Module.End F V)), one_pow]
  exact sub_eq_zero.mp (hsub ▸ hpow_zero)

/-- Faithfulness turns the previous representation-level p-torsion into
group-level p-torsion. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_pow_prime_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Nontrivial V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    g ^ p = 1 := by
  apply hfaithful
  simpa [map_pow] using
    (fixedOnSubmoduleAndQuotientSubgroup_rep_pow_prime_eq_one
      (p := p) W ρ hg)

/-- In a faithful representation over characteristic `p`, the subgroup acting
trivially on a submodule and on the quotient is a p-subgroup. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_isPGroup_of_faithful
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Nontrivial V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) :
    IsPGroup p (fixedOnSubmoduleAndQuotientSubgroup W ρ) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using
    (fixedOnSubmoduleAndQuotientSubgroup_pow_prime_eq_one
      (p := p) W ρ hfaithful g.property)

/-- The `C_G(W) ∩ C_G(V/W)` subgroup is abelian for a faithful representation. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_commutative
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) :
    Std.Commutative
      (· * · : fixedOnSubmoduleAndQuotientSubgroup W ρ →
        fixedOnSubmoduleAndQuotientSubgroup W ρ →
        fixedOnSubmoduleAndQuotientSubgroup W ρ) :=
  subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    (fixedOnSubmoduleAndQuotientSubgroup W ρ) W ρ hfaithful
    (fun h => h.property)

/-- If a p-subgroup acts by scalar characters on `W` and `V/W`, then in
characteristic `p` it lies in `C_G(W) ∩ C_G(V/W)`.

The scalar characters are passed as hypotheses rather than constructed here;
BG obtains them from the fact that `W` and `V/W` are one-dimensional. -/
private theorem subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_isPGroup_scalar_actions
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) (ρ : Representation F G V)
    (hH : IsPGroup p H) (φW φQ : H →* Fˣ)
    (hW : ∀ h : H, ∀ w ∈ W, ρ h w = (φW h : F) • w)
    (hQ : ∀ h : H, ∀ v, ρ h v - (φQ h : F) • v ∈ W) :
    H ≤ fixedOnSubmoduleAndQuotientSubgroup W ρ := by
  intro g hg
  rw [mem_fixedOnSubmoduleAndQuotientSubgroup]
  let h : H := ⟨g, hg⟩
  constructor
  · intro w hw
    have hφW : φW h = 1 :=
      monoidHom_units_apply_eq_one_of_isPGroup_charP hH φW h
    calc
      ρ g w = (φW h : F) • w := hW h w hw
      _ = w := by simp [hφW]
  · intro v
    have hφQ : φQ h = 1 :=
      monoidHom_units_apply_eq_one_of_isPGroup_charP hH φQ h
    simpa [hφQ] using hQ h v

/-- Commutativity version of
`subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_isPGroup_scalar_actions`
for faithful representations. -/
private theorem subgroup_commutative_of_isPGroup_scalar_actions
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hH : IsPGroup p H) (φW φQ : H →* Fˣ)
    (hW : ∀ h : H, ∀ w ∈ W, ρ h w = (φW h : F) • w)
    (hQ : ∀ h : H, ∀ v, ρ h v - (φQ h : F) • v ∈ W) :
    Std.Commutative (· * · : H → H → H) := by
  apply subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    H W ρ hfaithful
  intro h
  have hle := subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_isPGroup_scalar_actions
    H W ρ hH φW φQ hW hQ h.property
  exact (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hle)

/-- If a p-subgroup acts on a rank-one invariant submodule and rank-one quotient,
then it lies in `C_G(W) ∩ C_G(V/W)`. -/
private theorem subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hH : IsPGroup p H)
    (hW : ∀ h : H, W ≤ W.comap (ρ h))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    H ≤ fixedOnSubmoduleAndQuotientSubgroup W ρ := by
  intro g hg
  rw [mem_fixedOnSubmoduleAndQuotientSubgroup]
  let h : H := ⟨g, hg⟩
  constructor
  · exact isPGroup_rank_one_submodule_action_trivial_of_charP hH W hdimW (ρ.comp H.subtype)
      hW h
  · exact isPGroup_rank_one_quotient_action_trivial_of_charP hH W hdimQ
      (ρ.comp H.subtype) hW h

/-- Commutativity consequence of
`subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients`. -/
private theorem subgroup_commutative_of_rank_one_subquotients
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ) (hH : IsPGroup p H)
    (hW : ∀ h : H, W ≤ W.comap (ρ h))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    Std.Commutative (· * · : H → H → H) := by
  apply subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    H W ρ hfaithful
  intro h
  exact mem_fixedOnSubmoduleAndQuotientSubgroup.mp
    (subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
      H W ρ hH hW hdimW hdimQ h.property)

/-- A scalar character into a field's unit group kills the commutator subgroup. -/
private theorem commutator_le_ker_of_units_character
    {F : Type*} [Field F] {G : Type*} [Group G] (φ : G →* Fˣ) :
    commutator G ≤ φ.ker := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro x _hx y _hy
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (φ x) (φ y))

/-- A representation as a group homomorphism into `GL(V)`.

This is the determinant-facing form of a `Representation`; the inverse of
`ρ g` is supplied by `ρ g⁻¹`. -/
private def representationToGeneralLinearGroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : G →* LinearMap.GeneralLinearGroup F V where
  toFun g :=
    { val := ρ g
      inv := ρ g⁻¹
      val_inv := by
        rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by
        rw [← map_mul, inv_mul_cancel, map_one] }
  map_one' := by
    apply Units.ext
    ext v
    simp
  map_mul' g h := by
    apply Units.ext
    ext v
    simp [map_mul]

/-- The determinant character attached to a representation.  BG writes its
kernel as `G* = G ∩ SL(V, F)`. -/
private noncomputable def determinantCharacterOfRepresentation
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : G →* Fˣ :=
  (LinearEquiv.det : (V ≃ₗ[F] V) →* Fˣ).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp
      (representationToGeneralLinearGroup ρ))

/-- Determinant-kernel subgroup `G*` from BG Thm 2.6. -/
private noncomputable def determinantKernelSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : Subgroup G :=
  (determinantCharacterOfRepresentation ρ).ker

private theorem mem_determinantKernelSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    {ρ : Representation F G V} {g : G} :
    g ∈ determinantKernelSubgroup ρ ↔
      determinantCharacterOfRepresentation ρ g = 1 :=
  Iff.rfl

private theorem determinantKernelSubgroup_normal
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    (determinantKernelSubgroup ρ).Normal := by
  dsimp [determinantKernelSubgroup]
  infer_instance

/-- On an invariant rank-one submodule and rank-one quotient, the determinant
character is the product of the two scalar characters. -/
private theorem determinantCharacter_eq_scalarCharacter_mul_quotient
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    (g : G) :
    determinantCharacterOfRepresentation ρ g =
      scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g *
        scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g := by
  ext
  have hdet :
      LinearMap.det (ρ g) =
        LinearMap.det ((ρ g).restrict (hW g)) *
          LinearMap.det (W.mapQ W (ρ g) (hW g)) :=
    LinearMap.det_eq_det_mul_det W (ρ g) (hW g)
  have hdetW :
      LinearMap.det ((ρ g).restrict (hW g)) =
        (scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g : F) := by
    apply det_eq_scalar_of_finrank_eq_one hdimW
    intro w
    simpa [Representation.subrepresentation] using
      scalarCharacterOfFinrankEqOne_apply_smul hdimW
        (ρ.subrepresentation W hW) g w
  have hdetQ :
      LinearMap.det (W.mapQ W (ρ g) (hW g)) =
        (scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g : F) := by
    apply det_eq_scalar_of_finrank_eq_one hdimQ
    intro v
    simpa [Representation.quotient] using
      scalarCharacterOfFinrankEqOne_apply_smul hdimQ (ρ.quotient W hW) g v
  calc
    (determinantCharacterOfRepresentation ρ g : F) = LinearMap.det (ρ g) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    _ = LinearMap.det ((ρ g).restrict (hW g)) *
        LinearMap.det (W.mapQ W (ρ g) (hW g)) := hdet
    _ = (scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g : F) *
        (scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g : F) := by
      rw [hdetW, hdetQ]

/-- Membership in the determinant kernel forces the two rank-one scalar
characters to have product one. -/
private theorem scalarCharacters_mul_eq_one_of_mem_determinantKernel
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    {g : G} (hg : g ∈ determinantKernelSubgroup ρ) :
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g *
        scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g = 1 := by
  have hdet :=
    determinantCharacter_eq_scalarCharacter_mul_quotient W ρ hW hdimW hdimQ g
  have hgdet : determinantCharacterOfRepresentation ρ g = 1 :=
    mem_determinantKernelSubgroup.mp hg
  simpa [hdet] using hgdet

/-- On a preserved complement, the scalar character of the quotient `V/W`
is the same as the scalar character on the complementary line.

This is the bridge needed in BG Thm 2.6 q ≠ p to replace the determinant
formula's quotient scalar by the actual scalar on the second Maschke line. -/
private theorem scalarCharacter_quotient_eq_complement_of_isCompl
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Free F U] [Module.Finite F U]
    [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V)
    (hcompl : IsCompl W U)
    (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimU : Module.finrank F U = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    (g : G) :
    scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g =
      scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU) g := by
  let φQ : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW)
  let φU : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU)
  have hU_ne_bot : U ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  rcases Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hU_ne_bot) with
    ⟨u, hu_ne_zero⟩
  have hmk_ne_zero :
      (Submodule.Quotient.mk (u : V) : V ⧸ W) ≠ 0 := by
    intro hmk
    have huW : (u : V) ∈ W := by
      simpa [Submodule.Quotient.mk_eq_zero] using hmk
    have huInf : (u : V) ∈ W ⊓ U := ⟨huW, u.2⟩
    have huBot : (u : V) ∈ (⊥ : Submodule F V) := by
      simpa [hcompl.inf_eq_bot] using huInf
    exact hu_ne_zero (Subtype.ext (by simpa using huBot))
  have hquot :=
    scalarCharacterOfFinrankEqOne_apply_smul hdimQ (ρ.quotient W hW) g
      (Submodule.Quotient.mk (u : V) : V ⧸ W)
  change
      (Submodule.Quotient.mk (ρ g (u : V)) : V ⧸ W) =
        (φQ g : F) • (Submodule.Quotient.mk (u : V) : V ⧸ W) at hquot
  have hsub :=
    scalarCharacterOfFinrankEqOne_apply_smul hdimU (ρ.subrepresentation U hU) g u
  have hsubV : ρ g (u : V) = (φU g : F) • (u : V) :=
    congrArg Subtype.val hsub
  have hscalar :
      (φU g : F) • (Submodule.Quotient.mk (u : V) : V ⧸ W) =
        (φQ g : F) • (Submodule.Quotient.mk (u : V) : V ⧸ W) := by
    simpa [hsubV] using hquot
  ext
  have hdiff :
      ((φU g : F) - (φQ g : F)) •
          (Submodule.Quotient.mk (u : V) : V ⧸ W) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hscalar
  have hcoeff : (φU g : F) - (φQ g : F) = 0 := by
    exact (smul_eq_zero.mp hdiff).resolve_right hmk_ne_zero
  exact (sub_eq_zero.mp hcoeff).symm

/-- Determinant-kernel elements have inverse scalar characters on two preserved
complementary rank-one lines. -/
private theorem scalarCharacters_complement_mul_eq_one_of_mem_determinantKernel
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Free F U] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V)
    (hcompl : IsCompl W U)
    (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimW : Module.finrank F W = 1)
    (hdimU : Module.finrank F U = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    {g : G} (hg : g ∈ determinantKernelSubgroup ρ) :
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g *
        scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU) g = 1 := by
  have hprod :=
    scalarCharacters_mul_eq_one_of_mem_determinantKernel W ρ hW hdimW hdimQ hg
  have hquot_eq :=
    scalarCharacter_quotient_eq_complement_of_isCompl W U ρ hcompl hW hU
      hdimU hdimQ g
  simpa [hquot_eq] using hprod

/-- A nontrivial odd-order determinant-kernel element has distinct scalars on
two preserved complementary rank-one lines.

This is the BG Thm 2.6 q ≠ p eigenvalue step: if the two scalars were equal,
their determinant product would make the common scalar square to one; odd order
then forces both scalars to be one, and faithfulness makes the element trivial. -/
private theorem scalarCharacters_ne_of_mem_determinantKernel_of_ne_one
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Free F U]
    [Module.Finite F U] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hcompl : IsCompl W U)
    (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimW : Module.finrank F W = 1)
    (hdimU : Module.finrank F U = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    {g : G} (hgdet : g ∈ determinantKernelSubgroup ρ)
    (hoddg : Odd (orderOf g)) (hg_ne_one : g ≠ 1) :
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g ≠
      scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU) g := by
  let φW : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW)
  let φU : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU)
  intro hsame
  have hprod :
      φW g * φU g = 1 :=
    scalarCharacters_complement_mul_eq_one_of_mem_determinantKernel
      W U ρ hcompl hW hU hdimW hdimU hdimQ hgdet
  have hsq : (φW g) ^ 2 = 1 := by
    simpa [φW, φU, pow_two, hsame] using hprod
  have hpow_order : (φW g) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have horder_dvd_two : orderOf (φW g) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hsq
  have horder_dvd_g : orderOf (φW g) ∣ orderOf g :=
    orderOf_dvd_of_pow_eq_one hpow_order
  have hodd_scalar : Odd (orderOf (φW g)) :=
    hoddg.of_dvd_nat horder_dvd_g
  have horder_pos : 0 < orderOf (φW g) := Odd.pos hodd_scalar
  have horder_le_two : orderOf (φW g) ≤ 2 :=
    Nat.le_of_dvd (by decide) horder_dvd_two
  have horder_ne_two : orderOf (φW g) ≠ 2 := by
    intro htwo
    rw [htwo] at hodd_scalar
    exact (by norm_num : ¬ Odd (2 : ℕ)) hodd_scalar
  have horder_one : orderOf (φW g) = 1 := by omega
  have hφW_one : φW g = 1 := orderOf_eq_one_iff.mp horder_one
  have hφU_one : φU g = 1 := by
    simpa [φW, φU, hsame] using hφW_one
  have hg_one : g = 1 := by
    apply hfaithful
    ext v
    obtain ⟨w, u, hv, _huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
    have hw_fix : ρ g (w : V) = (w : V) := by
      have hw_scalar :=
        scalarCharacterOfFinrankEqOne_apply_smul hdimW
          (ρ.subrepresentation W hW) g w
      calc
        ρ g (w : V) = (φW g : F) • (w : V) := congrArg Subtype.val hw_scalar
        _ = (w : V) := by simp [hφW_one]
    have hu_fix : ρ g (u : V) = (u : V) := by
      have hu_scalar :=
        scalarCharacterOfFinrankEqOne_apply_smul hdimU
          (ρ.subrepresentation U hU) g u
      calc
        ρ g (u : V) = (φU g : F) • (u : V) := congrArg Subtype.val hu_scalar
        _ = (u : V) := by simp [hφU_one]
    calc
      ρ g v = ρ g ((w : V) + (u : V)) := by rw [hv]
      _ = ρ g (w : V) + ρ g (u : V) := map_add (ρ g) (w : V) (u : V)
      _ = (w : V) + (u : V) := by rw [hw_fix, hu_fix]
      _ = v := hv
      _ = (ρ 1) v := by simp
  exact hg_ne_one hg_one

/-- A nontrivial odd-order determinant-kernel element with two complementary
rank-one eigenspaces exhausts the rank-one subrepresentations.

This packages the BG Thm 2.6 q ≠ p step that the distinct eigenvalues of
`x ∈ K#` make the two Maschke lines the only one-dimensional `K`-submodules. -/
private theorem rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_element
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (W U : Subrepresentation ρ)
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F U.toSubmodule] [Module.Free F (V ⧸ W.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQ : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    {x : G} (hxdet : x ∈ determinantKernelSubgroup ρ)
    (hoddx : Odd (orderOf x)) (hx_ne_one : x ≠ 1) :
    ∀ L : Subrepresentation ρ,
      Module.finrank F L.toSubmodule = 1 → L = W ∨ L = U := by
  have hW : ∀ g : G, W.toSubmodule ≤ W.toSubmodule.comap (ρ g) := by
    intro g v hv
    exact W.apply_mem_toSubmodule g hv
  have hU : ∀ g : G, U.toSubmodule ≤ U.toSubmodule.comap (ρ g) := by
    intro g v hv
    exact U.apply_mem_toSubmodule g hv
  let φW : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W.toSubmodule hW)
  let φU : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U.toSubmodule hU)
  have hdistinct_units : φW x ≠ φU x :=
    scalarCharacters_ne_of_mem_determinantKernel_of_ne_one
      W.toSubmodule U.toSubmodule ρ hfaithful hcompl hW hU hdimW hdimU hdimQ
      hxdet hoddx hx_ne_one
  have hdistinct : (φW x : F) ≠ (φU x : F) := by
    intro hval
    exact hdistinct_units (Units.ext hval)
  intro L hLdim
  have hLstable : L.toSubmodule ≤ L.toSubmodule.comap (ρ x) := by
    intro v hv
    exact L.apply_mem_toSubmodule x hv
  have hWscalar : ∀ w ∈ W.toSubmodule, ρ x w = (φW x : F) • w := by
    intro w hw
    have hw_scalar :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimW
        (ρ.subrepresentation W.toSubmodule hW) x ⟨w, hw⟩
    exact congrArg Subtype.val hw_scalar
  have hUscalar : ∀ u ∈ U.toSubmodule, ρ x u = (φU x : F) • u := by
    intro u hu
    have hu_scalar :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimU
        (ρ.subrepresentation U.toSubmodule hU) x ⟨u, hu⟩
    exact congrArg Subtype.val hu_scalar
  rcases rank_one_invariant_submodule_eq_left_or_right_of_distinct_scalars
      W.toSubmodule U.toSubmodule L.toSubmodule (ρ x)
      hcompl hdimW hdimU hLdim hLstable (φW x : F) (φU x : F)
      hdistinct hWscalar hUscalar with hLW | hLU
  · left
    exact Subrepresentation.toSubmodule_injective hLW
  · right
    exact Subrepresentation.toSubmodule_injective hLU

/-- Ambient form of
`rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_element`.

If `K ≤ G*` and `G` has odd order, a nontrivial element of `K` supplies the
distinct-scalar witness for the restricted `K`-representation.  This is the
form needed before applying the normal-conjugate line bridge. -/
private theorem rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F U.toSubmodule] [Module.Free F (V ⧸ W.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQ : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) :
    ∀ L : Subrepresentation (ρ.comp K.subtype),
      Module.finrank F L.toSubmodule = 1 → L = W ∨ L = U := by
  have hρK_faithful : Function.Injective (ρ.comp K.subtype) := by
    intro a b hab
    apply Subtype.ext
    exact hfaithful (by simpa using hab)
  have hxdet : x ∈ determinantKernelSubgroup (ρ.comp K.subtype) := by
    have hxdetG : (x : G) ∈ determinantKernelSubgroup ρ := hKle x.2
    rw [mem_determinantKernelSubgroup] at hxdetG ⊢
    simpa [determinantCharacterOfRepresentation, representationToGeneralLinearGroup] using hxdetG
  have hoddxG : Odd (orderOf (x : G)) :=
    hodd.of_dvd_nat (orderOf_dvd_natCard (x : G))
  have hoddx : Odd (orderOf x) := by
    simpa [Subgroup.orderOf_coe x] using hoddxG
  exact rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_element
    (ρ.comp K.subtype) hρK_faithful W U hcompl hdimW hdimU hdimQ
    hxdet hoddx hx_ne_one

/-- Determinant-kernel uniqueness forces every ambient conjugate of one Maschke
line to be one of the two Maschke lines.

This is the next BG Thm 2.6 q ≠ p bridge after choosing a nontrivial
`x : K`: normality makes the conjugate a `K`-subrepresentation, and the
distinct-scalar uniqueness pins it to `W` or `U`. -/
private theorem conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F U.toSubmodule] [Module.Free F (V ⧸ W.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQ : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    conjugateSubrepresentationOfNormal K hKnormal ρ W g = W ∨
      conjugateSubrepresentationOfNormal K hKnormal ρ W g = U := by
  exact conjugateSubrepresentation_eq_left_or_right_of_rank_one_unique
    K hKnormal ρ W U hdimW
    (rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKle W U hcompl hdimW hdimU hdimQ hx_ne_one)
    g

/-- `comap` form of
`conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup`.

This is the shape required by `RankOneLinePairData.permutes` for one of the
two lines. -/
private theorem le_comap_left_or_right_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F U.toSubmodule] [Module.Free F (V ⧸ W.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQ : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    W.toSubmodule ≤ W.toSubmodule.comap (ρ g) ∨
      W.toSubmodule ≤ U.toSubmodule.comap (ρ g) := by
  rcases conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQ
      hx_ne_one g with hleft | hright
  · left
    exact le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ W W hleft
  · right
    exact le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ W U hright

/-- Symmetric `comap` form for both Maschke lines.

This packages the two applications of
`le_comap_left_or_right_of_determinantKernel_subgroup`, once for each line, so
the next step can choose a coherent permutation of the two labels. -/
private theorem both_lines_le_comap_left_or_right_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F W.toSubmodule] [Module.Finite F U.toSubmodule]
    [Module.Free F (V ⧸ W.toSubmodule)] [Module.Free F (V ⧸ U.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQW : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    (hdimQU : Module.finrank F (V ⧸ U.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    (W.toSubmodule ≤ W.toSubmodule.comap (ρ g) ∨
      W.toSubmodule ≤ U.toSubmodule.comap (ρ g)) ∧
    (U.toSubmodule ≤ W.toSubmodule.comap (ρ g) ∨
      U.toSubmodule ≤ U.toSubmodule.comap (ρ g)) := by
  constructor
  · exact le_comap_left_or_right_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQW
      hx_ne_one g
  · rcases le_comap_left_or_right_of_determinantKernel_subgroup
        ρ hfaithful hodd K hKnormal hKle U W hcompl.symm hdimU hdimW hdimQU
        hx_ne_one g with hstay | hswap
    · right
      exact hstay
    · left
      exact hswap

/-- The two conjugate-line alternatives are coherent: an ambient element either
preserves both Maschke lines or swaps them.

The impossible mixed cases would make the two conjugate complementary lines
land on the same nonzero rank-one line. -/
private theorem conjugateSubrepresentations_stay_or_swap_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F W.toSubmodule] [Module.Finite F U.toSubmodule]
    [Module.Free F (V ⧸ W.toSubmodule)] [Module.Free F (V ⧸ U.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQW : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    (hdimQU : Module.finrank F (V ⧸ U.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    (conjugateSubrepresentationOfNormal K hKnormal ρ W g = W ∧
      conjugateSubrepresentationOfNormal K hKnormal ρ U g = U) ∨
    (conjugateSubrepresentationOfNormal K hKnormal ρ W g = U ∧
      conjugateSubrepresentationOfNormal K hKnormal ρ U g = W) := by
  have hW_ne_bot : W.toSubmodule ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  have hU_ne_bot : U.toSubmodule ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  have hcomplg :
      IsCompl
        (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule
        (conjugateSubrepresentationOfNormal K hKnormal ρ U g).toSubmodule :=
    isCompl_conjugateSubrepresentationOfNormal K hKnormal ρ W U g hcompl
  rcases conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQW
      hx_ne_one g with hWW | hWU
  · rcases conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
        ρ hfaithful hodd K hKnormal hKle U W hcompl.symm hdimU hdimW hdimQU
        hx_ne_one g with hUU | hUW
    · exact Or.inl ⟨hWW, hUU⟩
    · exfalso
      have hW_bot : W.toSubmodule = ⊥ := by
        have hleft := congrArg Subrepresentation.toSubmodule hWW
        have hright := congrArg Subrepresentation.toSubmodule hUW
        simpa [hleft, hright] using hcomplg.inf_eq_bot
      exact hW_ne_bot hW_bot
  · rcases conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
        ρ hfaithful hodd K hKnormal hKle U W hcompl.symm hdimU hdimW hdimQU
        hx_ne_one g with hUU | hUW
    · exfalso
      have hU_bot : U.toSubmodule = ⊥ := by
        have hleft := congrArg Subrepresentation.toSubmodule hWU
        have hright := congrArg Subrepresentation.toSubmodule hUU
        simpa [hleft, hright] using hcomplg.inf_eq_bot
      exact hU_ne_bot hU_bot
    · exact Or.inr ⟨hWU, hUW⟩

/-- Coherent `comap` form of the two-line alternatives: each ambient element
either preserves both lines or swaps them. -/
private theorem both_lines_le_comap_stay_or_swap_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F W.toSubmodule] [Module.Finite F U.toSubmodule]
    [Module.Free F (V ⧸ W.toSubmodule)] [Module.Free F (V ⧸ U.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQW : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    (hdimQU : Module.finrank F (V ⧸ U.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    (W.toSubmodule ≤ W.toSubmodule.comap (ρ g) ∧
      U.toSubmodule ≤ U.toSubmodule.comap (ρ g)) ∨
    (W.toSubmodule ≤ U.toSubmodule.comap (ρ g) ∧
      U.toSubmodule ≤ W.toSubmodule.comap (ρ g)) := by
  rcases conjugateSubrepresentations_stay_or_swap_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQW hdimQU
      hx_ne_one g with hstay | hswap
  · exact Or.inl
      ⟨le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ W W hstay.1,
        le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ U U hstay.2⟩
  · exact Or.inr
      ⟨le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ W U hswap.1,
        le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ U W hswap.2⟩

/-- The commutator subgroup lies in the determinant kernel. -/
private theorem commutator_le_determinantKernelSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    commutator G ≤ determinantKernelSubgroup ρ := by
  simpa [determinantKernelSubgroup] using
    (commutator_le_ker_of_units_character (determinantCharacterOfRepresentation ρ))

/-- An injective character into `Fˣ` forces the source group to be abelian. -/
private theorem commutative_of_injective_units_character
    {F : Type*} [Field F] {G : Type*} [Group G] (φ : G →* Fˣ)
    (hφ : Function.Injective φ) :
    Std.Commutative (· * · : G → G → G) := by
  constructor
  intro x y
  apply hφ
  calc
    φ (x * y) = φ x * φ y := map_mul φ x y
    _ = φ y * φ x := by rw [mul_comm]
    _ = φ (y * x) := (map_mul φ y x).symm

private theorem determinantCharacter_injective_of_kernel_eq_bot
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hker : determinantKernelSubgroup ρ = ⊥) :
    Function.Injective (determinantCharacterOfRepresentation ρ) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by
    simpa [determinantKernelSubgroup] using hker)

/-- BG Thm 2.6 determinant endpoint: if `G* = ker(det ∘ ρ)` is trivial, then
the determinant character embeds `G` into the abelian group `Fˣ`. -/
private theorem commutative_of_determinantKernel_eq_bot
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hker : determinantKernelSubgroup ρ = ⊥) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_injective_units_character (determinantCharacterOfRepresentation ρ)
    (determinantCharacter_injective_of_kernel_eq_bot ρ hker)

/-- If `G` preserves a rank-one submodule and rank-one quotient, then `G'`
acts trivially on both.

This is the `G' ≤ C_G(W) ∩ C_G(V/W)` half of BG Thm 2.6, q = p.  Unlike the
p-subgroup bridge above, it does not use characteristic `p`: scalar characters
to `Fˣ` kill commutators because `Fˣ` is abelian. -/
private theorem commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    commutator G ≤ fixedOnSubmoduleAndQuotientSubgroup W ρ := by
  let φW : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW)
  let φQ : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW)
  have hkerW : commutator G ≤ φW.ker :=
    commutator_le_ker_of_units_character φW
  have hkerQ : commutator G ≤ φQ.ker :=
    commutator_le_ker_of_units_character φQ
  intro g hg
  rw [mem_fixedOnSubmoduleAndQuotientSubgroup]
  constructor
  · intro w hw
    have hφW : φW g = 1 := MonoidHom.mem_ker.mp (hkerW hg)
    have hsub :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimW
        (ρ.subrepresentation W hW) g ⟨w, hw⟩
    calc
      ρ g w = (φW g : F) • w := congrArg Subtype.val hsub
      _ = w := by simp [hφW]
  · intro v
    have hφQ : φQ g = 1 := MonoidHom.mem_ker.mp (hkerQ hg)
    have hq :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimQ (ρ.quotient W hW) g
        (Submodule.Quotient.mk v : V ⧸ W)
    change Submodule.Quotient.mk (ρ g v) =
      (φQ g : F) • (Submodule.Quotient.mk v : V ⧸ W) at hq
    have hq_one :
        (Submodule.Quotient.mk (ρ g v) : V ⧸ W) =
          (Submodule.Quotient.mk v : V ⧸ W) := by
      simpa [hφQ] using hq
    simpa [Submodule.Quotient.eq] using hq_one

/-- An element acting trivially on a submodule and on the quotient is the identity
if it also preserves a complementary submodule.

This is the diagonal-form bridge for BG Thm 2.6, q ≠ p: once the two
one-dimensional `K`-submodules are both `G`-invariant, a commutator that is
trivial on one line and on the quotient is trivial on the complementary line
as well. -/
private theorem eq_one_of_mem_fixedOnSubmoduleAndQuotientSubgroup_of_preserves_complement
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hcompl : IsCompl W U)
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    g = 1 := by
  apply hfaithful
  ext v
  obtain ⟨w, u, hv, _huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
  have hgW : ∀ w ∈ W, ρ g w = w :=
    (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).1
  have hgQ : ∀ v, ρ g v - v ∈ W :=
    (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).2
  have hfixU : ρ g (u : V) = (u : V) := by
    have hdiffW : ρ g (u : V) - (u : V) ∈ W := hgQ u
    have hdiffU : ρ g (u : V) - (u : V) ∈ U :=
      U.sub_mem (hU g u.2) u.2
    have hdiff_bot : ρ g (u : V) - (u : V) ∈ (⊥ : Submodule F V) := by
      simpa [hcompl.inf_eq_bot] using (show ρ g (u : V) - (u : V) ∈ W ⊓ U from
        ⟨hdiffW, hdiffU⟩)
    exact sub_eq_zero.mp (by simpa using hdiff_bot)
  calc
    ρ g v = ρ g ((w : V) + (u : V)) := by rw [hv]
    _ = ρ g (w : V) + ρ g (u : V) := map_add (ρ g) (w : V) (u : V)
    _ = (w : V) + (u : V) := by rw [hgW (w : V) w.2, hfixU]
    _ = v := hv
    _ = (ρ 1) v := by simp

/-- If a faithful representation preserves complementary one-dimensional
submodules, then the group is abelian.

In the q≠p branch of BG Thm 2.6, Maschke and algebraic closedness give
`V = W₁ ⊕ W₂` with both lines `G`-invariant.  The two rank-one scalar
characters kill commutators on `W₁` and on `V/W₁`; the complement prevents any
remaining unipotent shear. -/
private theorem commutative_of_faithful_representation_preserves_rank_one_complement
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hcompl : IsCompl W U) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimW : Module.finrank F W = 1)
    (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    Std.Commutative (· * · : G → G → G) := by
  constructor
  intro x y
  rw [← commutatorElement_eq_one_iff_mul_comm]
  apply eq_one_of_mem_fixedOnSubmoduleAndQuotientSubgroup_of_preserves_complement
    W U ρ hfaithful hcompl hU
  exact commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    W ρ hW hdimW hdimQ
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

/-- Odd order turns a stay/swap dichotomy for two complementary lines into
actual preservation of both lines.

This is the line-permutation step in BG Thm 2.6, q ≠ p, stated without
choosing an explicit `Fin 2` action.  If an element swapped the two lines, then
its square would preserve them; since the element has odd order, the element
itself is a power of its square, contradiction with the nonzero first line and
the direct-sum decomposition. -/
private theorem preserves_of_stay_or_swap_rank_one_complement_of_odd
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Finite F W]
    (ρ : Representation F G V)
    (hodd : Odd (Nat.card G)) (hcompl : IsCompl W U)
    (hstay_swap : ∀ g : G,
      (W ≤ W.comap (ρ g) ∧ U ≤ U.comap (ρ g)) ∨
      (W ≤ U.comap (ρ g) ∧ U ≤ W.comap (ρ g)))
    (hdimW : Module.finrank F W = 1) :
    ∀ g : G, W ≤ W.comap (ρ g) ∧ U ≤ U.comap (ρ g) := by
  intro g
  rcases hstay_swap g with hstay | hswap
  · exact hstay
  · exfalso
    have hW_ne_bot : W ≠ ⊥ := by
      rw [← Submodule.one_le_finrank_iff]
      omega
    have hg2W : W ≤ W.comap (ρ (g ^ 2)) := by
      intro w hw
      rw [pow_two, map_mul]
      exact hswap.2 (hswap.1 hw)
    have hpowW : ∀ n : ℕ, W ≤ W.comap (ρ ((g ^ 2) ^ n)) := by
      intro n
      induction n with
      | zero =>
          intro w hw
          simpa using hw
      | succ n ih =>
          intro w hw
          rw [pow_succ, map_mul]
          exact ih (hg2W hw)
    have hoddg : Odd (orderOf g) := hodd.of_dvd_nat (orderOf_dvd_natCard g)
    rcases hoddg with ⟨k, hk⟩
    have hg_pow_square : g = (g ^ 2) ^ (k + 1) := by
      calc
        g = g ^ (orderOf g + 1) := by
          rw [pow_succ, pow_orderOf_eq_one, one_mul]
        _ = g ^ (2 * (k + 1)) := by
          congr 1
          omega
        _ = (g ^ 2) ^ (k + 1) := by
          rw [pow_mul]
    have hgW : W ≤ W.comap (ρ g) := by
      rw [hg_pow_square]
      exact hpowW (k + 1)
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hW_ne_bot with ⟨w, hwW, hw_ne_zero⟩
    have hρgw_bot : ρ g w ∈ (⊥ : Submodule F V) := by
      have hρgw_inf : ρ g w ∈ W ⊓ U := ⟨hgW hwW, hswap.1 hwW⟩
      simpa [hcompl.inf_eq_bot] using hρgw_inf
    have hρgw_zero : ρ g w = 0 := by
      simpa using hρgw_bot
    have hw_zero : w = 0 := by
      have hleft : ρ g⁻¹ (ρ g w) = w := by
        calc
          ρ g⁻¹ (ρ g w) = ((ρ g⁻¹) * (ρ g)) w := rfl
          _ = ρ (g⁻¹ * g) w := by rw [map_mul]
          _ = w := by simp
      simpa [hleft] using congrArg (ρ g⁻¹) hρgw_zero
    exact hw_ne_zero hw_zero

/-- Stay/swap form of the odd-order two-line bridge.

This avoids building a separate `Fin 2` action when the proof has already
produced the concrete dichotomy that every element preserves both lines or
swaps them. -/
private theorem commutative_of_faithful_representation_stay_or_swap_rank_one_complement_of_odd
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Finite F W]
    [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hcompl : IsCompl W U)
    (hstay_swap : ∀ g : G,
      (W ≤ W.comap (ρ g) ∧ U ≤ U.comap (ρ g)) ∨
      (W ≤ U.comap (ρ g) ∧ U ≤ W.comap (ρ g)))
    (hdimW : Module.finrank F W = 1)
    (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    Std.Commutative (· * · : G → G → G) := by
  have hpreserve :=
    preserves_of_stay_or_swap_rank_one_complement_of_odd
      W U ρ hodd hcompl hstay_swap hdimW
  exact commutative_of_faithful_representation_preserves_rank_one_complement
    W U ρ hfaithful hcompl
    (fun g => (hpreserve g).1) (fun g => (hpreserve g).2) hdimW hdimQ

/-- Determinant-kernel line-pair bridge for the q≠p branch.

Once Maschke has produced two complementary rank-one `K`-submodules and a
nontrivial element of the normal subgroup `K ≤ G*`, the determinant-kernel
uniqueness argument gives a stay/swap dichotomy for every ambient group
element.  Odd order removes the swap case, so the faithful diagonal bridge
makes `G` abelian. -/
private theorem commutative_of_determinantKernel_subgroup_rank_one_complement
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F W.toSubmodule] [Module.Finite F U.toSubmodule]
    [Module.Free F (V ⧸ W.toSubmodule)] [Module.Free F (V ⧸ U.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQW : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    (hdimQU : Module.finrank F (V ⧸ U.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) :
    Std.Commutative (· * · : G → G → G) := by
  exact
    commutative_of_faithful_representation_stay_or_swap_rank_one_complement_of_odd
      W.toSubmodule U.toSubmodule ρ hfaithful hodd hcompl
      (fun g =>
        both_lines_le_comap_stay_or_swap_of_determinantKernel_subgroup
          ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQW hdimQU
          hx_ne_one g)
      hdimW hdimQW

/-- Odd-order no-interchange bridge for the q≠p branch of BG Thm 2.6.

If `G` permutes two complementary rank-one submodules, then the induced
permutation action on the two labels is trivial because `|G|` is odd.  Hence
`G` preserves both lines and the diagonal complement bridge makes `G` abelian. -/
private theorem commutative_of_faithful_representation_permuted_rank_one_complement_of_odd
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] [MulAction G (Fin 2)]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Fin 2 → Submodule F V)
    [Module.Free F (W 0)] [Module.Free F (V ⧸ W 0)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hcompl : IsCompl (W 0) (W 1))
    (hperm : ∀ (g : G) (i : Fin 2), W i ≤ (W (g • i)).comap (ρ g))
    (hdimW : Module.finrank F (W 0) = 1)
    (hdimQ : Module.finrank F (V ⧸ W 0) = 1) :
    Std.Commutative (· * · : G → G → G) := by
  have hW0 : ∀ g : G, W 0 ≤ (W 0).comap (ρ g) := by
    intro g
    simpa [smul_fin_two_eq_self_of_odd_card hodd g (0 : Fin 2)] using
      hperm g (0 : Fin 2)
  have hW1 : ∀ g : G, W 1 ≤ (W 1).comap (ρ g) := by
    intro g
    simpa [smul_fin_two_eq_self_of_odd_card hodd g (1 : Fin 2)] using
      hperm g (1 : Fin 2)
  exact commutative_of_faithful_representation_preserves_rank_one_complement
    (W 0) (W 1) ρ hfaithful hcompl hW0 hW1 hdimW hdimQ

/-- Data produced by the q≠p Maschke/algebraically-closed step in BG Thm 2.6.

The two lines are allowed to be permuted by `G`; odd order later forces the
permutation action on `Fin 2` to be trivial. -/
private structure RankOneLinePairData
    {F : Type*} [Field F] {G : Type*} [Group G] [MulAction G (Fin 2)]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : Type _ where
  W : Fin 2 → Submodule F V
  freeW0 : Module.Free F (W 0)
  freeQ0 : Module.Free F (V ⧸ W 0)
  isCompl : IsCompl (W 0) (W 1)
  permutes : ∀ (g : G) (i : Fin 2), W i ≤ (W (g • i)).comap (ρ g)
  finrankW0 : Module.finrank F (W 0) = 1
  finrankQ0 : Module.finrank F (V ⧸ W 0) = 1

/-- Two-dimensional form of
`commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients`. -/
private theorem commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdim : Module.finrank F V = 2) (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    commutator G ≤ fixedOnSubmoduleAndQuotientSubgroup W ρ := by
  rcases rank_one_subquotients_of_finrank_two W hdim hW_ne_bot hW_ne_top with
    ⟨hdimW, hdimQ⟩
  exact commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    W ρ hW hdimW hdimQ

/-- If `G'` acts trivially on a submodule and quotient, then that common
fixed-on-subquotients subgroup is normal.  This packages the normality shape
needed in the q = p branch of BG Thm 2.6. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_normal_of_rank_one_subquotients
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    (fixedOnSubmoduleAndQuotientSubgroup W ρ).Normal :=
  Subgroup.Normal.of_commutator_le
    (G := G)
    (H := fixedOnSubmoduleAndQuotientSubgroup W ρ)
    (commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
      W ρ hW hdimW hdimQ)

/-- Two-dimensional normality form of
`fixedOnSubmoduleAndQuotientSubgroup_normal_of_rank_one_subquotients`. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_normal_of_finrank_two
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdim : Module.finrank F V = 2) (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    (fixedOnSubmoduleAndQuotientSubgroup W ρ).Normal :=
  Subgroup.Normal.of_commutator_le
    (G := G)
    (H := fixedOnSubmoduleAndQuotientSubgroup W ρ)
    (commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two
      W ρ hW hdim hW_ne_bot hW_ne_top)

/-- A normal p-subgroup is contained in every Sylow p-subgroup.

This is the Sylow-conjugacy bridge used in BG Thm 2.6(b) after a normal
p-subgroup containing `G'` has been constructed. -/
private theorem normal_pSubgroup_le_sylow
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    (N : Subgroup G) (hNnormal : N.Normal) (hN : IsPGroup p N) (P : Sylow p G) :
    N ≤ (P : Subgroup G) := by
  haveI : N.Normal := hNnormal
  obtain ⟨Q, hNQ⟩ := hN.exists_le_sylow
  obtain ⟨g, hgQ⟩ := MulAction.exists_smul_eq G Q P
  calc (N : Subgroup G)
      = MulAut.conj g • N := (Subgroup.Normal.conj_smul_eq_self g N).symm
    _ ≤ MulAut.conj g • (Q : Subgroup G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNQ
    _ = ↑(g • Q) := Sylow.coe_subgroup_smul.symm
    _ = ↑P := by rw [hgQ]

/-- If `G'` lies in a normal p-subgroup, then `G'` lies in every Sylow
p-subgroup. -/
private theorem commutator_le_sylow_of_le_normal_pSubgroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    (N : Subgroup G) (hNnormal : N.Normal) (hN : IsPGroup p N)
    (hcomm : commutator G ≤ N) (P : Sylow p G) :
    commutator G ≤ (P : Subgroup G) :=
  hcomm.trans (normal_pSubgroup_le_sylow N hNnormal hN P)

/-- Two-dimensional fixed-subquotient route to the Sylow containment
`G' ≤ P` in BG Thm 2.6(b), q = p.

Once a nonzero proper invariant submodule `W` is available, the common
fixed-on-subquotients subgroup is normal, is a p-subgroup in characteristic
`p`, and contains `G'`; hence every Sylow p-subgroup contains `G'`. -/
private theorem commutator_le_sylow_of_finrank_two_invariant_submodule
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdim : Module.finrank F V = 2) (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤)
    (P : Sylow p G) :
    commutator G ≤ (P : Subgroup G) := by
  have hVpos : 0 < Module.finrank F V := by
    rw [hdim]
    norm_num
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) hVpos
  exact commutator_le_sylow_of_le_normal_pSubgroup
    (fixedOnSubmoduleAndQuotientSubgroup W ρ)
    (fixedOnSubmoduleAndQuotientSubgroup_normal_of_finrank_two
      W ρ hW hdim hW_ne_bot hW_ne_top)
    (fixedOnSubmoduleAndQuotientSubgroup_isPGroup_of_faithful
      (p := p) W ρ hfaithful)
    (commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two
      W ρ hW hdim hW_ne_bot hW_ne_top)
    P

/-- Two-dimensional wrapper for
`subgroup_commutative_of_rank_one_subquotients`.

This is the form needed in BG Thm 2.6, q = p, after constructing a nonzero
proper invariant fixed-space `W = C_V(K)`. -/
private theorem subgroup_commutative_of_finrank_two_invariant_submodule
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (H : Subgroup G) (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ) (hH : IsPGroup p H)
    (hW : ∀ h : H, W ≤ W.comap (ρ h))
    (hdim : Module.finrank F V = 2) (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    Std.Commutative (· * · : H → H → H) := by
  rcases rank_one_subquotients_of_finrank_two W hdim hW_ne_bot hW_ne_top with
    ⟨hdimW, hdimQ⟩
  exact subgroup_commutative_of_rank_one_subquotients
    H W ρ hfaithful hH hW hdimW hdimQ

/-- If a normal p-subgroup has a proper fixed space in a faithful two-dimensional
representation over characteristic `p`, then every p-subgroup preserving that
fixed space is abelian.

In BG Thm 2.6, q = p, this is applied to
`K = Ω₁(Z(O_p(G^*)))` and `W = C_V(K)`.  Nontriviality of `W` is supplied by
`IsPGroup.invariants_ne_bot`; normality of `K` supplies `G`-invariance. -/
private theorem subgroup_commutative_of_normal_p_fixed_space_proper
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K H : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K) (hH : IsPGroup p H)
    (hdim : Module.finrank F V = 2)
    (hfixed_ne_top : Representation.invariants (ρ.comp K.subtype) ≠ ⊤) :
    Std.Commutative (· * · : H → H → H) := by
  let W : Submodule F V := Representation.invariants (ρ.comp K.subtype)
  have hV_ne_bot : (⊤ : Submodule F V) ≠ ⊥ := by
    intro hbot
    have htop : Module.finrank F (⊤ : Submodule F V) = 2 := by
      simp [hdim]
    have hzero : Module.finrank F (⊤ : Submodule F V) = 0 := by
      rw [hbot, finrank_bot]
    omega
  have hW_ne_bot : W ≠ ⊥ := by
    simpa [W] using hK.invariants_ne_bot (ρ.comp K.subtype) hV_ne_bot
  have hW_ne_top : W ≠ ⊤ := by
    simpa [W] using hfixed_ne_top
  have hW_invariant : ∀ h : H, W ≤ W.comap (ρ h) := by
    intro h
    exact Representation.le_comap_invariants ρ K h
  exact subgroup_commutative_of_finrank_two_invariant_submodule
    H W ρ hfaithful hH hW_invariant hdim hW_ne_bot hW_ne_top

/-- In a faithful representation, a nontrivial subgroup cannot fix the whole
space pointwise. -/
private theorem invariants_ne_top_of_faithful_subgroup_ne_bot
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Subgroup G) (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hK_ne_bot : K ≠ ⊥) :
    Representation.invariants (ρ.comp K.subtype) ≠ ⊤ := by
  intro htop
  apply hK_ne_bot
  ext g
  constructor
  · intro hg
    let k : K := ⟨g, hg⟩
    have hk_fixed : ∀ v : V, ρ g v = v := by
      intro v
      have hv : v ∈ Representation.invariants (ρ.comp K.subtype) := by
        rw [htop]
        exact Submodule.mem_top
      simpa [k] using (Representation.mem_invariants (ρ.comp K.subtype) v).mp hv k
    have hρg : ρ g = 1 := by
      ext v
      exact hk_fixed v
    have hg_one : g = 1 := by
      apply hfaithful
      simp [hρg]
    simp [hg_one]
  · intro hg
    have hg_one : g = 1 := by
      simpa using hg
    simp [hg_one]

/-- Nontrivial-normal-subgroup version of
`subgroup_commutative_of_normal_p_fixed_space_proper`.

This is the closest current Lean entrypoint to BG Thm 2.6, q = p: once the
nontrivial normal p-subgroup `K` is constructed, faithful two-dimensionality
forces its fixed space to be nonzero and proper, hence every p-subgroup is
abelian. -/
private theorem subgroup_commutative_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K H : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K) (hH : IsPGroup p H)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥) :
    Std.Commutative (· * · : H → H → H) :=
  subgroup_commutative_of_normal_p_fixed_space_proper K H ρ hfaithful hK hH hdim
    (invariants_ne_top_of_faithful_subgroup_ne_bot K ρ hfaithful hK_ne_bot)

/-- Nontrivial-normal-p-subgroup form of
`commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two`.

This packages the `G' ≤ C_G(W) ∩ C_G(V/W)` bridge for the same
`W = C_V(K)` used in BG Thm 2.6, q = p. -/
private theorem
    commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥) :
    commutator G ≤
      fixedOnSubmoduleAndQuotientSubgroup
        (Representation.invariants (ρ.comp K.subtype)) ρ := by
  let W : Submodule F V := Representation.invariants (ρ.comp K.subtype)
  have hV_ne_bot : (⊤ : Submodule F V) ≠ ⊥ := by
    intro hbot
    have htop : Module.finrank F (⊤ : Submodule F V) = 2 := by
      simp [hdim]
    have hzero : Module.finrank F (⊤ : Submodule F V) = 0 := by
      rw [hbot, finrank_bot]
    omega
  have hW_ne_bot : W ≠ ⊥ := by
    simpa [W] using hK.invariants_ne_bot (ρ.comp K.subtype) hV_ne_bot
  have hW_ne_top : W ≠ ⊤ := by
    simpa [W] using invariants_ne_top_of_faithful_subgroup_ne_bot K ρ hfaithful hK_ne_bot
  have hW_invariant : ∀ g : G, W ≤ W.comap (ρ g) := by
    intro g
    exact Representation.le_comap_invariants ρ K g
  exact commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two
    W ρ hW_invariant hdim hW_ne_bot hW_ne_top

/-- Nontrivial-normal-p-subgroup normality form for the same
`W = C_V(K)` used in BG Thm 2.6, q = p. -/
private theorem
    fixedOnSubmoduleAndQuotientSubgroup_normal_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥) :
    (fixedOnSubmoduleAndQuotientSubgroup
      (Representation.invariants (ρ.comp K.subtype)) ρ).Normal :=
  Subgroup.Normal.of_commutator_le
    (G := G)
    (H := fixedOnSubmoduleAndQuotientSubgroup
      (Representation.invariants (ρ.comp K.subtype)) ρ)
    (commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_nontrivial_normal_p_fixed_space
      K ρ hfaithful hK hdim hK_ne_bot)

/-- Nontrivial-normal-p-subgroup route to the Sylow containment `G' ≤ P`.

This is the current q = p endpoint: after constructing a nontrivial normal
p-subgroup `K`, its fixed space supplies the invariant submodule `W = C_V(K)`,
and the fixed-subquotient subgroup carries `G'` into every Sylow p-subgroup. -/
private theorem commutator_le_sylow_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥)
    (P : Sylow p G) :
    commutator G ≤ (P : Subgroup G) := by
  let W : Submodule F V := Representation.invariants (ρ.comp K.subtype)
  have hVpos : 0 < Module.finrank F V := by
    rw [hdim]
    norm_num
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) hVpos
  exact commutator_le_sylow_of_le_normal_pSubgroup
    (fixedOnSubmoduleAndQuotientSubgroup W ρ)
    (by
      simpa [W] using
        (fixedOnSubmoduleAndQuotientSubgroup_normal_of_nontrivial_normal_p_fixed_space
          K ρ hfaithful hK hdim hK_ne_bot))
    (fixedOnSubmoduleAndQuotientSubgroup_isPGroup_of_faithful
      (p := p) W ρ hfaithful)
    (by
      simpa [W] using
        (commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_nontrivial_normal_p_fixed_space
          K ρ hfaithful hK hdim hK_ne_bot))
    P

/-- q = p endpoint for BG Thm 2.6(b), conditional on the construction of a
nontrivial normal p-subgroup `K`.

The remaining theorem-level task is to construct the `K` supplied by the BG
argument; once it exists, this lemma gives exactly the Sylow conclusion. -/
private theorem sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  constructor
  · exact subgroup_commutative_of_nontrivial_normal_p_fixed_space
      K (P : Subgroup G) ρ hfaithful hK P.2 hdim hK_ne_bot
  · exact commutator_le_sylow_of_nontrivial_normal_p_fixed_space
      K ρ hfaithful hK hdim hK_ne_bot P

/-- A prime divisor of `|G|` makes `G` nontrivial, hence `⊤ : Subgroup G` is
not `⊥`. -/
private theorem top_ne_bot_of_prime_dvd_card
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hp_dvd : p ∣ Nat.card G) :
    (⊤ : Subgroup G) ≠ ⊥ := by
  have hcard_gt : 1 < Nat.card G :=
    lt_of_lt_of_le (Fact.out (p := p.Prime)).one_lt
      (Nat.le_of_dvd Nat.card_pos hp_dvd)
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  exact top_ne_bot

/-- If the ambient group is abelian, then the Sylow conclusion of
BG Thm 2.6(b) is immediate. -/
private theorem sylow_commutative_and_commutator_le_of_commutative
    {p : ℕ} {G : Type*} [Group G]
    (hGcomm : Std.Commutative (· * · : G → G → G))
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  constructor
  · constructor
    intro x y
    exact Subtype.ext (hGcomm.comm x y)
  · intro g hg
    have hcomm_bot : commutator G = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top, Subgroup.eq_top_iff']
      intro x
      rw [Subgroup.mem_center_iff]
      intro y
      exact hGcomm.comm y x
    rw [hcomm_bot] at hg
    have hg_one : g = 1 := by simpa using hg
    simp [hg_one]

/-- q = p endpoint phrased as the existence of a nontrivial normal p-subgroup.

This is the theorem-facing reduction left after the fixed-space helpers: the
full BG proof only has to produce such a subgroup, then this lemma supplies
the Sylow conclusion. -/
private theorem sylow_commutative_and_commutator_le_of_exists_nontrivial_normal_pSubgroup
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hexists : ∃ K : Subgroup G, K.Normal ∧ IsPGroup p K ∧ K ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  rcases hexists with ⟨K, hKnormal, hK, hK_ne_bot⟩
  haveI : K.Normal := hKnormal
  exact sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space
    K ρ hfaithful hK hdim hK_ne_bot P

/-- q = p endpoint when the determinant kernel `G*` is trivial.

This is the `G* = 1` branch in BG Thm 2.6: the determinant character embeds
`G` into `Fˣ`, so `G` is abelian and hence every Sylow subgroup is abelian and
contains `G'`. -/
private theorem sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hdet : determinantKernelSubgroup ρ = ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  exact sylow_commutative_and_commutator_le_of_commutative
    (commutative_of_determinantKernel_eq_bot ρ hdet) P

/-- q = p endpoint when the determinant kernel `G*` itself is a nontrivial
p-subgroup.

In this case `G*` is already the nontrivial normal p-subgroup needed by the
fixed-space reduction. -/
private theorem sylow_commutative_and_commutator_le_of_nontrivial_determinantKernel_pGroup
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hdet_p : IsPGroup p (determinantKernelSubgroup ρ))
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  haveI : (determinantKernelSubgroup ρ).Normal :=
    determinantKernelSubgroup_normal ρ
  exact sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space
    (determinantKernelSubgroup ρ) ρ hfaithful hdet_p hdim hdet_ne_bot P

/-- A nontrivial normal `p`-subgroup forces the `p`-core to be nontrivial.

This is the small `O_p` bridge used twice in BG Thm 2.6: once for `O_p(G*)`,
and once inside the normalizer of a Sylow `q`-subgroup in the `q ≠ p` branch. -/
private theorem opCore_ne_bot_of_nontrivial_normal_pSubgroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    {K : Subgroup G} [K.Normal] (hK : IsPGroup p K) (hK_ne_bot : K ≠ ⊥) :
    OddOrder.Isaacs.Ch01.opCore p G ≠ ⊥ := by
  intro hop_bot
  apply hK_ne_bot
  refine le_bot_iff.mp ?_
  intro x hx
  rw [← hop_bot]
  exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK hx

/-- A finite nontrivial abelian group has a nontrivial prime core.

This is one half of the induction-output bridge for BG Thm 2.6: when an
inductive subgroup is abelian, any nontrivial Sylow subgroup is normal, hence it
lies in the corresponding `O_r`. -/
private theorem exists_prime_opCore_ne_bot_of_commutative
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hGcomm : Std.Commutative (· * · : G → G → G)) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  have hcard_ne_one : Nat.card G ≠ 1 := (Finite.one_lt_card (α := G)).ne'
  obtain ⟨r, hr_prime, hr_dvd⟩ :=
    Nat.exists_prime_and_dvd hcard_ne_one
  haveI : Fact r.Prime := ⟨hr_prime⟩
  haveI : Finite (Sylow r G) := inferInstance
  obtain ⟨P⟩ := Sylow.nonempty (p := r) (G := G)
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hr_dvd
  have hPnormal : (P : Subgroup G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    change g * x * g⁻¹ ∈ (P : Subgroup G)
    rw [hGcomm.comm g x]
    simpa [mul_assoc] using hx
  haveI : (P : Subgroup G).Normal := hPnormal
  exact ⟨r, hr_prime,
    opCore_ne_bot_of_nontrivial_normal_pSubgroup
      (G := G) (K := (P : Subgroup G)) P.2 hP_ne_bot⟩

/-- A BG Thm 2.6(b)-style Sylow conclusion supplies a nontrivial prime core.

If `G'` is nontrivial then `G' ≤ P` makes the derived subgroup a nontrivial
normal `p`-subgroup.  If `G' = 1`, the group is abelian, so a nontrivial Sylow
subgroup gives a nontrivial prime core.  This is the form needed to turn the
induction theorem's Sylow conclusion back into the `hind` input used by the
determinant-kernel spine. -/
private theorem exists_prime_opCore_ne_bot_of_commutator_le_sylow
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Nontrivial G]
    [Finite (Sylow p G)] (P : Sylow p G)
    (hcomm_le : commutator G ≤ (P : Subgroup G)) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  by_cases hcomm_bot : commutator G = ⊥
  · apply exists_prime_opCore_ne_bot_of_commutative
    constructor
    intro x y
    have hxcenter : x ∈ Subgroup.center G := by
      rw [(commutator_eq_bot_iff_center_eq_top (G := G)).mp hcomm_bot]
      trivial
    exact (Subgroup.mem_center_iff.mp hxcenter y).symm
  · haveI : (commutator G).Normal :=
      Subgroup.Normal.of_commutator_le (G := G) (H := commutator G) le_rfl
    have hcomm_p : IsPGroup p (commutator G) := P.2.to_le hcomm_le
    exact ⟨p, Fact.out,
      opCore_ne_bot_of_nontrivial_normal_pSubgroup
        (G := G) (K := commutator G) hcomm_p hcomm_bot⟩

/-- The combined BG Thm 2.6 induction outputs imply a nontrivial prime core.

For a smaller subgroup in the induction, either the ambient characteristic does
not divide its order and the abelian branch supplies a normal Sylow subgroup, or
the characteristic prime divides the order and the Sylow branch supplies
`G' ≤ P`.  Both cases produce some nontrivial `O_r(G)`. -/
private theorem exists_prime_opCore_ne_bot_of_odd_two_dim_outputs
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [hchar : CharP F p]
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hab : (∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) →
      Std.Commutative (· * · : G → G → G))
    (hsyl : p ∣ Nat.card G → (P : Sylow p G) →
      Std.Commutative (· * · : P → P → P) ∧
        commutator G ≤ (P : Subgroup G)) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  by_cases hp_dvd : p ∣ Nat.card G
  · haveI : Finite (Sylow p G) := inferInstance
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    exact exists_prime_opCore_ne_bot_of_commutator_le_sylow
      (p := p) P (hsyl hp_dvd P).2
  · apply exists_prime_opCore_ne_bot_of_commutative
    apply hab
    intro q _hq_prime hq_dvd hq_char
    exact hp_dvd ((CharP.eq F hq_char hchar) ▸ hq_dvd)

/-- Proper determinant-kernel subgroups receive the induction output in the
shape required by the core spine.

For a normal `N < G*`, the restricted representation is still faithful and `N`
has odd order.  Thus the two BG Thm 2.6 induction outputs for that restricted
representation give the nontrivial prime core required by the determinant-kernel
normal-complement spine. -/
private theorem determinantKernel_hind_of_odd_two_dim_induction_outputs
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hab_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 →
        (∀ q : ℕ, q.Prime → q ∣ Nat.card N → ¬ CharP F q) →
        Std.Commutative (· * · : N → N → N))
    (hsyl_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 → p ∣ Nat.card N → (P : Sylow p N) →
        Std.Commutative (· * · : P → P → P) ∧
          commutator N ≤ (P : Subgroup N))
    (N : Subgroup (determinantKernelSubgroup ρ))
    (hNnormal : N.Normal) (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥ := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let ρN : Representation F N V := ρ.comp (Gstar.subtype.comp N.subtype)
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne_bot
  have hfaithfulN : Function.Injective ρN := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hfaithful (by simpa [ρN, Gstar] using hxy)
  have hoddN : Odd (Nat.card N) := by
    have hN_dvd_Gstar : Nat.card N ∣ Nat.card Gstar :=
      Subgroup.card_subgroup_dvd_card N
    have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card Gstar
    exact hodd.of_dvd_nat (hN_dvd_Gstar.trans hGstar_dvd_G)
  exact exists_prime_opCore_ne_bot_of_odd_two_dim_outputs
    (p := p) (F := F) (G := N)
    (fun hcharN => hab_ind N hNnormal hN_ne_bot hN_ne_top hoddN
      ρN hfaithfulN hdim hcharN)
    (fun hpN P => hsyl_ind N hNnormal hN_ne_bot hN_ne_top hoddN
      ρN hfaithfulN hdim hpN P)

/-- A nontrivial `p`-core in a normal subgroup gives a nontrivial `p`-core
in the ambient group.

This is the ambient-lift needed after the induction step in BG Thm 2.6: if a
normal complement `N ⊴ G*` has `O_r(N) ≠ 1`, then `O_r(G*) ≠ 1`. -/
private theorem opCore_ne_bot_of_normal_subgroup_opCore_ne_bot
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    (N : Subgroup G) [N.Normal]
    (hNcore : OddOrder.Isaacs.Ch01.opCore p N ≠ ⊥) :
    OddOrder.Isaacs.Ch01.opCore p G ≠ ⊥ := by
  let K : Subgroup G := (OddOrder.Isaacs.Ch01.opCore p N).map N.subtype
  haveI : (OddOrder.Isaacs.Ch01.opCore p N).Characteristic :=
    OddOrder.Isaacs.Ch01.opCore.characteristic p N
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hKp : IsPGroup p K := by
    dsimp [K]
    exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p N).map N.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    apply hNcore
    have hmap :
        (OddOrder.Isaacs.Ch01.opCore p N).map N.subtype =
          (⊥ : Subgroup N).map N.subtype := by
      simpa [K] using hK_bot
    exact (Subgroup.map_subtype_inj (H := N)).mp hmap
  exact opCore_ne_bot_of_nontrivial_normal_pSubgroup
    (G := G) (K := K) hKp hK_ne_bot

/-- A nontrivial `q`-core contains a nontrivial abelian normal `q`-subgroup.

This is the group-theoretic precursor to BG's
`K = Ω₁(Z(O_q(G^*)))`: before introducing `Ω₁`, the center of `O_q(G)` already
gives a nontrivial abelian normal `q`-subgroup. -/
private theorem exists_nontrivial_normal_commutative_qSubgroup_of_opCore_ne_bot
    {q : ℕ} [Fact q.Prime] {G : Type*} [Group G] [Finite G] [Finite (Sylow q G)]
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q G ≠ ⊥) :
    ∃ K : Subgroup G, K.Normal ∧ IsPGroup q K ∧ K ≠ ⊥ ∧
      Std.Commutative (· * · : K → K → K) := by
  set O : Subgroup G := OddOrder.Isaacs.Ch01.opCore q G with hO_def
  have hO_ne_bot : O ≠ ⊥ := by
    simpa [hO_def] using hcore_ne_bot
  have hO_p : IsPGroup q O := by
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup q G
  have hO_nontrivial : Nontrivial O :=
    (Subgroup.nontrivial_iff_ne_bot O).mpr hO_ne_bot
  haveI : Nontrivial O := hO_nontrivial
  have hcenter_nontrivial : Nontrivial (Subgroup.center O) := by
    have htop_nontrivial : Nontrivial (⊤ : Subgroup O) :=
      (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup O)).mpr top_ne_bot
    have h :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial
        (P := O) (p := q) (N := (⊤ : Subgroup O))
        hO_p htop_nontrivial
    simpa using h
  let Z : Subgroup G := (Subgroup.center O).map O.subtype
  haveI : O.Normal := by
    rw [hO_def]
    infer_instance
  haveI : (Subgroup.center O).Characteristic := Subgroup.centerCharacteristic
  have hZnormal : Z.Normal := by
    dsimp [Z]
    infer_instance
  have hZp : IsPGroup q Z := by
    dsimp [Z]
    exact (hO_p.to_subgroup (Subgroup.center O)).map O.subtype
  have hZ_ne_bot : Z ≠ ⊥ := by
    intro hZ_bot
    have hcenter_ne_bot : Subgroup.center O ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (Subgroup.center O)).mp hcenter_nontrivial
    apply hcenter_ne_bot
    have hmap :
        (Subgroup.center O).map O.subtype = (⊥ : Subgroup O).map O.subtype := by
      simpa [Z] using hZ_bot
    exact (Subgroup.map_subtype_inj (H := O)).mp hmap
  have hZcomm : Std.Commutative (· * · : Z → Z → Z) := by
    constructor
    intro x y
    apply Subtype.ext
    rcases x.property with ⟨xO, hxO_center, hx_eq⟩
    rcases y.property with ⟨yO, _hyO_center, hy_eq⟩
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hx_eq, ← hy_eq]
    simpa using (congr_arg Subtype.val
      (Subgroup.mem_center_iff.mp hxO_center yO)).symm
  exact ⟨Z, hZnormal, hZp, hZ_ne_bot, hZcomm⟩

/-- Determinant-kernel q-core bridge for BG Thm 2.6, q≠p.

From `O_q(G*) ≠ 1`, construct a nontrivial abelian normal q-subgroup of the
ambient group `G` that still lies in `G*`.  This is the formal counterpart of
BG's choice `K = Ω₁(Z(O_q(G*)))`, stopping just before the `Ω₁` refinement. -/
private theorem exists_ambient_normal_commutative_qSubgroup_le_determinantKernel_of_opCore_ne_bot
    {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ determinantKernelSubgroup ρ ∧
      IsPGroup q K ∧ K ≠ ⊥ ∧ Std.Commutative (· * · : K → K → K) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let Ostar : Subgroup Gstar := OddOrder.Isaacs.Ch01.opCore q Gstar
  let Oamb : Subgroup G := Ostar.map Gstar.subtype
  haveI : Gstar.Normal := by
    dsimp [Gstar]
    exact determinantKernelSubgroup_normal ρ
  haveI : Ostar.Characteristic := by
    dsimp [Ostar]
    exact OddOrder.Isaacs.Ch01.opCore.characteristic q Gstar
  have hOamb_normal : Oamb.Normal := by
    dsimp [Oamb]
    infer_instance
  have hOamb_p : IsPGroup q Oamb := by
    dsimp [Oamb, Ostar]
    exact (OddOrder.Isaacs.Ch01.opCore_isPGroup q Gstar).map Gstar.subtype
  have hOamb_ne_bot : Oamb ≠ ⊥ := by
    intro hOamb_bot
    apply hcore_ne_bot
    have hmap :
        Ostar.map Gstar.subtype = (⊥ : Subgroup Gstar).map Gstar.subtype := by
      simpa [Oamb] using hOamb_bot
    exact (Subgroup.map_subtype_inj (H := Gstar)).mp hmap
  have hOamb_nontrivial : Nontrivial Oamb :=
    (Subgroup.nontrivial_iff_ne_bot Oamb).mpr hOamb_ne_bot
  haveI : Nontrivial Oamb := hOamb_nontrivial
  have hcenter_nontrivial : Nontrivial (Subgroup.center Oamb) := by
    have htop_nontrivial : Nontrivial (⊤ : Subgroup Oamb) :=
      (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup Oamb)).mpr top_ne_bot
    have h :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial
        (P := Oamb) (p := q) (N := (⊤ : Subgroup Oamb))
        hOamb_p htop_nontrivial
    simpa using h
  let K : Subgroup G := (Subgroup.center Oamb).map Oamb.subtype
  haveI : Oamb.Normal := hOamb_normal
  haveI : (Subgroup.center Oamb).Characteristic := Subgroup.centerCharacteristic
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hOamb_le_Gstar : Oamb ≤ Gstar := by
    intro x hx
    rcases hx with ⟨xstar, _hxstar, rfl⟩
    exact xstar.2
  have hK_le_Gstar : K ≤ Gstar := by
    intro x hx
    rcases hx with ⟨xO, _hxO_center, rfl⟩
    exact hOamb_le_Gstar xO.2
  have hKp : IsPGroup q K := by
    dsimp [K]
    exact (hOamb_p.to_subgroup (Subgroup.center Oamb)).map Oamb.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    have hcenter_ne_bot : Subgroup.center Oamb ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (Subgroup.center Oamb)).mp hcenter_nontrivial
    apply hcenter_ne_bot
    have hmap :
        (Subgroup.center Oamb).map Oamb.subtype =
          (⊥ : Subgroup Oamb).map Oamb.subtype := by
      simpa [K] using hK_bot
    exact (Subgroup.map_subtype_inj (H := Oamb)).mp hmap
  have hKcomm : Std.Commutative (· * · : K → K → K) := by
    constructor
    intro x y
    apply Subtype.ext
    rcases x.property with ⟨xO, hxO_center, hx_eq⟩
    rcases y.property with ⟨yO, _hyO_center, hy_eq⟩
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hx_eq, ← hy_eq]
    simpa using (congr_arg Subtype.val
      (Subgroup.mem_center_iff.mp hxO_center yO)).symm
  exact ⟨K, hKnormal, hK_le_Gstar, hKp, hK_ne_bot, hKcomm⟩

/-- q≠p core branch reduced to the Maschke line-pair construction.

After `O_q(G*) ≠ 1` supplies an abelian normal q-subgroup `K ≤ G*`, it remains
to construct the two rank-one `K`-module lines and prove that `G` permutes
them.  This theorem connects exactly that future line-pair data to the
already-formalized odd-order no-interchange bridge. -/
private theorem commutative_of_determinantKernel_opCore_ne_bot_of_rankOneLinePair
    {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G] [MulAction G (Fin 2)]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥)
    (hline : ∀ K : Subgroup G, K.Normal → K ≤ determinantKernelSubgroup ρ →
      IsPGroup q K → K ≠ ⊥ → Std.Commutative (· * · : K → K → K) →
      RankOneLinePairData ρ) :
    Std.Commutative (· * · : G → G → G) := by
  rcases exists_ambient_normal_commutative_qSubgroup_le_determinantKernel_of_opCore_ne_bot
      ρ hcore_ne_bot with
    ⟨K, hKnormal, hK_le_Gstar, hKq, hK_ne_bot, hKcomm⟩
  let D := hline K hKnormal hK_le_Gstar hKq hK_ne_bot hKcomm
  letI : Module.Free F (D.W 0) := D.freeW0
  letI : Module.Free F (V ⧸ D.W 0) := D.freeQ0
  exact commutative_of_faithful_representation_permuted_rank_one_complement_of_odd
    D.W ρ hfaithful hodd D.isCompl D.permutes D.finrankW0 D.finrankQ0

/-- q≠p core branch reduced to constructing complementary rank-one
`K`-submodules.

This is the action-free successor to
`commutative_of_determinantKernel_opCore_ne_bot_of_rankOneLinePair`: the
Maschke/algebraically-closed step only has to provide two complementary
rank-one subrepresentations for the normal abelian `q`-subgroup `K ≤ G*`.
The determinant-kernel uniqueness and odd-order no-swap arguments then make
the ambient group abelian. -/
private theorem commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules
    {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥)
    (hline : ∀ K : Subgroup G, K.Normal → K ≤ determinantKernelSubgroup ρ →
      IsPGroup q K → K ≠ ⊥ → Std.Commutative (· * · : K → K → K) →
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
        Module.finrank F (V ⧸ U.toSubmodule) = 1) :
    Std.Commutative (· * · : G → G → G) := by
  rcases exists_ambient_normal_commutative_qSubgroup_le_determinantKernel_of_opCore_ne_bot
      ρ hcore_ne_bot with
    ⟨K, hKnormal, hK_le_Gstar, hKq, hK_ne_bot, hKcomm⟩
  rcases hline K hKnormal hK_le_Gstar hKq hK_ne_bot hKcomm with
    ⟨W, U, hfreeW, hfreeU, hfiniteW, hfiniteU, hfreeQW, hfreeQU,
      hcompl, hdimW, hdimU, hdimQW, hdimQU⟩
  letI : Module.Free F W.toSubmodule := hfreeW.some
  letI : Module.Free F U.toSubmodule := hfreeU.some
  letI : Module.Finite F W.toSubmodule := hfiniteW.some
  letI : Module.Finite F U.toSubmodule := hfiniteU.some
  letI : Module.Free F (V ⧸ W.toSubmodule) := hfreeQW.some
  letI : Module.Free F (V ⧸ U.toSubmodule) := hfreeQU.some
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne_bot
  obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : K)
  exact commutative_of_determinantKernel_subgroup_rank_one_complement
    ρ hfaithful hodd K hKnormal hK_le_Gstar W U hcompl
    hdimW hdimU hdimQW hdimQU hx_ne_one

/-- Algebraically closed q≠p determinant-core endpoint for BG Thm 2.6.

If `O_q(G*)` is nontrivial for a prime `q ≠ p`, Maschke and algebraic
closedness produce the two rank-one `K`-submodules required by the
determinant-kernel uniqueness bridge.  The ambient group is therefore abelian.
The remaining theorem-level work is to route the original field to this
algebraically closed setting and then dispatch the group-theoretic core spine. -/
private theorem commutative_of_determinantKernel_opCore_ne_bot_of_isAlgClosed
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hq_ne_p : q ≠ p)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules
    ρ hfaithful hodd hcore_ne_bot
    (fun K _hKnormal _hKle hKq _hK_ne_bot hKcomm =>
      exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
        ρ hdim K hKq hq_ne_p hKcomm)

/-- Algebraically closed characteristic-away determinant-core endpoint for
BG Thm 2.6(a).

If the characteristic of `F` is not any prime divisor of `|G|`, a nontrivial
`O_q(G*)` supplies an abelian normal q-subgroup `K ≤ G*` whose order is
nonzero in `F`; Maschke then gives the same rank-one data as in the q≠p
branch. -/
private theorem commutative_of_determinantKernel_opCore_ne_bot_of_isAlgClosed_charAway
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules
    ρ hfaithful hodd hcore_ne_bot
    (fun K _hKnormal _hKle _hKq _hK_ne_bot hKcomm =>
      letI : NeZero (Nat.card K : F) :=
        neZero_nat_card_cast_of_subgroup_forall_prime_not_char hchar K
      exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
        ρ hdim K hKcomm)

/-- Algebraically closed q≠p endpoint when the determinant is already trivial.

This is the normalizer form of the q≠p branch: for subgroups lying inside
`G*`, the restricted representation has determinant kernel equal to the whole
group.  A nontrivial `O_q(G)` then supplies the abelian normal `q`-subgroup
needed by the same Maschke line argument. -/
private theorem commutative_of_opCore_ne_bot_of_isAlgClosed_of_determinantKernel_eq_top
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hq_ne_p : q ≠ p)
    (hdet_top : determinantKernelSubgroup ρ = ⊤)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q G ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  haveI : Finite (Sylow q G) := inferInstance
  rcases exists_nontrivial_normal_commutative_qSubgroup_of_opCore_ne_bot
      (q := q) (G := G) hcore_ne_bot with
    ⟨K, hKnormal, hKq, hK_ne_bot, hKcomm⟩
  have hKle : K ≤ determinantKernelSubgroup ρ := by
    intro x _hx
    rw [hdet_top]
    trivial
  rcases exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
      (p := p) (q := q) ρ hdim K hKq hq_ne_p hKcomm with
    ⟨W, U, hfreeW, hfreeU, hfiniteW, hfiniteU, hfreeQW, hfreeQU,
      hcompl, hdimW, hdimU, hdimQW, hdimQU⟩
  letI : Module.Free F W.toSubmodule := hfreeW.some
  letI : Module.Free F U.toSubmodule := hfreeU.some
  letI : Module.Finite F W.toSubmodule := hfiniteW.some
  letI : Module.Finite F U.toSubmodule := hfiniteU.some
  letI : Module.Free F (V ⧸ W.toSubmodule) := hfreeQW.some
  letI : Module.Free F (V ⧸ U.toSubmodule) := hfreeQU.some
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne_bot
  obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : K)
  exact commutative_of_determinantKernel_subgroup_rank_one_complement
    ρ hfaithful hodd K hKnormal hKle W U hcompl
    hdimW hdimU hdimQW hdimQU hx_ne_one

/-- Algebraically closed characteristic-away endpoint when the determinant is
already trivial.

This is the determinant-trivial subgroup form needed by the normalizer branch
of BG Thm 2.6(a): `O_q(G) ≠ 1` supplies the abelian normal q-subgroup, while
the theorem-level `hchar` hypothesis supplies Maschke's `NeZero` premise. -/
private theorem commutative_of_opCore_ne_bot_of_isAlgClosed_charAway_of_determinantKernel_eq_top
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_top : determinantKernelSubgroup ρ = ⊤)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q G ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  haveI : Finite (Sylow q G) := inferInstance
  rcases exists_nontrivial_normal_commutative_qSubgroup_of_opCore_ne_bot
      (q := q) (G := G) hcore_ne_bot with
    ⟨K, hKnormal, _hKq, hK_ne_bot, hKcomm⟩
  have hKle : K ≤ determinantKernelSubgroup ρ := by
    intro x _hx
    rw [hdet_top]
    trivial
  haveI : NeZero (Nat.card K : F) :=
    neZero_nat_card_cast_of_subgroup_forall_prime_not_char hchar K
  rcases exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
      ρ hdim K hKcomm with
    ⟨W, U, hfreeW, hfreeU, hfiniteW, hfiniteU, hfreeQW, hfreeQU,
      hcompl, hdimW, hdimU, hdimQW, hdimQU⟩
  letI : Module.Free F W.toSubmodule := hfreeW.some
  letI : Module.Free F U.toSubmodule := hfreeU.some
  letI : Module.Finite F W.toSubmodule := hfiniteW.some
  letI : Module.Finite F U.toSubmodule := hfiniteU.some
  letI : Module.Free F (V ⧸ W.toSubmodule) := hfreeQW.some
  letI : Module.Free F (V ⧸ U.toSubmodule) := hfreeQU.some
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne_bot
  obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : K)
  exact commutative_of_determinantKernel_subgroup_rank_one_complement
    ρ hfaithful hodd K hKnormal hKle W U hcompl
    hdimW hdimU hdimQW hdimQU hx_ne_one

/-- If `Q ∈ Syl_q(G)` is nontrivial, then `O_q(N_G(Q))` is nontrivial.

This isolates the group-theoretic part of BG Thm 2.6 where, after choosing
`q ≠ p` and a Sylow `q`-subgroup `Q ≤ G*`, one sets `H = N_{G*}(Q)` and needs
`O_q(H) ≠ 1`. -/
private theorem opCore_ne_bot_of_sylow_normalizer
    {q : ℕ} [Fact q.Prime] {G : Type*} [Group G] [Finite G] [Finite (Sylow q G)]
    (Q : Sylow q G) (hq_dvd : q ∣ Nat.card G) :
    OddOrder.Isaacs.Ch01.opCore q
      (Subgroup.normalizer (Q : Set G)) ≠ ⊥ := by
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let QN : Sylow q N := Q.subtype Q.le_normalizer
  haveI : Finite (Sylow q N) := inferInstance
  haveI : (QN : Subgroup N).Normal := by
    change ((Q : Subgroup G).subgroupOf N).Normal
    exact Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hQ_ne_bot : (Q : Subgroup G) ≠ ⊥ := Q.ne_bot_of_dvd_card hq_dvd
  have hQN_ne_bot : (QN : Subgroup N) ≠ ⊥ := by
    intro hbot
    apply hQ_ne_bot
    have hmap : ((QN : Subgroup N).map N.subtype) = (Q : Subgroup G) := by
      simp only [QN, Sylow.coe_subtype]
      exact Subgroup.map_subgroupOf_eq_of_le Q.le_normalizer
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  exact opCore_ne_bot_of_nontrivial_normal_pSubgroup
    (G := N) (K := (QN : Subgroup N)) QN.2 hQN_ne_bot

/-- q≠p normalizer branch inside the determinant kernel.

For `Q ∈ Syl_q(G*)`, set `H = N_{G*}(Q)`.  Since `H ≤ G*`, the determinant of
the restricted representation on `H` is trivial.  Thus the algebraically
closed q≠p endpoint applies directly to `H` once `O_q(H) ≠ 1`. -/
private theorem determinantKernel_sylow_normalizer_commutative_of_isAlgClosed
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hq_ne_p : q ≠ p)
    (Q : Sylow q (determinantKernelSubgroup ρ))
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q
      (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
        Set (determinantKernelSubgroup ρ))) ≠ ⊥) :
    Std.Commutative
      (· * · :
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let H : Subgroup Gstar := Subgroup.normalizer ((Q : Subgroup Gstar) : Set Gstar)
  let ρH : Representation F H V := ρ.comp (Gstar.subtype.comp H.subtype)
  have hfaithfulH : Function.Injective ρH := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hfaithful (by simpa [ρH] using hxy)
  have hoddH : Odd (Nat.card H) := by
    have hH_dvd_Gstar : Nat.card H ∣ Nat.card Gstar :=
      Subgroup.card_subgroup_dvd_card H
    have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card Gstar
    exact hodd.of_dvd_nat (hH_dvd_Gstar.trans hGstar_dvd_G)
  have hdet_top : determinantKernelSubgroup ρH = ⊤ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rw [mem_determinantKernelSubgroup]
      have hxdetG : (((x : H) : Gstar) : G) ∈ determinantKernelSubgroup ρ :=
        ((x : H) : Gstar).2
      rw [mem_determinantKernelSubgroup] at hxdetG
      simpa [ρH, determinantCharacterOfRepresentation,
        representationToGeneralLinearGroup] using hxdetG
  simpa [H] using
    commutative_of_opCore_ne_bot_of_isAlgClosed_of_determinantKernel_eq_top
      (p := p) (q := q) ρH hfaithfulH hoddH hdim hq_ne_p hdet_top
      hcore_ne_bot

/-- Characteristic-away normalizer branch inside the determinant kernel.

This is the BG Thm 2.6(a) analogue of
`determinantKernel_sylow_normalizer_commutative_of_isAlgClosed`: for
`H = N_{G*}(Q)`, the determinant is trivial on `H`, and the characteristic-away
hypothesis restricts from `G` to `H`. -/
private theorem determinantKernel_sylow_normalizer_commutative_of_isAlgClosed_charAway
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (Q : Sylow q (determinantKernelSubgroup ρ))
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q
      (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
        Set (determinantKernelSubgroup ρ))) ≠ ⊥) :
    Std.Commutative
      (· * · :
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let H : Subgroup Gstar := Subgroup.normalizer ((Q : Subgroup Gstar) : Set Gstar)
  let ρH : Representation F H V := ρ.comp (Gstar.subtype.comp H.subtype)
  have hfaithfulH : Function.Injective ρH := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hfaithful (by simpa [ρH] using hxy)
  have hH_dvd_Gstar : Nat.card H ∣ Nat.card Gstar :=
    Subgroup.card_subgroup_dvd_card H
  have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card Gstar
  have hoddH : Odd (Nat.card H) :=
    hodd.of_dvd_nat (hH_dvd_Gstar.trans hGstar_dvd_G)
  have hcharH :
      ∀ r : ℕ, r.Prime → r ∣ Nat.card H → ¬ CharP F r := by
    intro r hr_prime hr_dvd
    exact hchar r hr_prime (hr_dvd.trans (hH_dvd_Gstar.trans hGstar_dvd_G))
  have hdet_top : determinantKernelSubgroup ρH = ⊤ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rw [mem_determinantKernelSubgroup]
      have hxdetG : (((x : H) : Gstar) : G) ∈ determinantKernelSubgroup ρ :=
        ((x : H) : Gstar).2
      rw [mem_determinantKernelSubgroup] at hxdetG
      simpa [ρH, determinantCharacterOfRepresentation,
        representationToGeneralLinearGroup] using hxdetG
  simpa [H] using
    commutative_of_opCore_ne_bot_of_isAlgClosed_charAway_of_determinantKernel_eq_top
      (q := q) ρH hfaithfulH hoddH hdim hcharH hdet_top hcore_ne_bot

/-- A finite group that is not a `p`-group has a prime divisor different from `p`.

This is the arithmetic half of the `G*` dichotomy in BG Thm 2.6. -/
private theorem exists_prime_ne_dvd_card_of_not_isPGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hnot_pgroup : ¬ IsPGroup p G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ Nat.card G := by
  by_contra hnone
  apply hnot_pgroup
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card G).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro q hq_prime hq_dvd
  by_contra hq_ne_p
  exact hnone ⟨q, hq_prime, hq_ne_p, hq_dvd⟩

/-- If a finite group is not a `p`-group, one can choose `q ≠ p` and
`Q ∈ Syl_q(G)` with nontrivial `O_q(N_G(Q))`.

This packages the first two group-theoretic moves in the `q ≠ p` branch of
BG Thm 2.6 before the Burnside normal-complement/induction step. -/
private theorem exists_prime_ne_sylow_normalizer_opCore_ne_bot_of_not_isPGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hnot_pgroup : ¬ IsPGroup p G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ Nat.card G ∧ ∃ Q : Sylow q G,
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer (Q : Set G)) ≠ ⊥ := by
  rcases exists_prime_ne_dvd_card_of_not_isPGroup (p := p) (G := G) hnot_pgroup with
    ⟨q, hq_prime, hq_ne_p, hq_dvd⟩
  haveI : Fact q.Prime := ⟨hq_prime⟩
  haveI : Finite (Sylow q G) := inferInstance
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  exact ⟨q, hq_prime, hq_ne_p, hq_dvd, Q,
    opCore_ne_bot_of_sylow_normalizer Q hq_dvd⟩

/-- Burnside bridge for BG Thm 2.6: an abelian Sylow normalizer gives a normal
`p`-complement.

BG phrases the step as "`H = N_G(Q)` is abelian, so by Burnside ..."; Ch.5's
formal entry point expects `N_G(Q) ≤ C_G(Q)`. -/
private theorem hasNormalPComplement_of_sylow_normalizer_commutative
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (Q : Sylow p G)
    (hN_comm : Std.Commutative
      (· * · : Subgroup.normalizer (Q : Set G) →
        Subgroup.normalizer (Q : Set G) →
        Subgroup.normalizer (Q : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer
    Q ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (congr_arg Subtype.val
    (hN_comm.comm ⟨x, hx⟩ ⟨y, Q.le_normalizer hy⟩)).symm

/-- Burnside normal-complement branch for BG Thm 2.6.

If `G` has a normal `p`-complement and `p ∣ |G|`, then either the complement is
trivial, giving `O_p(G) ≠ 1`, or the induction result on the nontrivial normal
complement lifts back to `G`.  The hypothesis `hind` is exactly the induction
output used in the text for `N ≠ 1`. -/
private theorem exists_prime_opCore_ne_bot_of_hasNormalPComplement_induction
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    (hp_dvd : p ∣ Nat.card G)
    (hcomp : OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hind : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  rcases hcomp with ⟨N, hNnormal, hNcompl⟩
  by_cases hN_bot : N = ⊥
  · obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hPtop : (P : Subgroup G) = ⊤ := by
      simpa [hN_bot] using hNcompl P
    haveI : (P : Subgroup G).Normal := by
      rw [hPtop]
      infer_instance
    exact ⟨p, Fact.out,
      opCore_ne_bot_of_nontrivial_normal_pSubgroup
        (G := G) (K := (P : Subgroup G)) P.2
        (P.ne_bot_of_dvd_card hp_dvd)⟩
  · haveI : N.Normal := hNnormal
    have hN_ne_top : N ≠ ⊤ := by
      intro hN_top
      obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
      have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hp_dvd
      apply hP_ne_bot
      refine le_bot_iff.mp ?_
      have hP_le_N : (P : Subgroup G) ≤ N := by
        rw [hN_top]
        exact le_top
      have hP_le_inf : (P : Subgroup G) ≤ N ⊓ (P : Subgroup G) :=
        le_inf hP_le_N le_rfl
      simpa [(hNcompl P).isCompl.inf_eq_bot] using hP_le_inf
    rcases hind N hNnormal hN_bot hN_ne_top with ⟨r, hr_prime, hNcore_ne_bot⟩
    haveI : Fact r.Prime := ⟨hr_prime⟩
    haveI : Finite (Sylow r G) := inferInstance
    exact ⟨r, hr_prime,
      opCore_ne_bot_of_normal_subgroup_opCore_ne_bot
        (p := r) (G := G) N hNcore_ne_bot⟩

/-- BG Thm 2.6 step 5 as a group-theoretic spine.

When `G` is not a `p`-group, choose `q ≠ p` and `Q ∈ Syl_q(G)`, use the
previous `O_q(N_G(Q)) ≠ 1` branch to make `N_G(Q)` abelian, apply Burnside, and
then return the normal-complement induction output to `G`. -/
private theorem exists_prime_opCore_ne_bot_of_not_isPGroup_via_normalizers
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hnot_pgroup : ¬ IsPGroup p G)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p → (Q : Sylow q G) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer (Q : Set G)) ≠ ⊥ →
      Std.Commutative
        (· * · : Subgroup.normalizer (Q : Set G) →
          Subgroup.normalizer (Q : Set G) →
          Subgroup.normalizer (Q : Set G)))
    (hind : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  rcases exists_prime_ne_sylow_normalizer_opCore_ne_bot_of_not_isPGroup
      (p := p) (G := G) hnot_pgroup with
    ⟨q, hq_prime, hq_ne_p, hq_dvd, Q, hQcore_ne_bot⟩
  haveI : Fact q.Prime := ⟨hq_prime⟩
  haveI : Finite (Sylow q G) := inferInstance
  have hcomp : OddOrder.Isaacs.Ch05.HasNormalPComplement q G :=
    hasNormalPComplement_of_sylow_normalizer_commutative
      Q (hnormalizer hq_ne_p Q hQcore_ne_bot)
  exact exists_prime_opCore_ne_bot_of_hasNormalPComplement_induction
    (p := q) (G := G) hq_dvd hcomp hind

/-- BG Thm 2.6 step 5 specialized to the determinant kernel `G*`.

If `G*` is nontrivial, then either it is a `p`-group, giving
`O_p(G*) ≠ 1`, or the non-`p`-group normalizer spine supplies a prime `r` with
`O_r(G*) ≠ 1`.  The two hypotheses are precisely the remaining theorem-level
inputs from the text: the q≠p linear-algebra normalizer step and the induction
output on normal complements. -/
private theorem exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧
      OddOrder.Isaacs.Ch01.opCore r (determinantKernelSubgroup ρ) ≠ ⊥ := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  have hGstar_ne_bot : Gstar ≠ ⊥ := by
    simpa [Gstar] using hdet_ne_bot
  by_cases hGstar_p : IsPGroup p Gstar
  · haveI : Finite (Sylow p Gstar) := inferInstance
    haveI : Nontrivial Gstar :=
      (Subgroup.nontrivial_iff_ne_bot Gstar).mpr hGstar_ne_bot
    exact ⟨p, Fact.out,
      opCore_ne_bot_of_nontrivial_normal_pSubgroup
        (G := Gstar) (K := (⊤ : Subgroup Gstar))
        (hGstar_p.to_subgroup ⊤) top_ne_bot⟩
  · exact exists_prime_opCore_ne_bot_of_not_isPGroup_via_normalizers
      (p := p) (G := Gstar) hGstar_p
      (fun {q} hq_prime hq_ne_p Q hQcore =>
        hnormalizer (q := q) hq_ne_p Q hQcore)
      hind

/-- Characteristic-away determinant-kernel core spine.

This is the BG Thm 2.6(a) version of
`exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot`: since there is no
distinguished field characteristic prime, we choose any prime divisor of
`|G*|` and reuse the p-parametrized normalizer spine. -/
private theorem exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot_charAway
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime],
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧
      OddOrder.Isaacs.Ch01.opCore r (determinantKernelSubgroup ρ) ≠ ⊥ := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  have hGstar_ne_bot : Gstar ≠ ⊥ := by
    simpa [Gstar] using hdet_ne_bot
  haveI : Nontrivial Gstar :=
    (Subgroup.nontrivial_iff_ne_bot Gstar).mpr hGstar_ne_bot
  obtain ⟨p, hp_prime, _hp_dvd⟩ :=
    Nat.exists_prime_and_dvd (Finite.one_lt_card (α := Gstar)).ne'
  haveI : Fact p.Prime := ⟨hp_prime⟩
  exact exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot
    (p := p) ρ hdet_ne_bot
    (fun {q} _hq_prime _hq_ne_p Q hQcore =>
      hnormalizer (q := q) Q hQcore)
    hind

/-- q = p endpoint when `O_p(G*)` is nontrivial.

Here `G* = ker(det ∘ ρ)`.  The Ch.1 `opCore` is characteristic in `G*`; since
`G* ⊴ G`, its image in `G` is a nontrivial normal p-subgroup and can be fed to
the fixed-space reduction. -/
private theorem sylow_commutative_and_commutator_le_of_determinantKernel_opCore_ne_bot
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hop_ne_bot : OddOrder.Isaacs.Ch01.opCore p (determinantKernelSubgroup ρ) ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  haveI : Gstar.Normal := by
    dsimp [Gstar]
    exact determinantKernelSubgroup_normal ρ
  have hGcore_ne_bot : OddOrder.Isaacs.Ch01.opCore p G ≠ ⊥ :=
    opCore_ne_bot_of_normal_subgroup_opCore_ne_bot
      (p := p) (G := G) Gstar hop_ne_bot
  exact sylow_commutative_and_commutator_le_of_exists_nontrivial_normal_pSubgroup
    ρ hfaithful hdim
    ⟨OddOrder.Isaacs.Ch01.opCore p G, inferInstance,
      OddOrder.Isaacs.Ch01.opCore_isPGroup p G, hGcore_ne_bot⟩ P

/-- Determinant-kernel core dispatch for the Sylow conclusion of BG Thm 2.6(b).

Once the group-theoretic spine has produced a nontrivial prime core in `G*`,
the `r = p` branch feeds the fixed-space endpoint.  The only remaining
theorem-specific input for `r ≠ p` is the linear-algebra branch from the text:
a nontrivial `q`-core in `G*`, with `q ≠ p`, makes the ambient group abelian. -/
private theorem sylow_commutative_and_commutator_le_of_determinantKernel_core_spine
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (hcore_ne_p_comm : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥ →
      Std.Commutative (· * · : G → G → G))
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  rcases exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot
      (p := p) ρ hdet_ne_bot hnormalizer hind with
    ⟨r, hr_prime, hcore_ne_bot⟩
  by_cases hr_eq_p : r = p
  · subst r
    exact sylow_commutative_and_commutator_le_of_determinantKernel_opCore_ne_bot
      ρ hfaithful hdim hcore_ne_bot P
  · haveI : Fact r.Prime := ⟨hr_prime⟩
    exact sylow_commutative_and_commutator_le_of_commutative
      (hcore_ne_p_comm (q := r) hr_eq_p hcore_ne_bot) P

/-- Theorem-facing determinant-kernel reduction for BG Thm 2.6(b).

This packages the current end of the q = p route.  If `G* = 1`, the determinant
character makes `G` abelian.  If `G* ≠ 1`, the group-theoretic core spine
produces a nontrivial prime core in `G*`; the `p`-core branch feeds the
fixed-space Sylow endpoint, while every `q ≠ p` core is discharged by the
rank-one line-pair construction.  The remaining inputs are exactly the
normalizer/induction spine and the line-pair construction. -/
private theorem
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_rankOneLinePair
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)] [MulAction G (Fin 2)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (hline : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ K : Subgroup G, K.Normal → K ≤ determinantKernelSubgroup ρ →
        IsPGroup q K → K ≠ ⊥ → Std.Commutative (· * · : K → K → K) →
        RankOneLinePairData ρ)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  by_cases hdet_bot : determinantKernelSubgroup ρ = ⊥
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot
      ρ hdet_bot P
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_core_spine
      ρ hfaithful hdim hdet_bot hnormalizer hind
      (fun {q} hq_prime hq_ne_p hcore_ne_bot =>
        commutative_of_determinantKernel_opCore_ne_bot_of_rankOneLinePair
          ρ hfaithful hodd hcore_ne_bot (hline (q := q) hq_ne_p))
      P

/-- Theorem-facing determinant-kernel reduction using `K`-submodule data.

This is the successor of
`sylow_commutative_and_commutator_le_of_determinantKernel_spine_rankOneLinePair`
after the q≠p branch has been moved below the permutation-action interface:
the only remaining linear-algebra input is the pair of complementary rank-one
`K`-submodules for every nontrivial `q`-core in `G*`. -/
private theorem
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_rankOneKSubmodules
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (hline : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ K : Subgroup G, K.Normal → K ≤ determinantKernelSubgroup ρ →
        IsPGroup q K → K ≠ ⊥ → Std.Commutative (· * · : K → K → K) →
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
          Module.finrank F (V ⧸ U.toSubmodule) = 1)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  by_cases hdet_bot : determinantKernelSubgroup ρ = ⊥
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot
      ρ hdet_bot P
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_core_spine
      ρ hfaithful hdim hdet_bot hnormalizer hind
      (fun {q} _hq_prime hq_ne_p hcore_ne_bot =>
        commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules
          ρ hfaithful hodd hcore_ne_bot (hline (q := q) hq_ne_p))
      P

/-- Algebraically closed determinant-kernel spine for BG Thm 2.6(b).

Over an algebraically closed field, the q≠p Maschke branch supplies the
rank-one `K`-submodule input directly.  What remains outside this bridge is
the group-theoretic normalizer/induction spine inside `G*`. -/
private theorem
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) :=
  sylow_commutative_and_commutator_le_of_determinantKernel_spine_rankOneKSubmodules
    ρ hfaithful hodd hdim hnormalizer hind
    (fun {q} _hq_prime hq_ne_p K _hKnormal _hKle hKq _hK_ne_bot hKcomm =>
      exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
        (p := p) (q := q) ρ hdim K hKq hq_ne_p hKcomm)
    P

/-- Algebraically closed determinant-kernel spine with the normalizer branch closed.

The q≠p normalizer step is now supplied by restricting the representation to
`H = N_{G*}(Q)`, where the determinant is trivial because `H ≤ G*`.  The only
remaining theorem-level input in this algebraically closed reduction is the
induction output on nontrivial normal subgroups of `G*`. -/
private theorem
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) :=
  sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed
    ρ hfaithful hodd hdim
    (fun {q} _hq_prime hq_ne_p Q hQcore =>
      determinantKernel_sylow_normalizer_commutative_of_isAlgClosed
        (q := q) ρ hfaithful hodd hdim hq_ne_p Q hQcore)
    hind P

/-! ### Base change toward the algebraically closed reduction -/

/-- Scalar extension preserves the determinant kernel.

This is the determinant compatibility needed to move the BG Thm 2.6(b) spine to
an algebraic closure: the base-changed determinant is the algebra-map image of
the original determinant, and field extensions have injective algebra maps. -/
private theorem determinantKernelSubgroup_baseChangeRepresentation
    {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) :
    determinantKernelSubgroup (baseChangeRepresentation K ρ) =
      determinantKernelSubgroup ρ := by
  ext g
  rw [mem_determinantKernelSubgroup, mem_determinantKernelSubgroup]
  constructor
  · intro hg
    apply Units.ext
    apply (algebraMap F K).injective
    have hdetF :
        ((determinantCharacterOfRepresentation ρ g : F) =
          LinearMap.det (ρ g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hdetK :
        ((determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) =
          LinearMap.det ((baseChangeRepresentation K ρ) g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hgK :
        ((determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) =
          1) := by
      simpa using congrArg Units.val hg
    calc
      algebraMap F K ((determinantCharacterOfRepresentation ρ g : F))
          = algebraMap F K (LinearMap.det (ρ g)) := by rw [hdetF]
      _ = LinearMap.det ((ρ g).baseChange K) := by rw [LinearMap.det_baseChange]
      _ = LinearMap.det ((baseChangeRepresentation K ρ) g) := rfl
      _ = (determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) :=
        hdetK.symm
      _ = 1 := hgK
      _ = algebraMap F K (1 : F) := by simp
  · intro hg
    apply Units.ext
    have hdetF :
        ((determinantCharacterOfRepresentation ρ g : F) =
          LinearMap.det (ρ g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hdetK :
        ((determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) =
          LinearMap.det ((baseChangeRepresentation K ρ) g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hgF : ((determinantCharacterOfRepresentation ρ g : F) = 1) := by
      simpa using congrArg Units.val hg
    calc
      (determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K)
          = LinearMap.det ((baseChangeRepresentation K ρ) g) := hdetK
      _ = LinearMap.det ((ρ g).baseChange K) := rfl
      _ = algebraMap F K (LinearMap.det (ρ g)) := by rw [LinearMap.det_baseChange]
      _ = algebraMap F K ((determinantCharacterOfRepresentation ρ g : F)) := by rw [hdetF]
      _ = 1 := by simp [hgF]

/-- A prime characteristic on the algebraic closure descends to the base field. -/
private theorem not_charP_algebraicClosure_of_not_charP
    {F : Type*} [Field F] {q : ℕ} (hchar : ¬ CharP F q) :
    ¬ CharP (AlgebraicClosure F) q := by
  intro hq
  exact hchar ((Algebra.charP_iff F (AlgebraicClosure F) q).mpr hq)

/-- The BG Thm 2.6(a) characteristic-away hypothesis survives algebraic closure. -/
private theorem charAway_algebraicClosure
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP (AlgebraicClosure F) q :=
  fun q hq_prime hq_dvd =>
    not_charP_algebraicClosure_of_not_charP (hchar q hq_prime hq_dvd)

/-- Algebraic-closure reduction for the characteristic-away determinant-core
endpoint.

This transports BG Thm 2.6(a)'s linear-algebra branch to `AlgebraicClosure F`
while keeping the determinant kernel, hence the nontrivial `O_q(G*)`, unchanged. -/
private theorem commutative_of_determinantKernel_opCore_ne_bot_of_algebraicClosure_charAway
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  let ρK : Representation (AlgebraicClosure F) G
      (TensorProduct F (AlgebraicClosure F) V) :=
    baseChangeRepresentation (AlgebraicClosure F) ρ
  have hfaithfulK : Function.Injective ρK := by
    simpa [ρK] using
      baseChangeRepresentation_faithful (AlgebraicClosure F) ρ hfaithful
  have hdimK :
      Module.finrank (AlgebraicClosure F)
        (TensorProduct F (AlgebraicClosure F) V) = 2 := by
    exact
      (Module.finrank_baseChange (R := AlgebraicClosure F) (S := F) (M' := V)).trans hdim
  have hcoreK :
      OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρK) ≠ ⊥ := by
    change
      OddOrder.Isaacs.Ch01.opCore q
          (determinantKernelSubgroup (baseChangeRepresentation (AlgebraicClosure F) ρ)) ≠
        ⊥
    rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
    exact hcore_ne_bot
  exact
    commutative_of_determinantKernel_opCore_ne_bot_of_isAlgClosed_charAway
      ρK hfaithfulK hodd hdimK (charAway_algebraicClosure hchar) hcoreK

/-- Characteristic-away dispatch once the determinant-kernel core spine has
produced a nontrivial prime core.

The resulting `O_r(G*) ≠ 1` is sent to the algebraic-closure Maschke endpoint,
which returns commutativity of the original group. -/
private theorem commutative_of_determinantKernel_core_spine_charAway
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime],
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  rcases exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot_charAway
      ρ hdet_ne_bot hnormalizer hind with
    ⟨r, hr_prime, hcore_ne_bot⟩
  haveI : Fact r.Prime := ⟨hr_prime⟩
  exact commutative_of_determinantKernel_opCore_ne_bot_of_algebraicClosure_charAway
    ρ hfaithful hodd hdim hchar hcore_ne_bot

/-- Algebraically closed characteristic-away determinant-kernel spine with the
normalizer branch closed.

The normalizer step is supplied by restricting the representation to
`N_{G*}(Q)`, where the determinant is trivial.  The remaining input is only the
proper-normal-subgroup induction output inside `G*`. -/
private theorem commutative_of_determinantKernel_core_spine_isAlgClosed_charAway
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_determinantKernel_core_spine_charAway
    ρ hfaithful hodd hdim hchar hdet_ne_bot
    (fun {q} _hq_prime Q hQcore =>
      determinantKernel_sylow_normalizer_commutative_of_isAlgClosed_charAway
        (q := q) ρ hfaithful hodd hdim hchar Q hQcore)
    hind

/-- Algebraic-closure reduction for the characteristic-away determinant-kernel
spine, with the induction hypothesis stated on the original determinant kernel.

This is the theorem-facing bridge for BG Thm 2.6(a): scalar extension preserves
faithfulness, dimension, and the determinant kernel, so the algebraically closed
normalizer branch can be used without changing the group-theoretic spine. -/
private theorem commutative_of_determinantKernel_core_spine_algebraicClosure_charAway
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  let ρK : Representation (AlgebraicClosure F) G
      (TensorProduct F (AlgebraicClosure F) V) :=
    baseChangeRepresentation (AlgebraicClosure F) ρ
  have hfaithfulK : Function.Injective ρK := by
    simpa [ρK] using
      baseChangeRepresentation_faithful (AlgebraicClosure F) ρ hfaithful
  have hdimK :
      Module.finrank (AlgebraicClosure F)
        (TensorProduct F (AlgebraicClosure F) V) = 2 := by
    exact
      (Module.finrank_baseChange (R := AlgebraicClosure F) (S := F) (M' := V)).trans hdim
  have hdetK_ne_bot : determinantKernelSubgroup ρK ≠ ⊥ := by
    change
      determinantKernelSubgroup (baseChangeRepresentation (AlgebraicClosure F) ρ) ≠ ⊥
    rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
    exact hdet_ne_bot
  have hindK :
      ∀ N : Subgroup (determinantKernelSubgroup ρK),
        N.Normal → N ≠ ⊥ → N ≠ ⊤ →
          ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥ := by
    change
      ∀ N : Subgroup
          (determinantKernelSubgroup
            (baseChangeRepresentation (AlgebraicClosure F) ρ)),
        N.Normal → N ≠ ⊥ → N ≠ ⊤ →
          ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥
    rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
    exact hind
  exact
    commutative_of_determinantKernel_core_spine_isAlgClosed_charAway
      ρK hfaithfulK hodd hdimK (charAway_algebraicClosure hchar)
      hdetK_ne_bot hindK

/-- Algebraic-closure reduction for the current BG Thm 2.6(b) spine.

This keeps the remaining induction hypothesis explicit but moves the field
from `F` to `AlgebraicClosure F`, where the q≠p Maschke/eigenline branch is
available.  The content is the faithful scalar-extension and dimension
transport, not a theorem rename. -/
private theorem
    sylow_commutative_and_commutator_le_of_algebraicClosure_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hind :
      ∀ N : Subgroup
          (determinantKernelSubgroup
            (baseChangeRepresentation (AlgebraicClosure F) ρ)),
        N.Normal → N ≠ ⊥ → N ≠ ⊤ →
        ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  let ρK : Representation (AlgebraicClosure F) G
      (TensorProduct F (AlgebraicClosure F) V) :=
    baseChangeRepresentation (AlgebraicClosure F) ρ
  have hfaithfulK : Function.Injective ρK := by
    simpa [ρK] using
      baseChangeRepresentation_faithful (AlgebraicClosure F) ρ hfaithful
  have hdimK :
      Module.finrank (AlgebraicClosure F)
        (TensorProduct F (AlgebraicClosure F) V) = 2 := by
    exact
      (Module.finrank_baseChange (R := AlgebraicClosure F) (S := F) (M' := V)).trans hdim
  exact
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed_induction
      ρK hfaithfulK hodd hdimK hind P

/-- Algebraic-closure reduction with the induction hypothesis stated on the
original determinant kernel.

The preceding determinant-kernel compatibility identifies the determinant
kernel after scalar extension with the original `G*`, so the theorem-facing
induction hypothesis no longer has to mention the base-changed representation. -/
private theorem
    sylow_commutative_and_commutator_le_of_algebraicClosure_original_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ →
        ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  refine
    sylow_commutative_and_commutator_le_of_algebraicClosure_induction
      ρ hfaithful hodd hdim ?_ P
  rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
  exact hind

/-- q = p determinant-kernel split packaged as a theorem-facing reduction. -/
private theorem sylow_commutative_and_commutator_le_of_determinantKernel_bot_or_pGroup
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hcase : determinantKernelSubgroup ρ = ⊥ ∨
      IsPGroup p (determinantKernelSubgroup ρ) ∧ determinantKernelSubgroup ρ ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  rcases hcase with hbot | ⟨hdet_p, hdet_ne_bot⟩
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot ρ hbot P
  · exact sylow_commutative_and_commutator_le_of_nontrivial_determinantKernel_pGroup
      ρ hfaithful hdim hdet_p hdet_ne_bot P

/-- Special case of the q = p endpoint when the ambient group itself is a
p-group. -/
private theorem sylow_commutative_and_commutator_le_of_isPGroup
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hG : IsPGroup p G) (hp_dvd : p ∣ Nat.card G)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) :=
  sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space
    (⊤ : Subgroup G) ρ hfaithful (hG.to_subgroup ⊤) hdim
    (top_ne_bot_of_prime_dvd_card (p := p) hp_dvd) P

/-- BG Thm 2.6(b) with the proper-subgroup induction outputs supplied
explicitly.

This is the theorem-facing endpoint for the remaining `G* ≠ 1` and
`G*` non-`p`-group branch.  The hypotheses `hab_ind` and `hsyl_ind` are exactly
the strong-induction outputs for proper normal subgroups of the determinant
kernel, phrased on the restricted faithful representation. -/
private theorem odd_two_dim_sylow_abelian_of_determinantKernel_induction_outputs
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hab_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 →
        (∀ q : ℕ, q.Prime → q ∣ Nat.card N → ¬ CharP F q) →
        Std.Commutative (· * · : N → N → N))
    (hsyl_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 → p ∣ Nat.card N → (P : Sylow p N) →
        Std.Commutative (· * · : P → P → P) ∧
          commutator N ≤ (P : Subgroup N))
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  by_cases hdet_bot : determinantKernelSubgroup ρ = ⊥
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot
      ρ hdet_bot P
  by_cases hdet_p : IsPGroup p (determinantKernelSubgroup ρ)
  · exact sylow_commutative_and_commutator_le_of_nontrivial_determinantKernel_pGroup
      ρ hfaithful hdim hdet_p hdet_bot P
  exact
    sylow_commutative_and_commutator_le_of_algebraicClosure_original_induction
      ρ hfaithful hodd hdim
      (determinantKernel_hind_of_odd_two_dim_induction_outputs
        ρ hfaithful hodd hdim hab_ind hsyl_ind) P

/-- Finite subgroup cardinality strictly drops for a proper subgroup. -/
private lemma subgroup_card_lt_of_lt_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H < ⊤) :
    Nat.card H < Nat.card G := by
  have h_dvd : Nat.card H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le : Nat.card H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne : Nat.card H ≠ Nat.card G := fun heq =>
    hH.ne (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le h_ne

/-- Strong-induction form of BG Thm 2.6(a).

The determinant-kernel branch uses the characteristic-away core spine.  Proper
normal subgroups of `G*` are handled by the induction hypothesis and then
converted into a nontrivial prime core. -/
private theorem odd_two_dim_abelian_strong_induction
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G],
      Nat.card G = n → Odd (Nat.card G) → Module.finrank F V = 2 →
      (ρ : Representation F G V) → Function.Injective ρ →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) →
      Std.Commutative (· * · : G → G → G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard hodd hdim ρ hfaithful hchar
    by_cases hdet_bot : determinantKernelSubgroup ρ = ⊥
    · exact commutative_of_determinantKernel_eq_bot ρ hdet_bot
    · refine
        commutative_of_determinantKernel_core_spine_algebraicClosure_charAway
          ρ hfaithful hodd hdim hchar hdet_bot ?_
      intro N hNnormal hN_ne_bot hN_ne_top
      let Gstar : Subgroup G := determinantKernelSubgroup ρ
      let ρN : Representation F N V := ρ.comp (Gstar.subtype.comp N.subtype)
      haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne_bot
      have hfaithfulN : Function.Injective ρN := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact hfaithful (by simpa [ρN, Gstar] using hxy)
      have hN_dvd_Gstar : Nat.card N ∣ Nat.card Gstar :=
        Subgroup.card_subgroup_dvd_card N
      have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card Gstar
      have hoddN : Odd (Nat.card N) :=
        hodd.of_dvd_nat (hN_dvd_Gstar.trans hGstar_dvd_G)
      have hcharN :
          ∀ q : ℕ, q.Prime → q ∣ Nat.card N → ¬ CharP F q := by
        intro q hq_prime hq_dvd
        exact hchar q hq_prime (hq_dvd.trans (hN_dvd_Gstar.trans hGstar_dvd_G))
      have hN_card_lt_Gstar : Nat.card N < Nat.card Gstar := by
        have hN_lt_top : N < ⊤ := lt_top_iff_ne_top.mpr hN_ne_top
        exact subgroup_card_lt_of_lt_top hN_lt_top
      have hGstar_card_le_G : Nat.card Gstar ≤ Nat.card G :=
        Subgroup.card_le_card_group Gstar
      have hN_card_lt_G : Nat.card N < Nat.card G :=
        lt_of_lt_of_le hN_card_lt_Gstar hGstar_card_le_G
      have hNcomm : Std.Commutative (· * · : N → N → N) :=
        ih (Nat.card N) (by simpa [hcard] using hN_card_lt_G)
          (G := N) rfl hoddN hdim ρN hfaithfulN hcharN
      exact exists_prime_opCore_ne_bot_of_commutative hNcomm

/-- **BG Theorem 2.6 (a)**: 奇数位数の有限群 `G` が体 `F` 上 2 次元の
faithful 表現を持ち, char `F` が `|G|` を割らないなら, `G` は abelian. -/
theorem odd_two_dim_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) :
    Std.Commutative (· * · : G → G → G) :=
  odd_two_dim_abelian_strong_induction
    (F := F) (V := V) (Nat.card G) (G := G) rfl hodd hdim ρ hfaithful hchar

/-- Strong-induction form of BG Thm 2.6(b), using Thm 2.6(a) for the
characteristic-away branch on proper subgroups.

This is not the final theorem (a) proof; it isolates the remaining dependency of
the q=p theorem on the abelian branch and supplies the proper-subgroup Sylow
branch recursively. -/
private theorem odd_two_dim_sylow_abelian_strong_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)],
      Nat.card G = n → Odd (Nat.card G) → Module.finrank F V = 2 →
      (ρ : Representation F G V) → Function.Injective ρ →
      p ∣ Nat.card G → (P : Sylow p G) →
      Std.Commutative (· * · : P → P → P) ∧
        commutator G ≤ (P : Subgroup G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hcard hodd hdim ρ hfaithful hp_dvd P
    refine
      odd_two_dim_sylow_abelian_of_determinantKernel_induction_outputs
        (p := p) (F := F) (G := G) hodd hdim ρ hfaithful ?_ ?_ P
    · intro N _hNnormal _hN_ne_bot _hN_ne_top hoddN σ hfaithfulN hdimN hcharN
      exact odd_two_dim_abelian hoddN hdimN σ hfaithfulN hcharN
    · intro N _hNnormal _hN_ne_bot hN_ne_top hoddN σ hfaithfulN hdimN hpN PN
      let Gstar : Subgroup G := determinantKernelSubgroup ρ
      have hN_card_lt_Gstar : Nat.card N < Nat.card Gstar := by
        have hN_lt_top : N < ⊤ := lt_top_iff_ne_top.mpr hN_ne_top
        exact subgroup_card_lt_of_lt_top hN_lt_top
      have hGstar_card_le_G : Nat.card Gstar ≤ Nat.card G :=
        Subgroup.card_le_card_group Gstar
      have hN_card_lt_G : Nat.card N < Nat.card G :=
        lt_of_lt_of_le hN_card_lt_Gstar hGstar_card_le_G
      exact ih (Nat.card N) (by simpa [hcard] using hN_card_lt_G)
        (G := N) rfl hoddN hdimN σ hfaithfulN hpN PN

/-- **BG Theorem 2.6 (b)**: 奇数位数の有限群 `G` が体 `F` 上 2 次元の
faithful 表現を持ち, char `F = p` が `|G|` を割るなら, `G` の `p`-Sylow
は abelian かつ `G'` を含む.

stub: 詳細 proof は §2F section docstring の "證明梗概" + Case q = p
(BG L785-787) 参照. -/
theorem odd_two_dim_sylow_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    (hchar : CharP F p) (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  haveI : CharP F p := hchar
  exact
    odd_two_dim_sylow_abelian_strong_induction
      (p := p) (F := F) (V := V) (Nat.card G)
      (G := G) rfl hodd hdim ρ hfaithful hp_dvd P

end OddOrder.BG.Ch1.S02
