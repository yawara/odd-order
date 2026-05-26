/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Submodule
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Determinant
import OddOrder.GroupTheory.IsExtraspecial
import OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector
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

**Lean status** (2026-05-25): `PGroupFixedVector` shared module の
`IsPGroup.invariants_ne_bot` / `exists_fixed_vector_ne_zero` は sorry-free.
([OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean]
(../../GroupTheory/RepresentationTheory/PGroupFixedVector.lean)).
本節 Thm 2.6 (a)(b) は Lean signature 確定済み, sorry 付き stub.
残: (i) 帰納 + GL(2,F) 計算 + MISSING_PAGE:29 補完, (ii) `hchar` 引数の
mathlib との型整合 (`CharP F p` vs `(ringChar F).Prime`) 確認.
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
    simpa [hcard] using orderOf_dvd_natCard σ
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
  have hGcomm := commutative_of_determinantKernel_eq_bot ρ hdet
  constructor
  · constructor
    intro x y
    exact Subtype.ext (hGcomm.comm x y)
  · intro g hg
    have hgdet := commutator_le_determinantKernelSubgroup ρ hg
    rw [hdet] at hgdet
    have hg_one : g = 1 := by simpa using hgdet
    simp [hg_one]

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

/-- If `Q ∈ Syl_q(G)` is nontrivial, then `O_q(N_G(Q))` is nontrivial.

This isolates the group-theoretic part of BG Thm 2.6 where, after choosing
`q ≠ p` and a Sylow `q`-subgroup `Q ≤ G*`, one sets `H = N_{G*}(Q)` and needs
`O_q(H) ≠ 1`. -/
private theorem opCore_ne_bot_of_sylow_normalizer
    {q : ℕ} [Fact q.Prime] {G : Type*} [Group G] [Finite G] [Finite (Sylow q G)]
    (Q : Sylow q G) (hq_dvd : q ∣ Nat.card G) :
    OddOrder.Isaacs.Ch01.opCore q
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) ≠ ⊥ := by
  let N : Subgroup G := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  let QN : Sylow q N := Q.subtype Q.le_normalizer
  haveI : Finite (Sylow q N) := inferInstance
  haveI : (QN : Subgroup N).Normal := by
    change ((Q : Subgroup G).subgroupOf N).Normal
    infer_instance
  have hQ_ne_bot : (Q : Subgroup G) ≠ ⊥ := Q.ne_bot_of_dvd_card hq_dvd
  have hQN_ne_bot : (QN : Subgroup N) ≠ ⊥ := by
    intro hbot
    apply hQ_ne_bot
    have hmap :
        ((QN : Subgroup N).map N.subtype) = (⊥ : Subgroup N).map N.subtype := by
      rw [hbot]
    simpa [QN, N, Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le Q.le_normalizer] using hmap
  exact opCore_ne_bot_of_nontrivial_normal_pSubgroup
    (G := N) (K := (QN : Subgroup N)) QN.2 hQN_ne_bot

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
        (Subgroup.normalizer ((Q : Subgroup G) : Set G)) ≠ ⊥ := by
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
      (· * · : Subgroup.normalizer ((Q : Subgroup G) : Set G) →
        Subgroup.normalizer ((Q : Subgroup G) : Set G) →
        Subgroup.normalizer ((Q : Subgroup G) : Set G))) :
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
    (hind : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ →
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
    rcases hind N hNnormal hN_bot with ⟨r, hr_prime, hNcore_ne_bot⟩
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
        (Subgroup.normalizer ((Q : Subgroup G) : Set G)) ≠ ⊥ →
      Std.Commutative
        (· * · : Subgroup.normalizer ((Q : Subgroup G) : Set G) →
          Subgroup.normalizer ((Q : Subgroup G) : Set G) →
          Subgroup.normalizer ((Q : Subgroup G) : Set G)))
    (hind : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ →
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
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ →
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

/-- **BG Theorem 2.6 (a)**: 奇数位数の有限群 `G` が体 `F` 上 2 次元の
faithful 表現を持ち, char `F` が `|G|` を割らないなら, `G` は abelian.

stub: 詳細 proof は §2F section docstring の "證明梗概" 参照. -/
theorem odd_two_dim_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (_hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (_hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (_hfaithful : Function.Injective ρ)
    (_hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) :
    Std.Commutative (· * · : G → G → G) := by
  sorry

/-- **BG Theorem 2.6 (b)**: 奇数位数の有限群 `G` が体 `F` 上 2 次元の
faithful 表現を持ち, char `F = p` が `|G|` を割るなら, `G` の `p`-Sylow
は abelian かつ `G'` を含む.

stub: 詳細 proof は §2F section docstring の "證明梗概" + Case q = p
(BG L785-787) 参照. -/
theorem odd_two_dim_sylow_abelian
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (_hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (_hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (_hfaithful : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (_hp_dvd : p ∣ Nat.card G)
    (_hchar : CharP F p) (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  sorry

end OddOrder.BG.Ch1.S02
