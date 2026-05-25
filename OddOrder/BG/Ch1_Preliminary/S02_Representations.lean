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
import OddOrder.GroupTheory.IsExtraspecial
import OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector

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

**証明梗概** (BG L779-793, **MISSING_PAGE:29** あり): 帰納法 (|G| について).
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
4. **Case q ≠ p**: (MISSING_PAGE:29 以降) Sylow q-subgroup の coprime
   action, induction.
5. (L789-793, MISSING_PAGE 後の残部) `Q ⊆ GL(P)` 線型変換のうち
   `v_1^β = λ_1·v_1`, `v_2^β = λ_2·v_2` (`λ_i^q = 1`) の形, から (a), (b).

**形式化方針**:
- mathlib `Sylow` ✓, `Matrix.GeneralLinearGroup` ✓, `Module.finrank` ✓.
- 依存: G Lem 2.6.3 (p-group fixed vector; Isaacs FGT 不在;
  mathlib partial), shared module
  `OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean`
  (~30 行) で新規構築.
- 奇数位数: `Odd (Nat.card G)`.
- 帰納構造: `(Nat.card G).strongRecOn` または `WellFoundedLT`.
- MISSING_PAGE:29 内容: PDF p.28-29 を再 OCR or 別文献
  (Aschbacher §35.4 等) で補完必要.

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
