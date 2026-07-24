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
# BG §2A-§2E — the basic representation propositions (Prop 2.1-2.4, Thm 2.5)

Bender–Glauberman §2: Schur + absolute irreducibility (Prop 2.1), Clifford theory for a
cyclic quotient (Prop 2.2), Fong–Swan (Lem 2.3), the eigenspace decomposition under a
cyclic action (Prop 2.4), and the extraspecial-group theorem (Thm 2.5).

Split from `OddOrder.BG.Ch1_Preliminary.S02_RepresentationsBasic` (issue 0149, the
longFile-1500 campaign); that file imports this leaf, so downstream imports are
unchanged.
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

**形式化状態 (2026-07-18 更新, 旧 docstring は stale だった)**: 両パートとも形式化済み・sorry-free.
- **(a)** = `OddOrder.RepresentationTheory.restriction_isIrreducible`
  (`RepresentationTheory/CliffordMultiplicityOne.lean`). 制限が `M` 上 isotypic ⇒
  Skolem–Noether で `n = 1` を出す. `CliffordAlgClosed.lean` の共役単純部分加群
  permutation + isotypic 構造が土台. **char 条件なし** (2026-07-17 に Maschke 仮定
  `[Finite ↥H] [NeZero (Nat.card ↥H : k)]` を除去; 半単純性は `CliffordAlgClosed` の
  `isSemisimpleModule_resRep_of_isIrreducible` = 標数フリーな Clifford 論法で供給).
  Isaacs Ch.6 §6F Clifford 章に依存しない (Clifford decomposition を BG の
  `M ≅ M^x` 仮説から表現論的に直接構成).
- **(b)** = `OddOrder.RepresentationTheory.exists_extension_of_nonempty_equiv_conjRep`
  (`RepresentationTheory/CyclicExtension.lean`). 任意の代数閉体 `F` 上・任意標数で
  `H ⊴ K`, `K/H` cyclic (生成元 `g`), `ρ ≅ ρ^g` から拡張 `σ` (`Res_H σ = ρ`, `σ` 既約)
  を構成. Schur + `m` 乗根で正規化した共役単位 `P` による `g^i h ↦ P^i ρ(h)` 構成.
  ℂ 版 (Isaacs CTFG 11.22, 指標直交性から `ρ ≅ ρ^g` を導く層) は
  `CyclicCharacterExtension.lean`.

**下流引用**: §3 Thm 3.4 ×2 (BG §3 Frobenius; extraspecial Clifford は
`CliffordConjugateChar.lean` 経由), §2C Lem 2.3 内部 (`Prop 2.2` 直接適用).
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


end OddOrder.BG.Ch1.S02
