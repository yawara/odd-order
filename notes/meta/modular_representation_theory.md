# modular 表現論 — アーキテクチャ地図 (2026-08-03)

issue [9506](../../issues/9506-modular-p-modular-system.md) の作業ログは**時系列**なので、ここには
**層構造**を置く。0147 (Q₈ Brauer–Suzuki, Navarro 1998 spine) の bottom-up 第 1 段として
2026-08-03 に一気に積んだ 30 弱の leaf がどう積み重なっているか。

## 0. 到達点

* **Brauer の数え上げ**: 標数 `p` の代数閉体 `k` 上で
  `kG ⧸ J(kG) ≃ₐ[k] ∏_{i<n} M_{d_i}(k)` かつ **`n = #{p`-正則類`}`**。
  ブロックは既約 `kG`-加群と同型を除いて 1 対 1 なので `|IBr(G)| = #p`-正則類。
* **既約 Brauer 指標 `IBr(G)`** の定義と、`p`-正則類上での**一次独立性**。
* **分解定理**: 任意の有限次元表現の Brauer 指標は `p`-正則類上で `IBr(G)` の
  ℕ 係数一次結合 (= 分解数)。通常指標側も
  `χ|_{p-reg} = ∑_φ d_{χφ} φ` (= 分解行列 `D`)。
* 非空虚性: `𝒪 = 𝕎(𝔽̄_p)` が DVR・Henselian・p-modular system で剰余体が代数閉。

## 1. 層 (下から)

### L1 群論の下ごしらえ

| leaf | 内容 |
|---|---|
| `GroupTheory/PRegularElement.lean` | `IsPRegular` / `pPart` / `pRegularPart` / `pRegularExponent p G = \|G\|_{p'}` / `IsPRegularClass` / `isPRegular_out` |

### L2 可換代数・線型代数

| leaf | 内容 |
|---|---|
| `Algebra/WordExpansion.lean` | **非可換 Freshman**: 標数 `p` で `(x+y)^p - x^p - y^p ∈ T` (回転軌道) |
| `Algebra/CommutatorSpan.lean` | `commutatorSpan` / **`commutatorRadical` = `T'`** / 商上の半線型 Frobenius |
| `Algebra/MatrixCommutator.lean` | **`[M_n(R),M_n(R)] = ker tr`** / `tr(M^p) = (tr M)^p` / `T'(M_n) = T` |
| `Algebra/CommutatorSpanPi.lean` | 積は因子ごと (`commutatorSpan_pi` / `commutatorRadical_pi_eq`) |
| `Algebra/CommutatorSpanHom.lean` | 全射に沿った `T` の像・`T'` の**逆像** (核が一様冪零) |
| `Algebra/LagrangeInterpolationRing.lean`, `Algebra/EigenspaceDecomposition.lean` | 可換環 Lagrange / 分裂零化多項式での固有空間分解 |

### L3 分裂半単純商の数え上げ

`Algebra/SplitSemisimpleCount.lean` — `π : A ↠ B`, `e : B ≃ₐ ∏ M_{n_i}(k)` に対し

* `blockTrace` = 還元 → 分裂 → 各ブロックのトレース
* 🎯 `ker_blockTrace` = `T'` (L2 の 4 leaf が全部ここに集約)
* 🎯 **`blockTraceQuotientEquiv : A ⧸ T' ≃ₗ[k] (ι → k)`**
  (次元の等式でなく**同型**。双対基底として使うので必須)

### L4 `kG` 側の数え上げ

| leaf | 内容 |
|---|---|
| `.../Modular/CommutatorSubspace.lean`, `CommutatorQuotient.lean` | `dim kG/[kG,kG] = #共役類`、類代表が基底 |
| `.../Modular/PRegularRadical.lean` | 一様指数 `m > 0` (`max a 1 · φ(d)`)、`g - g_{p'} ∈ T'` |
| `.../Modular/PRegularCount.lean` | 🎯 **`basisPRegularQuotient`** / `finrank_quotient_commutatorRadical` = `#p`-正則類 |

L3 と L4 を突き合わせて `.../Modular/BrauerCount.lean`:
`card_split_blocks_eq_card_pRegularClass` / **`exists_wedderburn_pi_matrix_card_eq`** /
**`exists_surjective_blocks_card_eq`** (`ker π = J(kG)` 付き)。

### L5 Artin–Wedderburn の一意性側 (ブロック ↔ 既約加群)

| leaf | 内容 |
|---|---|
| `Algebra/MatrixNaturalModule.lean` | scoped `Module (Matrix n n k) (n → k)` / 単純性 / **単純 artin 環の単純加群は 1 つ** |
| `Algebra/PiSimpleModule.lean` | 中心冪等元 `e_i`、**単純加群では一意の `e_i` が恒等** / `factorModule` |
| `Algebra/ModuleAlongSurjection.lean` | 全射に沿った加群の引き戻し・押し出しと単純性 |
| `Algebra/PiMatrixSimpleModules.lean` | 🎯 `isSimpleModule_blockModule` / 🎯 **`exists_linearEquiv_blockModule`** |

### L6 Brauer 指標

| leaf | 内容 |
|---|---|
| `.../Modular/RootsOfUnityLift.lean`, `PModularSystem.lean`, `WittVectorSystem.lean`, `SplittingSystem.lean` | `IsPModularSystem` と具体構成、剰余体の代数閉性 |
| `.../Modular/BrauerCharacter.lean` | **`brauerCharacter`** / 類関数 / 次数 / **剰余 = 通常トレース** / 加法性 / **同型不変性** |
| `.../Modular/BlockRepresentation.lean` | `Module (kG) M` ↔ `Representation k G V` の橋 |
| `.../Modular/IrreducibleBrauerCharacter.lean` | 🎯 **`irreducibleBrauerCharacter`** = `IBr(G)` |
| `.../Modular/BrauerIndependence.lean` | 🎯 ブロックトレースは `p`-正則元上で独立 |
| `.../Modular/BrauerCharacterIndependence.lean` | 関係式の係数は `𝔪` に入る |
| `.../Modular/BrauerLinearIndependence.lean` | 🎯🎯 **一次独立性** (Nakayama) |
| `.../Modular/StandardSystem.lean` | `𝕎(𝔽̄_p)` — 代数閉かつ全 `p'`-乗根、非空虚性証明書 |

### L7 分解定理 / block 論の入口

| leaf | 内容 |
|---|---|
| `.../Modular/AsModuleSimple.lean` | 既約表現 ⟹ `asModule` 単純 (不変部分空間 ↔ `kG`-部分加群) |
| `.../Modular/MinimalSubrepresentation.lean` | **極小**非零不変部分空間の存在と既約性 |
| `.../Modular/IrreducibleIsBlock.lean` | 🎯 既約表現の Brauer 指標は `IBr(G)` のどれか |
| `.../Modular/BrauerDecomposition.lean` | 🎯🎯 **`exists_decomposition`** = 分解数 |
| `.../Modular/DecompositionMatrix.lean` | 🎯🎯 **`exists_decomposition_trace`** = 分解行列 `D` (通常指標側) |
| `Algebra/CentralCharacter.lean` | 🎯 **`centralCharacter`** `ω_i : Z(A) →+* k` / `SameBlock` / 核 = `Z(A) ∩ ker π` |
| `Algebra/SeparatingSubalgebra.lean` | 🎯 分離部分代数は全体 |
| `Algebra/BlockIdempotent.lean` | 🎯🎯 **block 冪等元** `e_B` / 完全直交性 / 🎯🎯 **`A ≃+* ∏_B` (block 分解)** / 単純加群の block 帰属 |
| `Algebra/PrimitiveIdempotent.lean` | 行列単位の持ち上げ = 原始冪等元分解 (Cartan 行列の入口) |
| `Algebra/CentralIdempotentModule.lean` | 中心冪等元の完全直交族による局在 (段 47 の一般版) |

## 2. mathlib 実測 (使えたもの / 無かったもの)

**使えた** (自前で作らずに済んだ):

* `IsSimpleModule (Module.End R M) M` — 自然加群の単純性はこれの移送で済む
* `IsSimpleRing.isIsotypic` — 単純 artin 環上の単純加群が 1 つ、はこれ 1 本
* `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` — 代数閉体版 Wedderburn
  (⚠ 段 44 で**自前に組んでから**気付いて置換した。claim-before-build の教訓)
* `instIsSemiprimaryRingOfIsArtinianRing` — artinian ⟹ `J` 冪零 + 商が半単純
* `IsSemisimpleModule.jacobson_le_annihilator` — `J` は単純加群を零化
* `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` (Nakayama) — Krull 交叉より短い
* `RingHom.liftOfRightInverse` — 全射に沿った加群構造の押し出し
* `IsAlgClosed.of_ringEquiv` / `IsAlgClosed.algebraMap_bijective_of_isIntegral`

**無かった** (自前):

* 非可換 Freshman `(x+y)^p ≡ x^p + y^p` (`add_pow_char` は可換必須)
* `[M_n(R), M_n(R)] = ker tr` と `tr(M^p) = (tr M)^p`
* `Module (Matrix n n k) (n → k)` の instance — mathlib は**意図的に置いていない**
  (`n → k` は既に `k`-加群)。本リポでは scoped instance
* Brauer 指標・分解行列・block 論一式 (mathlib の表現論は char 0 の ordinary のみ)
* 群の元 1 個の `p`/`p'` 分解

## 3. 設計上の判断

* **`tr(M^p) = (tr M)^p` を固有値で証明しない**。`M ≡ tr M·E₀₀ (mod [A,A])` +
  商上 Frobenius の半線型性で済む。代数閉包も底変換も不要。
* **(c)(d) を分けない**。教科書 (Navarro 2.9) は `dim A/(J+T) = #単純加群` と `T' = J+T` を
  別々に立てるが、`J+T` を作らず**全射 1 本の核の同定**で済ませた。
* **数え上げは同型で公開する**。次元の等式だけでは「ブロックトレース汎関数が双対の基底」に
  届かず、一次独立性が出ない (段 53 で refactor)。
* **代数閉体は分裂性のためだけ**に使う。`𝕎(𝔽̄_p)` は完全体上の Witt ベクトルなので
  p-modular system 構成と両立する。

## 4. frontier (2026-08-03 時点)

1. ~~`HasEnoughRootsOfUnity 𝔽̄_p n`~~ — **解決済 (段 58)**。ルート (a) を採用:
   `IsAlgClosed.lift` で `GaloisField p φ(n)` を代数閉体に埋め込み、既存の
   `hasEnoughRootsOfUnity_galoisField` を `hasEnoughRootsOfUnity_of_ringHom`
   (ringEquiv 版から一般化) で移送。
   `.../Modular/StandardSystem.lean` に **`StandardSystem p = 𝕎(𝔽̄_p)`** を置き、
   `exists_isPrimitiveRoot_pRegularExponent_standardSystem` (L6 の `hω` を供給) と
   🎯 `exists_surjective_blocks_card_eq_standardSystem` (有限群 `G` と素数 `p` だけから
   全部出る非空虚性証明書) を得た。
2. ~~分解行列 `D`~~ — **解決済 (段 59-62)**。組成列でなく**極小**不変部分空間を切り出す
   帰納にした (部分表現の不変部分空間の対応は `Submodule.map W.subtype` の単射性だけで
   済み、商だと束の移送が要るため)。`Representation ↔ Module` の往復は
   `asModule` 側 (`AsModuleSimple.lean`) で処理。
3. ~~分解行列 `D` (通常指標側)~~ — **解決済 (段 63)**。
   `trace_eq_brauerCharacter_reduction` (段 32) と `exists_decomposition` (段 62) を繋ぐだけ。
   ⚠ 原始根を上下 2 つ取る (`ω : 𝒪` はトレースを Brauer 指標形にするのに、
   `ω' : ResidueField 𝒪` は還元を組成因子に割るのに)。どちらも段 58 が供給。
4. block 論は段 64-72 で**基本構造まで到達**:
   中心指標 → `SameBlock` → 分離部分代数 → 冪等元持ち上げ → 完全直交性 →
   **単純加群はただ 1 つの block に属する**。
   さらに段 73-74 で **原始冪等元分解** (`1 = ∑ f_x`、`A f_x` が射影不可分) と
   **`A ≃+* ∏_B (e_B A e_B)`** (block 分解) まで到達。
   次: Cartan 行列 `C = DᵀD` (`A f_x` の組成因子を数える) / Brauer 対応 /
   2nd・3rd main theorem / Z\*-定理 → Q₈ bridge。

### L8 相対トレース / block 論の群環側 (段 75-79)

| leaf | 内容 |
|---|---|
| `Algebra/RelativeTrace.lean` | 🎯 `sum_smul_eq_relTrace` (代表元非依存) / 🎯 **`relTrace_trans`** (推移性) / 射影公式 / 🎯 `relTrace_conj` / `relTrace_one` / `relTrace_mul_eq_self` |
| `Algebra/GroupAlgebraConjugation.lean` | `R[G]` の共役 `G`-代数構造 (scoped instance) / `smul_eq_conj` / 🎯 **`forall_smul_eq_iff_mem_center`** (`(R[G])^G = Z(R[G])`) |
| `Algebra/PGroupOrbitSum.lean` | 🎯 **`sum_eq_sum_fixedPoints`** (標数 `p` で軌道上定数な和は固定点の和) |
| `Algebra/BrauerHomomorphism.lean` | `brauerProj` / 🎯🎯 **`brauerProj_mul_of_invariant`** (`Br_P` は `(k[G])^P` 上の環準同型) |

**設計上の判断 (段 75-79)**:

* **`Fintype` を statement に漏らさない**。`relTrace` の剰余類和は `Fintype.ofFinite` を
  定義の内側で使う (mathlib の `Subgroup.leftTransversals.diff` と同じ)。代わりに
  「任意の添字型 + 全単射」版の `sum_smul_eq_relTrace` を 1 本立て、構造法則
  (不変性・推移性・共役同変性) は全てその適用として書く。Fintype instance の diamond を
  一切踏まない。
* **`p`-群の軌道数え上げを独立の補題に切り出す**。`Br_P` の乗法性は「係数の和が軌道上で
  定数」+ この補題、の 2 行になる。固定点集合は `MulAction.fixedPoints` でなく
  **`Finset` + 特徴づけ仮説**で受け取り、decidability を statement に持ち込まない。
* **群作用の instance は scoped / 局所**。`R[G]` への共役作用は `scoped[OddOrder.Conjugation]`、
  `P` の `G` への共役作用は証明内の `letI` (`ConjAct` 経由) — どちらも mathlib の既定
  (左乗法) と衝突するため。

段 80-81 追加:

| leaf | 内容 |
|---|---|
| `Algebra/ClassSum.lean` | `classSum` / 🎯 **`relTrace_single_eq_classSum`** (`K̂ = Tr^G_{C_G(g)}(g)`) / 🎯 `mem_span_classSum` (`Z(k[G])` は類和で張られる) |
| `Algebra/RelativeTrace.lean` (Ring 節) | **`relTraceIdeal K H`** = `A^H_K` / 🎯 `relTraceIdeal_mono` / 両側イデアル性 / 共役同変性 / 可逆指数判定 |

**次の frontier**: (i) Mackey 公式 (`Res_K Tr^H_L = ∑_{KgL} Tr^K_{K ∩ ᵍL} ∘ ᵍ(-)`;
`sum_smul_eq_relTrace` が任意添字型なので `K`-軌道分解を食わせればよい) —
defect group の共役性と `Br_P` の核 `∑_{Q<P} Tr^P_Q((kG)^Q)` に要る。
(ii) Rosenberg の補題。(iii) 段 69 の block 冪等元を `Z(k[G])` に配線 (段 80 の類和経由)。

段 82-83 追加:

| leaf | 内容 |
|---|---|
| `Algebra/DefectGroup.lean` | `IsDefectGroup` / 🎯 存在 / 🎯🎯 **`p`-群性** |
| `Algebra/MackeyFormula.lean` | 🎯 固定化群 = `K ⊓ ᵍL` / 🎯🎯 **Mackey 公式** / 🎯🎯 `A^G_D · A^G_{D'} ⊆ ∑_g A^G_{D⊓ᵍD'}` |

⚠ Mackey の軌道分解は mathlib の `selfEquivSigmaOrbitsQuotientStabilizer` を使うより
**全単射 `Φ : (Σ ω, K ⧸ (K⊓ᵍL)) → G ⧸ L`, `⟨ω,k⟩ ↦ k.out • ω.out` を手で構成**した方が
短い (equiv の `symm` を展開する手間が消える)。単射性 = 軌道類の一致 + 固定化群補題、
全射性 = 軌道の定義、で各 5 行。

段 84 追加:

| leaf | 内容 |
|---|---|
| `Algebra/Rosenberg.lean` | 🎯🎯 **`exists_mem_of_sum_eq_of_local`** (Rosenberg) / 可換版 (`N` = 冪零) / 🎯 Fitting の二分律 `isNilpotent_or_exists_mul_eq` / Artin 環版 `exists_pow_eq_pow_mul` |
| `Algebra/DefectGroupConjugacy.lean` | 🎯 `IsDefectGroup.conj` / 🎯🎯 **`exists_conj_eq_of_isDefectGroup`** (defect group は 1 共役類) / 可換 `A^G` 版 |

**設計上の判断 (段 84)**:

* **corner の局所性を型でなく述語で受ける**。Rosenberg を適用したい環は `A` の中の
  **固定部分環 `A^G`** であって `A` 自身ではない (`relTraceIdeal D ⊤` は `A` のイデアル
  ではなく `A^G` のイデアル)。`A^G` を `Subring` に束ねて `IsIdempotentElem.Corner` を
  取り `IsLocalRing` を課すと、instance diamond と transport が両方乗る。代わりに
  「非単元を表す述語 `N`」と「係数集合 `U ⊆ R`」を引数にした: `N` が加法で閉じ `e` を
  避ける = corner が局所環、そのもの。⚠ `N` は**加法閉性を全域で要求する**ので、
  非可換 `A` に `N = IsNilpotent` を渡すと偽になる — 可換版の適用では
  `N z := IsNilpotent z ∧ ∀ g, g • z = z` と `G`-不変性を抱き合わせ、
  `A^G` の可換性から加法閉性を出す。
* **Fitting の二分律を Artin 性から独立に立てる**。`isNilpotent_or_exists_mul_eq` は
  「`(ex)^n = (ex)^{2n} b` となる `n ≥ 1` がある」だけを仮定する。Artin 環からの供給
  (`exists_pow_eq_pow_mul`、`IsArtinian.monotone_stabilizes` を `Ideal.span {y^(m+1)}`
  の降鎖に食わせる) は別補題にした。`Z(kG)` を環型で実現したあと差し込むだけになる。

段 85 追加:

| leaf | 内容 |
|---|---|
| `Algebra/GroupAlgebraDefectGroup.lean` | 一般論を `A = k[G]` (共役作用) へ特殊化。`commute_of_forall_smul_eq` / 🎯 `exists_fixed_nsmul_one_inv` / 🎯 `isPGroup_of_isDefectGroup` / 🎯🎯 `isNilpotent_or_exists_fixed_mul_eq` / 🎯🎯 **`exists_conj_eq_of_isDefectGroup`** (= Brauer の定理) |

**設計上の判断 (段 85)**: `A^G` を環型で実現する必要があったが、**群環の場合は
`Subalgebra.center k (k[G])` がそのまま使える** (段 77 の `forall_smul_eq_iff_mem_center`
で `A^G = Z(k[G])`)。mathlib は `Subalgebra.center` に `CommRing` instance を持つので
diamond を踏まない。有限次元性は `Module.Finite.of_injective` (部分加群の subtype) から、
Artin 性は `IsArtinianRing.of_finite k _` から。⟹ 段 84 の `hdich` が実際に閉じ、
Brauer の定理が仮説付きでなく**中心の原始性だけ**を要求する形になった。

段 86 追加 (`Algebra/BlockIdempotent.lean` に追記): 🎯 **`eq_zero_or_eq_of_mul_eq_of_isIdempotentElem`**
(**block 冪等元は中心で原始的**) + `blockIdempotent_ne_zero`。
中心指標 `Φ` を通すと `Φ u` は `blocks → k` の冪等元 = 指示関数で、`e_B u = u` が台を
`B` に閉じ込める ⟹ `Φ u ∈ {0, Pi.single c 1}`。前者は核が nil ゆえ `u = 0`
(mathlib `eq_of_isNilpotent_sub_of_isIdempotentElem`)、後者は段 69 の一意性で `u = e_B`。
⟹ **段 85 の `hprim` / `hb0` が block 冪等元に対して閉じた**。

段 87 追加:

| leaf | 内容 |
|---|---|
| `Algebra/AlgClosedSplitting.lean` | 🎯 **`exists_algHom_pi_matrix_of_isAlgClosed`** (代数閉体上の有限次元代数 → nil 核を持つ行列積への全射) |
| `Algebra/BlockIdempotent.lean` (追記) | `blockCharacterPi_eq_zero_iff` (段 69 の `hnil` を `ker π` の nil 性へ接続) |
| `Algebra/GroupAlgebraBlocks.lean` | 🎯🎯 **`exists_blockIdempotents_defectGroups_conj`** (`k` 代数閉・`G` 有限のみで block 分解 + Brauer の定理) |

**設計上の判断 (段 87)**: 段 69 以来 block 論が仮説で受けていた分裂データは、
**代数閉体上なら mathlib だけで供給できる**: 有限次元 ⟹ `IsArtinianRing.of_finite` ⟹
`IsSemiprimaryRing.isNilpotent` (`J(A)` 冪零) + `IsSemisimpleRing (A ⧸ Ring.jacobson A)`
(instance) ⟹ `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`。
⚠ 「分裂体」を一般に扱おうとすると単純加群の自己準同型環が `k` という条件を
universe を跨いで量化する羽目になる。代数閉に限れば mathlib の Wedderburn がそのまま
使え、しかも **`k = 𝔽̄_p` は段 58 の `𝕎(𝔽̄_p)` の剰余体で実際に使う設定**なので損が無い。
有限体 `GF(p^φ(n))` 版は Brauer の分裂体定理が要る (別項目に繰延)。

段 88 追加:

| leaf | 内容 |
|---|---|
| `Algebra/ClassSum.lean` (一般化) | 🎯 **`relTrace_single_apply`** (`Tr^P_{P⊓C_G(g)}(c·g)` = `P`-軌道和); 段 80 の類和版は `P = ⊤` の系に |
| `GroupTheory/PGroupRelIndex.lean` | `p`-群の真部分群は指数が `p` で割れる (Isaacs Ch09 との重複を解消して移設) |
| `Algebra/BrauerKernel.lean` | 🎯 `brauerProj_relTrace_eq_zero` / 🎯🎯 **`brauerProj_eq_zero_iff`** (`ker Br_P = ∑_{Q<P} Tr^P_Q((kG)^Q)`) |

**設計上の判断 (段 88)**:

* **Mackey は使わなかった**。核の記述に要るのは「単項式の相対トレース = 軌道和」だけで、
  これは段 80 の類和の議論を `G` から `P` へ一般化すれば出る。⊆ 方向は
  **台の大きさに関する帰納法**: `b` の台の元 `g` は `Br_P b = 0` ゆえ `C_G(P)` の外にあり、
  安定化群 `Q = P ⊓ C_G(g)` は真部分群。`Tr^P_Q(b_g·g)` を引くと軌道 1 本が丸ごと台から消える。
* ⚠ `set Q := ...` した部分群は**商型 `↥P ⧸ Q.subgroupOf P` の型に現れる**ので
  `rw [hQ]` が motive not type correct で落ちる。membership 補題
  (`hQmem`/`hQcomm`) を先に立てて `Q` を書き換えないで済ませる。
* ⚠ `k[G]` は `Finsupp` の型シノニムなので `Finsupp.sub_apply` / `finsetSum_apply` の
  `rw` が型不一致で落ちることがある。`have ... := rfl` / 明示型の `have` で回避。
* ⚠ `if` の `Decidable` インスタンスが `Fintype.decidableExistsFintype` と
  `Classical.propDecidable` で食い違うので、`if_pos`/`if_neg` 済みの 2 本に分けて渡す。

段 89 追加 (`Algebra/BrauerDefect.lean`): 🎯 **`brauerProj_eq_zero_of_forall_not_le`**
(`b ∈ A^G_D` で `P` がどの `ᵍD` にも入らないなら `Br_P b = 0`) と対偶
🎯 `exists_le_conj_of_brauerProj_ne_zero` / `card_le_card_of_brauerProj_ne_zero`。
**ここで段 83 の Mackey が効く**: `Res_P Tr^G_D(a) = ∑_g Tr^P_{P⊓ᵍD}(g·a)` に段 88 の核を
かけると `P ⊓ ᵍD < P` の項が全滅し、生き残るのは `P ≤ ᵍD` の項だけ。
= **Brauer の第 1 主定理の易しい半分** (block が「見る」`p`-部分群は defect group に
部分共役なものだけ)。

段 90 追加 (`BrauerHomomorphism.lean` / `BrauerKernel.lean` に追記): **Brauer 構成**
`A(P) = (k[G])^P / ∑_{Q<P} Tr^P_Q ≅ k[C_G(P)]`。
🎯 `exists_forall_smul_eq_brauerProj_eq` (全射性 + 切断: `C_G(P)` 上に台を持つ元は
そもそも `P`-不変なので `Br_P` の切断が自明に取れる) / 🎯 `brauerProj_conj_smul`
(`N_G(P)`-同変 ⟹ `Z(k[G])` を `k[C_G(P)]^{N_G(P)}` へ送る) /
🎯🎯 `brauerProj_eq_iff_sub_mem` (段 88 の核と合わせて商の同一視)。
土台 = `conj_mem_centralizer_iff` (`N_G(P)` の元による共役は `C_G(P)` を保つ)。

段 91 追加 (`Algebra/BrauerFirstMain.lean`): 🎯🎯 **`brauerProj_ne_zero_of_isDefectGroup`**
(= **第 1 主定理の難しい半分** `Br_D(e_B) ≠ 0`)。文献無しで再構成した。

**設計上の判断 (段 91) — 経路選択がすべて**:

* ⚠ **`N_G(D)` の Mackey 分解ルートは詰まる**。`A^G_D ∩ ker Br_D ⊆ ∑_{Q<_G D} A^G_Q` を
  `b = Tr^N_D(a) + junk` (`N = N_G(D)`) から出そうとすると
  「`c ∈ A^N ∩ A^D_{<D}` から `Tr^G_N(c) ∈ A^G_{<D}`」で止まる —
  `p ∣ [N_G(D):D]` があり得るので `Tr^N_D` による平均化が効かない。
* **類和基底で回すと通る**: `Br_D(e) = 0` ⟹ `C_G(D)` と交わる類の係数が全部 0 ⟹
  `e` は「`D ≰ ᵍS_K` なる類和 `K̂`」の一次結合。各 `K̂` は `C_G(x)` の Sylow `p`-部分群
  `S` からの相対トレース (段 80 + 段 85 の可逆指数 + 推移性) なので、`e = e·e` に
  段 83 (`A^G_D · A^G_S ⊆ ∑_g A^G_{D⊓ᵍS}`) を食わせると**全項が `D` の真部分群から**。
  Rosenberg (段 84) で 1 つに落ちて極小性に矛盾。
* 支持補題: `relTrace_smul` / `smul_mem_relTraceIdeal` (トレースイデアルは `k`-部分加群 —
  段 83 の積を係数付き類和に使うのに要る) / `eq_sum_classSum` (段 80 の証明から抽出) /
  `GAlgebra.exists_mem_relTraceIdeal_of_sum_eq` (Rosenberg のトレースイデアル版)。

⟹ 段 89 と合わせて **defect group = `Br_P(e) ≠ 0` なる極大 `p`-部分群** (Brauer の特徴づけ)。

**次の frontier**: Brauer 対応 (`Br_D` で `G` の block と `N_G(D)` の block を対応させる) →
2nd/3rd main theorem → Z\*。他の枝: Cartan 行列 / `𝒪G` への移行 / 分裂体定理。
