---
id: 9506
slug: modular-p-modular-system
title: "modular 表現論の底: p-modular system と Brauer 指標 (0147 の bottom-up 第 1 段, hub claim)"
created: 2026-08-03
---

# modular 表現論の底: p-modular system と Brauer 指標

**claim**: hub / main session (9500 band) / **状態**: 着手 (2026-08-03)

## 位置づけ

[issue 0147](0147-q8-modular-char-theory-frozen.md) (Q₈ Brauer–Suzuki, spine = Navarro 1998
Ch.1–7 / Z\*-定理) の **bottom-up 第 1 段**。project spec =
`notes/meta/q8_modular_char_theory_frozen_project.md` §3 の (1)(2)。

3 冊 (Isaacs / BG / Peterfalvi) の残り唯一の実 `sorry` が
`Peterfalvi/Appendices/RankOneAffineModel.lean` の `brauerSuzuki_quaternionSylow_q8` であり、
その根には mathlib にも本リポジトリにも**一切存在しない** modular 表現論がある (下記実測)。

## 着手前検索の結果 (2026-08-03 実測)

* **mathlib に無い**: `BrauerCharacter` / `decompositionMatrix` / block 論 / `defectGroup` は
  0 件 (`CartanMatrix` はルート系のもので別物)。mathlib の表現論は char 0 の ordinary のみ。
* **本リポジトリにも無い**: `OddOrder/GroupTheory/RepresentationTheory/` は 114 leaf あるが
  すべて ordinary。`pRegular` / `IsPRegular` / `IsDiscreteValuationRing` / `ResidueField` の
  grep はいずれも 0 件。
* 使える土台: mathlib の `IsDiscreteValuationRing` / `IsLocalRing.ResidueField` /
  `IsAdicComplete`、および本リポジトリの ordinary 指標一式
  (`ClassFunction` / `IrreducibleCharacter` / 誘導指標 / 直交関係)。

## 設計方針 (この issue で決める分岐)

Brauer 指標の定義には 2 つの流儀がある:

1. **p-modular system 経由** (Navarro Ch.1–2 の流儀): 完備 DVR `𝒪` (剰余体 `k` が char `p`,
   商体 `K` が char 0) を固定し、`p'`-位数の 1 の冪根の群 `U ⊆ K^×` と `k^×` の間の同型を通す。
2. **代数閉体 `k` だけで定義**: `k^×` の `p'`-部分と `ℂ^×` の `p'`-部分の間の単射を固定する。

**採用 = 1 (p-modular system)**。理由: block 論 (Brauer 対応・defect group、Navarro Ch.3–6) が
`𝒪` 上の冪等元の持ち上げを本質的に使うので後段で必ず必要になる。2 から始めると block 論の
段で作り直しになる。

⚠ **carrier の構成可能性 (CLAUDE.md「進捗の測り方」)**: `IsPModularSystem` を仮説クラスとして
置くだけでは doneness にならない。任意の `p` と `n` に対して「`n` 乗根を含む分裂 p-modular
system」を**実際に構成する**ところまでを本 issue のスコープに含める
(`ℤ[ζ_n]` の `p` 上の極大イデアルでの局所化 → 完備化)。これが無いと最終定理が空虚になる。

## やること (bottom-up)

- [x] **`p`-正則元の API** = `OddOrder/GroupTheory/PRegularElement.lean` (2026-08-03)。
      `IsPElement` / `IsPRegular` / `pPart` / `pRegularPart` と分解
      `g = g_{p'} · g_p`・**一意性** (`eq_pPart_of_commute`)・共役同変性。
      mathlib は群の元 1 個の `p`/`p'` 分解を持たない (実測)。
      ⚠ `(ordCompl[p] n : ℤ)` は **ℤ の除算**で elaborate される罠あり (docstring に明記)。
- [x] **根の持ち上げ** = `.../Modular/RootsOfUnityLift.lean` (2026-08-03)。
      Henselian 局所環 `𝒪` で `n` が単元なら還元は同型 `μ_n(𝒪) ≃* μ_n(k)` を誘導
      (`rootsOfUnityEquivResidue`)。一意性は `X^n - 1` の 1 次 Taylor 展開
      (`Polynomial.binomExpansion`) で `f'(b) = n b^{n-1}` が単元、
      存在は `HenselianLocalRing.is_henselian`。
      ⟹ **これが p-modular system の技術的核**。`𝒪` に完備 DVR を要求せず
      Henselian だけで足りることが分かったので、束ねの仮説はこれに合わせる。
- [x] **束ね** = `.../Modular/PModularSystem.lean` (2026-08-03)。
      `IsPModularSystem p 𝒪` = 「Henselian 局所環 `𝒪` が char 0、剰余体が char `p`」。
      `isUnit_natCast_of_not_dvd` (`p ∤ n` ⟹ `n` は `𝒪` の単元) と
      `rootsOfUnityEquivResidue_of_not_dvd` (`p ∤ n` で `μ_n(𝒪) ≃* μ_n(k)`)。
      ⚠ **非空虚性**: `ℤ_[p]` が instance (`instIsPModularSystemPadicInt`)。
      そのために `henselianLocalRing_of_isAdicComplete` (完備局所環は Henselian) を
      補った — mathlib は `HenselianRing R I` 版しか持たない (実測)。
- [x] **分裂 p-modular system の具体構成** (2026-08-03)。**不分岐拡大 = Witt ベクトル**を採用。
      2 leaf:
      * `.../Modular/WittVectorSystem.lean` — `k` が標数 `p` の完全体なら `𝕎 k` は
        `p`-modular system で **剰余体が `k` 自身** (`wittVectorResidueFieldEquiv`)。
        mathlib の `WittVector.quotientPEquiv` (`𝕎 k ⧸ (p) ≃+* k`) +
        `isAdicCompleteIdealSpanP` + `isDiscreteValuationRing` から
        `maximalIdeal (𝕎 k) = (p)` → Henselian を組む。`CharZero (𝕎 k)` は
        `n = p^a · m` 分解 + `p`-torsion freeness + 定数項が単元、で自前。
      * `.../Modular/SplittingSystem.lean` — **`SplittingSystem p n = 𝕎 (GF(p^φ(n)))`**。
        Euler (`p^φ(n) ≡ 1 mod n`) で `n ∣ |GF| − 1` ⟹ 有限体が `μ_n` を全部持つ ⟹
        剰余体経由で `HasEnoughRootsOfUnity (SplittingSystem p n) n`
        (**`rootsOfUnityEquivResidue_of_not_dvd` で `𝒪` 自身へ持ち上げ**)。
        非空虚性の決定打 = `natCard_rootsOfUnity_splittingSystem : Nat.card μ_n(𝒪) = n`。
      ⚠ 「分裂」を新クラスにはしない — 条件は mathlib の
      `HasEnoughRootsOfUnity (ResidueField 𝒪) n` そのものなので、下流は
      `[HasEnoughRootsOfUnity (ResidueField 𝒪) n]` と書く (ラッパー方針)。
- [x] **対角化可能性** = `OddOrder/Algebra/EigenspaceDecomposition.lean` (2026-08-03)。
      分裂した無平方零化多項式 `∏_{ζ ∈ s}(X - ζ)` で消える自己準同型は固有空間で張られる
      (`iSup_eigenspace_eq_top_of_aeval_prod_eq_zero`、証明 = Lagrange 補間)。
      系: `A^m = 1` + 原始 `m` 乗根 ⟹ 分解 + 内部直和 + `∑_ζ dim V_ζ = dim V`。
      ⚠ mathlib の `IsSemisimple.iSup_eigenspace_eq_top` は `IsAlgClosed` 前提で**使えない**
      (modular では係数体は「ちょうど足りる有限体」なので代数閉にできない)。
- [x] **Brauer 指標** = `.../Modular/BrauerCharacter.lean` (2026-08-03)。
      `rootLift n : k → 𝒪` (全域関数化した持ち上げ、`Finset k` 上の和で使うため) と
      `brauerCharacter n ρ g = ∑_{ζ ∈ μ_n(k)} dim_k V_ζ · ζ̂`。
      `brauerCharacter_one` (= `dim_k V`) / `brauerCharacter_conj` (類関数) /
      **`residue_brauerCharacter` (剰余 = 通常のトレース)** が定義の正当性を固定する。
- [x] **`p`-正則元との接続** (2026-08-03)。`pRegularExponent p G = |G|_{p'}` を導入し
      `orderOf_dvd_pRegularExponent` (Lagrange + `p ∤ orderOf g`) ⟹
      `residue_brauerCharacter_of_isPRegular` は `ρ g` への仮説なしで成立。
- [x] **加法性** (2026-08-03)。`brauerCharacter_quotient_add_subrepresentation`:
      `G`-不変 `W ≤ V` で `φ_V = φ_{V/W} + φ_W` ⟹ **組成因子だけで決まる**。
      核 = `finrank_eigenspace_eq_quotient_add` (各固有値ごとの次元加法性)。
      ⚠ スペクトル射影を作らず、**各 ζ の不等号 + 3 本の全次元恒等式で総和を squeeze**
      (`Finset.sum_eq_sum_iff_of_le`) して全項同時に等号にした。
- [x] **`𝒪` 上の固有空間分解** (2026-08-03)。分解行列 `D` は `𝒪`-束の還元を経由するので
      体でなく `𝒪` 上で分解する必要がある。
      * `Algebra/LagrangeInterpolationRing.lean` — 可換環 Lagrange (節点差が単元 =
        `SeparatedNodes`)。`eq_zero_of_degree_lt_card_of_eval_eq_zero` +
        `sum_ringLagrangeBasis`。
      * `iSup_eigenspace_eq_top_of_separated` — 体版はこの特殊化になった。
      * `.../Modular/LatticeEigenspaces.lean` — `separatedNodes_of_pow_eq_one`
        (**相異なる `n` 乗根は剰余が相異なる ⟹ 差が単元**、これが `𝒪` が体でなくても
        回る理由) + `iSup_eigenspace_eq_top_of_pow` / `_splittingSystem`。

## 次の段 (別 issue へ分割予定)

- [x] **分解写像の恒等式 (作用素レベル)** (2026-08-03)。
      `trace_eq_sum_finrank_baseChange_eigenspace`:
      `tr_𝒪 A = ∑_{ζ ∈ μ_n(𝒪)} dim_k(還元の ζ̄-固有空間) • ζ`
      = `brauerCharacter_eq_sum_nthRootsFinset` と同じ形。
      * `Algebra/LagrangeInterpolationRing.lean` / `EigenspaceDecomposition` の
        PID 版 (`trace_eq_sum_finrank_smul`) / `LatticeEigenspaces` (`𝒪` 側の分解と
        `μ_n(𝒪) ≃ μ_n(k)`) / `Reduction.lean` (底変換と 2 段 squeeze)。
      ⚠ **Nakayama も splitting criterion も使っていない** — 各項の不等号 +
      総和一致で `Finset.sum_eq_sum_iff_of_le` が termwise 等号を出す、を 2 回。
- [x] **ブロック数 = `p`-regular 類の個数** (Brauer、2026-08-03 完了)。証明は
      `T = [kG,kG]` と `T' = {x : x^{p^m} ∈ T}` を経由する:
      * (a) `dim kG/T = #共役類` — **済** (`CommutatorSubspace` + `CommutatorQuotient`)
      * (b) `dim kG/T' = #p-正則類` — **核の Freshman's dream は済**
        (2026-08-03、`Algebra/WordExpansion.lean` 438 行):
        **`add_pow_prime_sub_sub_mem`** = 標数 `p` で
        `(x+y)^p - x^p - y^p ∈ T` (T は交換子を含む任意の加法部分群)。
        部品 = 非可換二項展開 (`add_pow_eq_sum_wordProd`) / 回転は交換子だけ動かす
        (`wordProd_rotateWord_sub_mem`) / 非定数語の周期は `p`
        (`const_of_iterate_rotateWord_eq`、`Function.minimalPeriod` 経由) /
        自由軌道の和は `p` 倍 (`exists_nsmul_sum_of_free`)。
        ⚠ mathlib の `add_pow_char` は可換性必須なので**非可換版は新規**。
        `p`-正則類側の道具 (`IsPRegularClass` / `pRegularPartClass`) も済。
        **`T'` の部分空間性も済** (2026-08-03、`Algebra/CommutatorSpan.lean`):
        `pow_mem_commutatorSpan` (`T` は `p` 乗で閉じる — 交換子の `p` 乗が
        交換子であることと Freshman から) →
        `add_pow_prime_pow_sub_sub_mem` (反復 Freshman) →
        **`commutatorRadical hp hchar : Submodule k A`** = `T'`。
        **上からの評価も済** (2026-08-03、`.../Modular/PRegularCount.lean`):
        `exists_pow_prime_pow_eq_pRegularPart` (`m = a·φ(d)` で
        `g^{p^m} = g_{p'} = (g_{p'})^{p^m}`) →
        `single_sub_single_pRegularPart_mem` (`g - g_{p'} ∈ T'`) →
        **`finrank_quotient_commutatorRadical_le : dim (kG ⧸ T') ≤ #p-正則類`**。
        **下からの評価の枠組みも済** (2026-08-03):
        * `frobQuotient` = `A ⧸ T` 上の**半線型 Frobenius** `[x] ↦ [x^p]`
          (加法的 = Freshman、`F(c•u) = c^p•F(u)`)
        * **`mem_commutatorRadical_iff_frobQuotient`**: `T'/T = ker F^∞`
        * `exists_uniform_pow_prime_pow_eq_pRegularPart`: 全元に効く一様な `m`
        * `iterate_frobQuotient_mk_single`: `F^[m][g] = [g_{p'}]` (類基底上)
        **(b) 完成** (2026-08-03、段 40 `.../Modular/PRegularCount.lean`):
        当初の pickup メモは「`F^m` が `Im F^m` 上で半線型全単射 ⟹ `ker F^∞ = ker F^m`
        ⟹ `kG/T' ≅ Im F^m`」という Fitting 型の道筋だったが、**半線型写像の階数・
        退化次数を経由せず直接独立性が出る**ので短くなった:
        `x = ∑_C c_C h_C ∈ T'` ⟹ `∃ j, F^[j][x] = 0`。反復回数を**一様指数 `m` の倍数**
        `j·m` まで増やすと同じ反復が (i) `p`-正則類を**固定**し (ii) 係数を
        `c ↦ c^{p^{jm}}` に上げる ⟹ `0 = ∑_C c_C^{p^{jm}}[h_C]` を `kG ⧸ [kG,kG]` 内で
        得て、そこでの類代表の独立性 (段 39) から `c_C = 0`。
        * `eq_zero_of_sum_smul_mem_commutatorRadical` (核) /
          `linearIndependent_mkQ_pRegular` / **`basisPRegularQuotient`** (基底!) /
          🎯 **`finrank_quotient_commutatorRadical`**
        * 一様指数を `m > 0` に強化 (`max a 1 · φ(d)`)。`p ∤ |G|` で素朴な `a·φ(d)` が
          0 になり「倍数まで膨らませる」が効かなくなるため。
      * **(c)(d) は 1 本にまとめて完成** (2026-08-03、段 41-43)。教科書 (Navarro 2.9) は
        (c) `dim A/(J+T) = #単純加群` と (d) `T' = J+T` を別々に立てるが、`J + T` を
        明示的に作らず**核の同定 1 回**で済ませた。
        🎯 **`Algebra/SplitSemisimpleCount.lean` の
        `finrank_quotient_commutatorRadical_eq_card`**:
        体 `k` (標数 `p`) 上の代数 `A` に対し `π : A ↠ B` が全射で**核が一様冪零**
        (`∀ y, π y = 0 → y^N = 0`)、`e : B ≃ₐ[k] ∏_{i∈ι} M_{n_i}(k)` なら
        **`dim_k (A ⧸ T') = #ι`**。証明は「還元 → 分裂 → 各ブロックのトレース」という
        全射 `Ψ : A → (ι → k)` を 1 本作り、その核が `T'` であることを 3 段で確認:
        * `Algebra/MatrixCommutator.lean` (段 41) — `[M_n(R), M_n(R)] = ker tr`
          (`sub_single_trace_mem_commutatorSpan` / `mem_commutatorSpan_matrix_iff`) と
          `tr(M^p) = (tr M)^p` (`trace_pow_prime`)。
          ⚠ 標準証明は代数閉包で固有値を使うが、ここでは
          `M ≡ tr M·E₀₀ (mod [A,A])` + 商上 Frobenius の半線型性で済む。
          ⟹ `commutatorRadical_matrix_eq` (被約環上の行列環では `T' = T`)
        * `Algebra/CommutatorSpanPi.lean` (段 43) — `commutatorSpan_pi` /
          `commutatorRadical_pi_eq` (積は因子ごと)
        * `Algebra/CommutatorSpanHom.lean` (段 42) — `map_commutatorSpan` (`T` は像) /
          **`mem_commutatorRadical_of_map_mem`** (核が一様冪零なら `T'` は**逆像**)。
          逆向きは形式的でなく、反復 Freshman で `x^{p^{m+r}} ≡ t^{p^r} ∈ T(A)`。

      * **仮説の供給まで完了** (2026-08-03、段 44 `.../Modular/BrauerCount.lean`)。
        `card_split_blocks_eq_card_pRegularClass` (抽象的な分裂データからの数え上げ) と、
        🎯🎯 **`exists_wedderburn_pi_matrix_card_eq`** — 標数 `p` の**代数閉体** `k` 上で
        `kG ⧸ J(kG) ≃ₐ[k] ∏_{i<n} M_{d_i}(k)` かつ **`n = #p`-正則類**。
        供給した仮説 (すべて mathlib 実測で足りた):
        * `IsArtinianRing (kG)` = `isArtinian_of_tower k` (有限次元)
        * `IsSemiprimaryRing` (artinian ⟹ semiprimary の instance) ⟹ `J` 冪零 +
          `kG ⧸ J` 半単純。一様冪零性は `Ideal.pow_mem_pow` + `J^N = ⊥`
        * Artin–Wedderburn = `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`
          → 代数閉体上の有限次元斜体は `k` 自身
          (`IsAlgClosed.algebraMap_bijective_of_isIntegral`) → `AlgEquiv.mapMatrix`
        ⚠ 代数閉体は**分裂性のためだけ**に使う。`𝕎(𝔽̄_p)` は完全体上の Witt ベクトルなので
        段 26 の p-modular system 構成とそのまま両立する。

## 次の段 (frontier, 2026-08-03)

- [x] **ブロック ↔ 既約加群の対応** — **一般論は完了 (2026-08-03、段 45-49)**。
      `R = ∏_{j∈ι} M_{n_j}(k)` について「単純 `R`-加群 ↔ `ι` (同型を除いて重複なし)」:
      * `Algebra/MatrixNaturalModule.lean` (段 45-46) — `Module (Matrix n n k) (n → k)` の
        **scoped instance** (mathlib は意図的に置いていない) / `isSimpleModule_matrix`
        (mathlib の `IsSimpleModule (Module.End R M) M` から `toLinAlgEquiv'` に沿って移送) /
        🎯 `linearEquiv_of_isSimpleRing` (単純 artin 環上の単純加群は同型を除き 1 つ —
        `M × N` 内の `Submodule.fst`/`snd` に mathlib の `IsSimpleRing.isIsotypic` を適用) /
        `linearEquiv_natural_of_isSimpleModule`
      * `Algebra/PiSimpleModule.lean` (段 47-48) — 中心冪等元 `e_i = Pi.single i 1` の族 /
        🎯 `exists_unique_idem_smul_eq_self` (単純加群では**ちょうど 1 つ**の `e_i` が恒等) /
        `factorModule` (`R i`-加群構造、`Module.toAddMonoidEnd` 経由) /
        `isSimpleModule_factor`
      * `Algebra/PiMatrixSimpleModules.lean` (段 49) — 🎯 `isSimpleModule_piNatural` /
        `idem_smul_piNatural` / 🎯 `nonempty_linearEquiv_natural_of_idem`

      **`kG` への配線も完了 (2026-08-03、段 50)**:
      * `Algebra/ModuleAlongSurjection.lean` — 全射 `f : A ↠ B` に沿った加群の往復。
        `isSimpleModule_compHom` (引き戻し) / **`moduleOfSurjective`**
        (核が零化するなら押し出せる、`RingHom.liftOfRightInverse` で
        `Module.toAddMonoidEnd` を持ち上げ) / `isSimpleModule_of_surjective`
      * `Algebra/PiMatrixSimpleModules.lean` — `blockModule` /
        🎯 `isSimpleModule_blockModule` / 🎯 `exists_linearEquiv_blockModule`
      * `.../Modular/BrauerCount.lean` — 🎯🎯 **`exists_surjective_blocks_card_eq`**:
        代数閉体上で `π : kG ↠ ∏_{i<n} M_{d_i}(k)` 全射・**`ker π = J(kG)`**・
        `n = #p`-正則類。`J(kG)` は単純加群を零化する (mathlib
        `IsSemisimpleModule.jacobson_le_annihilator`) ので上の 3 本が直接適用でき、
        **ブロック ↔ 既約 `kG`-加群 (同型を除き 1 対 1)**。
      ⟹ **`|IBr(G)| = #p`-正則類 (Brauer) が完全に形式化された**。

- [x] **`IBr(G)` の定義** (2026-08-03、段 51-52)。
      * `.../Modular/BlockRepresentation.lean` (段 51) — **`blockRepresentation π i`**
        (ブロックが担う `Representation k G (nn i → k)`)。
        `Module (kG) M` の言葉 (段 45-50) と `Representation k G V` の言葉 (段 27) の橋。
      * `.../Modular/WittVectorSystem.lean` (段 51) —
        **`instIsAlgClosedResidueFieldWittVector`**: `k` 代数閉 ⟹ `ResidueField (𝕎 k)` も代数閉。
        ⟹ `𝒪 = 𝕎(𝔽̄_p)` は p-modular system かつ剰余体が分裂体 (設定が空虚でない)。
      * `.../Modular/IrreducibleBrauerCharacter.lean` (段 52) —
        🎯 **`irreducibleBrauerCharacter π i`** = 第 `i` ブロックの Brauer 指標。
        `_conj` (類関数) / `_one` (次数 = ブロックの大きさ) /
        🎯 `residue_irreducibleBrauerCharacter` (`p`-正則元での剰余 = ブロックのトレース)。
- [x] **Brauer 指標の一次独立性 — 表現論的な中身** (2026-08-03、段 53-55)。
      * 段 53 (refactor) — `Algebra/SplitSemisimpleCount.lean` が次元の等式でなく
        🎯🎯 **`blockTraceQuotientEquiv : A ⧸ T' ≃ₗ[k] (ι → k)`** を公開するようにした
        (`blockTrace` / `surjective_blockTrace` / 🎯 `ker_blockTrace`)。
        次元一致だけでは「汎関数が双対の基底」に届かないため。
      * 段 54 — `.../Modular/BrauerIndependence.lean`:
        🎯 **`eq_zero_of_sum_blockTrace_pRegular_eq_zero`**
        (`τ_i` は `p`-正則元上で一次独立)。`τ_i` は `T'` を殺し、`p`-正則類は
        `kG ⧸ T'` を張る (段 40) ので、そこで消える汎関数は恒等的に 0。
      * 段 55 — `.../Modular/BrauerCharacterIndependence.lean`:
        🎯 **`mem_maximalIdeal_of_sum_irreducibleBrauerCharacter`**
        (`∑ c_i φ_i = 0` なら全ての `c_i ∈ 𝔪`)。剰余に落として段 54。

- [x] **一次独立性の arithmetic descent** (2026-08-03、段 56)。
      `.../Modular/BrauerLinearIndependence.lean`:
      🎯🎯 **`eq_zero_of_sum_irreducibleBrauerCharacter`** (`𝒪` が DVR なら `c = 0`)。
      ⚠ Krull 交叉での帰納でなく **Nakayama** 一撃: 関係式の全体 `S` は
      一様化元で割れる (整域) ので `S ≤ 𝔪 • S`、`S` は f.g.、`𝔪 = jacobson ⊥`。
      ⚠ 主張は `𝒪` 上。商体上は分母を払えば出るが未形式化 (docstring に明記)。
- [x] **Brauer 指標の同型不変性** (2026-08-03、段 57) — `brauerCharacter_congr`。
      分解数が well-defined になるための部品 (段 29 の加法性と対)。

## アーキテクチャ地図

leaf の層構造・mathlib 実測 (使えたもの/無かったもの)・設計判断は
[`notes/meta/modular_representation_theory.md`](../notes/meta/modular_representation_theory.md)
に集約 (本 issue は時系列ログ)。

## 次の段 (frontier, 2026-08-03)

- [x] **`HasEnoughRootsOfUnity 𝔽̄_p n`** — 解決済 (2026-08-03、段 58)。
      `hasEnoughRootsOfUnity_of_isAlgClosed` (`IsAlgClosed.lift` で `GF(p^φ(n))` を
      埋め込み、`hasEnoughRootsOfUnity_of_ringHom` で移送) +
      `.../Modular/StandardSystem.lean` の **`StandardSystem p = 𝕎(𝔽̄_p)`**。
      🎯🎯 `exists_surjective_blocks_card_eq_standardSystem` で、有限群 `G` と素数 `p`
      だけから分裂データ・ブロックと既約加群の同定・数え上げが全部出る。
- [x] **分解行列 `D`** — 完了 (2026-08-03、段 59-62)。
      `IrreducibleIsBlock.lean` (既約表現の指標は `IBr(G)` のどれか) /
      `AsModuleSimple.lean` (表現の既約性 ⟹ `asModule` 単純) /
      `MinimalSubrepresentation.lean` (**極小**非零不変部分空間) /
      🎯🎯 `BrauerDecomposition.lean` の **`exists_decomposition`**:
      `∃ d : ι → ℕ, ∀ p`-正則 `g`, `φ_ρ(g) = ∑_i d_i φ_i(g)`。
      ⚠ 組成列でなく極小不変部分空間を切り出す帰納 (部分表現側の対応が商より易しい)。
      ⚠ 等式が `p`-正則元上限定なのは加法性 (段 29) が `(ρ g)^n = 1` を要求するため
      (= Brauer 指標が意味を持つ範囲そのもの)。

- [x] **分解行列 `D` (通常指標側)** — 完了 (2026-08-03、段 63)。
      `.../Modular/DecompositionMatrix.lean` の 🎯🎯 `exists_decomposition_trace`:
      `tr_𝒪 (ρ g) = ∑_i d_i φ_i(g)` (`p`-正則 `g`)。段 32 + 段 62 を繋ぐだけ。

- [x] **block 論の入口** (2026-08-03、段 64-67):
      * `Algebra/CentralCharacter.lean` — 🎯 `exists_scalar_of_mem_center` (中心元は各
        ブロック上でスカラー) / 🎯 **`centralCharacter`** `ω_i : Z(A) →+* k` /
        `centralScalar_smul` (中心はブロック上で `ω_i` 倍) /
        🎯 `centralCharacterPi_eq_zero_iff` (核 = `Z(A) ∩ ker π`) / `SameBlock`
      * `Algebra/SeparatingSubalgebra.lean` (段 67) — 🎯 `Subalgebra.eq_top_of_separates`

## 次の段 (frontier, 2026-08-03 更新)

- [x] **block 冪等元 `e_B`** — 完了 (2026-08-03、段 68-69)。
      * 段 68 `centralCharacterAlg` — 中心指標を `Subalgebra.center k A →ₐ[k] k` に
        (段 67 が `k`-部分代数を要求するため)
      * 段 69 `Algebra/BlockIdempotent.lean` — `blockSetoid` / `Block` /
        🎯 **`surjective_blockCharacterPi`** (段 67 で全射) /
        🎯🎯 **`existsUnique_blockIdempotent`** (mathlib の
        `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent` で一意に持ち上げ)
      ⚠ `AlgHom → RingHom` の強制を暗黙に任せると `whnf` heartbeat 超過。
        `toRingHom` 明示 + 全射性/冪等性を先に `have` で切り出して解消。
- [x] **block 分解の基本構造** — 完了 (2026-08-03、段 70-72)。
      🎯🎯 `exists_completeOrthogonalIdempotents_block` (`∑_B e_B = 1`) /
      段 71 `Algebra/CentralIdempotentModule.lean` の一般補題
      (中心冪等元の完全直交族による局在; 段 47 をその系に書き換え) /
      🎯 `existsUnique_block_smul_eq_self` (**単純加群はただ 1 つの block に属する**)。
- [x] **原始冪等元分解と block 分解** — 完了 (2026-08-03、段 73-74)。
      `Algebra/PrimitiveIdempotent.lean` の 🎯 `completeOrthogonalIdempotents_matrixUnit` /
      🎯 `exists_completeOrthogonalIdempotents_lift` (`1 = ∑ f_x`、`A f_x` が射影不可分) と
      `BlockIdempotent.lean` の 🎯🎯 **`blockRingEquiv`** (`A ≃+* ∏_B (e_B A e_B)`、
      mathlib の `ringEquivOfIsMulCentral`)。
- [x] **相対トレース `Tr^H_K` と `G`-代数の基本法則** — 完了 (2026-08-03、段 75-77)。
      * 段 75 `Algebra/RelativeTrace.lean` — `relTrace K H a = ∑_{xK ⊆ H} x • a`
        (`MulSemiringAction G A`、`K ≤ H ≤ G`)。
        🎯 `sum_smul_eq_relTrace` (代表元非依存; 任意の添字型でよいのでこれ 1 本から全部出る) /
        `smul_relTrace` (`K`-不変 ⟹ 値は `H`-不変) / `relTrace_self` /
        🎯 **`relTrace_trans`** (推移性 `Tr^H_K ∘ Tr^K_L = Tr^H_L`; 単射性 +
        `Subgroup.relIndex_mul_relIndex` の濃度) / `relTrace_mul_of_fixed`・
        `mul_relTrace_of_fixed` (射影公式 ⟹ `A^H_K` は `A^H` のイデアル) /
        `relTrace_one` (`= [H:K]·1`) / `sum_out_smul_eq_relTrace_top`。
        ⚠ `Fintype` は `Fintype.ofFinite` で**定義の内側に閉じ込め** statement に漏らさない
        (mathlib の `leftTransversals.diff` と同じ流儀)。
        ⚠ mathlib は `Finite G` から `Finite (G ⧸ H)` を出す instance を持たないので補った。
      * 段 76 — 🎯 `relTrace_conj` (共役同変性 ⟹ defect group が 1 共役類になる根拠) /
        `relTrace_mul_eq_self` (`[H:K]·1` 可逆なら `A^H_K = A^H` ⟹ defect group を
        `p`-部分群へ縮められる根拠)。
      * 段 77 `Algebra/GroupAlgebraConjugation.lean` — **carrier**: `R[G]` への `G` の
        共役作用 (`conjRingAut` / **scoped** `conjMulSemiringAction`; global instance に
        しない)。`conj_smul_apply`/`conj_smul_single` / `smul_eq_conj` (代数内部の共役) /
        `smul_eq_self_iff_apply`・`forall_mem_smul_eq_iff_apply` (`(R[G])^H` の係数記述) /
        🎯 **`forall_smul_eq_iff_mem_center`** (`(R[G])^G = Z(R[G])`、可換係数)。
- [x] **Brauer 準同型 `Br_P`** — 完了 (2026-08-03、段 78-79)。
      * 段 78 `Algebra/PGroupOrbitSum.lean` — 🎯 **`sum_eq_sum_fixedPoints`**:
        `p`-群の作用で軌道上定数な関数の和は、`p` が係数を零化するなら**固定点の和に等しい**
        (`IsPGroup.card_modEq_card_fixedPoints` の加法版)。固定点は `Finset` +
        特徴づけ仮説で受け取り statement に decidability を持ち込まない。
      * 段 79 `Algebra/BrauerHomomorphism.lean` — `brauerProj P` (`C_G(P)` への台の切り詰め) と
        🎯🎯 **`brauerProj_mul_of_invariant`** (`(k[G])^P` 上で環準同型)。
        `c ∈ C_G(P)` の係数 `∑_a x_a y_{a⁻¹c}` の被和関数が `P`-共役軌道上で定数、を
        段 78 に食わせるだけ。⚠ `P` の共役作用は `ConjAct` 経由の局所 instance。

- [x] **類和と `Z(k[G])`** — 完了 (2026-08-03、段 80 `Algebra/ClassSum.lean`)。
      `classSum k g` (= `K̂`) / 🎯 **`relTrace_single_eq_classSum`** (`K̂ = Tr^G_{C_G(g)}(g)`;
      相対トレースの添字集合 `G/C_G(g)` が共役類そのもの) / `smul_classSum` /
      🎯 **`mem_span_classSum`** (`Z(k[G])` は類和で張られる)。
      ⟹ defect group の主張が類和の言葉に翻訳でき、段 64-69 の中心指標 `ω_B` と繋がる。
- [x] **相対トレースイデアル `A^H_K`** — 完了 (2026-08-03、段 81)。
      `relTraceIdeal K H : AddSubgroup A` と 🎯 `relTraceIdeal_mono` (`L ≤ K` で増える) /
      両側イデアル性 / `A^H_H = A^H` (⟹ `D = G` は常に候補) / 共役同変性 /
      `mem_relTraceIdeal_of_index_inv` (⟹ Sylow `p`-部分群へ縮小)。
      **defect group の定義に必要な性質はこれで全部揃った**。

### Z\* までの残り (2026-08-03 時点の見取り図)

ここまでで Navarro **Ch.1-2 は完備**、**Ch.3 (block) は基本構造まで**到達した。
Z\*-定理 (Ch.7) までに要るものを、手持ちとの差分で:

- [ ] **Cartan 行列 `C = DᵀD`** — Z\* の必須経路ではない**枝**。
      形式化には Jordan–Hölder の**重複度関数**が要る (mathlib は `CompositionSeries` は
      持つが多重度は未確認)。代替として split 代数では `c_{xy} = dim_k (f_x A f_y)` を
      定義に採る手もある。段 73 の `f_x` は既にある。
- [ ] **`𝒪G` 側への移行** — block 論は `kG` 上で組んだが、Ch.4 以降の defect group /
      Brauer 対応は `𝒪G` の block (= `kG` の block と 1 対 1) で書くのが標準。
      冪等元の持ち上げ (`J(𝒪G)` は冪零でないが `𝒪` が完備なので
      `IsAdicComplete` 版の持ち上げが要る) が入口。
- [x] ~~**相対トレース `Tr^G_H`**~~ — 段 75-77 で完了 (上記)。
- [x] ~~**Brauer 準同型 `Br_P`**~~ — 段 78-79 で完了 (上記、乗法性まで)。
- [x] **defect group の存在と `p`-群性** — 完了 (2026-08-03、段 82
      `Algebra/DefectGroup.lean`)。`IsDefectGroup b D` /
      🎯 `exists_isDefectGroup` (部分群束の整礎性 + `A^G_G = A^G`) /
      🎯🎯 **`isPGroup_of_isDefectGroup`** (`D` の Sylow `p`-部分群 `Q` は
      `[D:Q]` が `p` と素 ⟹ `A^G_Q = A^G_D` ⟹ 極小性で `Q = D`)。
- [x] **Mackey 公式** — 完了 (2026-08-03、段 83 `Algebra/MackeyFormula.lean`)。
      🎯 `smul_mk_eq_iff_mem_inf_conj` (`gL` の `K`-固定化群 = `K ⊓ ᵍL`) /
      🎯🎯 **`exists_mackey`** (`Tr^G_L(a) = ∑_{[K\G/L]} Tr^K_{K⊓ᵍL}(g·a)`;
      全単射 `(Σ ω, K ⧸ (K⊓ᵍL)) ≃ G ⧸ L` を直接構成) /
      🎯🎯 **`exists_mul_eq_sum_relTraceIdeal_inf`**
      (`A^G_D · A^G_{D'} ⊆ ∑_g A^G_{D⊓ᵍD'}`)。
- [ ] **defect group の共役性** — 残るは **Rosenberg の補題**
      (原始冪等元がイデアルの和に入れば 1 つのイデアルに入る) のみ。
      段 83 の `exists_mul_eq_sum_relTraceIdeal_inf` に `e = e·e` を食わせればよい。
- [ ] **block 冪等元を `Z(k[G])` に配線** — 段 69 の一般論 (`existsUnique_blockIdempotent`)
      と段 80 の類和・段 58 の分裂データを繋ぐ。これで `IsDefectGroup e_B D` が
      Brauer の意味の defect group になる。
- [ ] **Mackey 公式** — `Tr^H_L` を `K` に制限すると `∑_{KgL} Tr^K_{K ∩ ᵍL} ∘ ᵍ(-)`。
      defect group の共役性 (`A^G_D · A^G_{D'} ⊆ ∑_g A^G_{D ∩ ᵍD'}`) に要る。
      段 75 の `sum_smul_eq_relTrace` は任意添字型なので、軌道分解を食わせればよい。
- [ ] **`Br_P` の核** = `∑_{Q < P} Tr^P_Q((kG)^Q)` — Mackey が要る。
- [ ] **2nd/3rd main theorem** → **Z\*-定理** → Q₈ bridge。

⚠ 上の 3-5 は `kG`/`𝒪G` の**群環固有**の構造 (共役作用・部分群・相対トレース) を使う。
段 40-74 は「分裂半単純商を持つ有限次元代数」の一般論だったので、ここから先は
群論側の道具立てが増える。

以降 (別 issue に分割予定): Cartan 行列 `C = DᵀD` / block / Brauer 対応 /
2nd・3rd main theorem / Z\*-定理 → Q₈ bridge。

## PDF gate について

0147 の pickup 手順 step 1「Navarro Ch.5–7 を精読して Ch.1–4 の slice を絞る」は **PDF 待ち**
(ユーザー購入手配中)。ただし step 2 の**最初の段 (p-modular system / Brauer 指標) は
標準的な内容で slice 絞りに依存しない**ので、そこから着手する。
PDF が入り次第 Ch.5–7 を読んで以降の段の範囲を確定する。

## 完了条件

上記チェックボックスが全て埋まり、**具体構成による instance が存在**し、
build green + AxiomsCheck 登録 + sorry 非退行。

## 参照

- 親: [0147](0147-q8-modular-char-theory-frozen.md)
- spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
- 前提調査: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`
