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
- [x] **Rosenberg の補題** — 完了 (2026-08-03、段 84 `Algebra/Rosenberg.lean`)。
      🎯🎯 **`exists_mem_of_sum_eq_of_local`** (冪等元 `e` の corner `eRe` が局所環なら、
      `e` がイデアルの有限和に入るとき既に 1 つのイデアルに入る)。
      局所性は**述語 `N` (corner の非単元) を引数で受ける** — 実際に適用したいのは
      大きい環 `A` の中の**固定部分環 `A^G`** なので、型に束ねてまた解くのは純粋な摩擦。
      係数側も集合 `U ⊆ R` で受ける。可換版 `exists_mem_of_sum_eq_of_isNilpotent`
      (`N` = 冪零)、Fitting の二分律 🎯 `isNilpotent_or_exists_mul_eq`
      (`u = (ex)^n b` が冪等 ⟹ 原始性で `0` か `e` ⟹ 冪零か corner で可逆)、
      その Artin 環版 `exists_pow_eq_pow_mul` / `exists_mem_of_sum_eq_of_isArtinian`
      (= 仮説が充足可能であることの実証) まで。
- [x] **defect group の共役性** — 完了 (2026-08-03、段 84
      `Algebra/DefectGroupConjugacy.lean`)。
      🎯 `IsDefectGroup.conj` (共役は defect group; 段 81 の共役同変性から) /
      🎯🎯 **`exists_conj_eq_of_isDefectGroup`** (`b = b·b` に段 83 を食わせ
      Rosenberg で 1 つの `A^G_{D⊓ᵍD'}` に落とし、`D` の極小性で `D ≤ ᵍD'`、
      `ᵍD'` の極小性で `D = ᵍD'`) /
      🎯🎯 **`exists_conj_eq_of_isDefectGroup_of_commute`** (`A^G` 可換版 =
      `A = kG` 共役作用で `A^G = Z(kG)` のとき使う形; `N` = 冪零 ∧ `G`-不変)。
- [x] **群環への特殊化 (`A = k[G]`, 共役作用)** — 完了 (2026-08-03、段 85
      `Algebra/GroupAlgebraDefectGroup.lean`)。一般論の仮説 3 本を全部落とした:
      `commute_of_forall_smul_eq` (`A^G = Z(k[G])` は可換) /
      🎯 `exists_fixed_nsmul_one_inv` (`char k = p`, `p ∤ n` ⟹ `n·1` はスカラー
      `(n:k)⁻¹` で可逆かつ `G`-不変) ⟹ 🎯 **`isPGroup_of_isDefectGroup`** /
      🎯🎯 **`isNilpotent_or_exists_fixed_mul_eq`** (`Z(k[G])` は有限次元可換 ⟹ Artin
      ⟹ 段 84 の Fitting 二分律; `Subalgebra.center k (k[G])` を環型として使い
      `Module.Finite` → `IsArtinianRing.of_finite`) ⟹
      🎯🎯 **`exists_conj_eq_of_isDefectGroup`** = **Brauer の定理**
      (`Z(k[G])` の原始冪等元の defect group は 1 共役類)。
- [x] **block 冪等元の原始性** — 完了 (2026-08-03、段 86 `Algebra/BlockIdempotent.lean`)。
      🎯 **`eq_zero_or_eq_of_mul_eq_of_isIdempotentElem`** (`e_B u = u` な中心冪等元 `u` は
      `0` か `e_B`)。証明: `Φ u` は `blocks → k` の冪等元 = 指示関数で、`e_B u = u` が
      台を `B` に閉じ込める ⟹ `Φ u = 0` か `Pi.single c 1`。前者は核が nil ゆえ `u = 0`、
      後者は段 69 の一意性で `u = e_B`。`blockIdempotent_ne_zero` も (段 85 の `hb0`)。
      ⟹ **段 85 の `hprim`/`hb0` は block 冪等元に対して閉じた**。
- [x] **分裂データの供給 + 無仮説版 Brauer** — 完了 (2026-08-03、段 87)。
      * `Algebra/AlgClosedSplitting.lean` — 🎯 **`exists_algHom_pi_matrix_of_isAlgClosed`**:
        **代数閉体上の有限次元代数は nil 核を持つ行列積への全射を持つ**。
        有限次元 ⟹ Artin ⟹ `J(A)` 冪零 (`IsSemiprimaryRing.isNilpotent`) かつ
        `A/J(A)` は半単純 ⟹ 代数閉体上の Artin–Wedderburn
        (`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`)。
      * `Algebra/BlockIdempotent.lean` に `blockCharacterPi_eq_zero_iff`
        (中心指標が全部消える ⟺ `π` で消える; 段 69 の `hnil` を `ker π` の nil 性に接続)。
      * `Algebra/GroupAlgebraBlocks.lean` — 🎯🎯
        **`exists_blockIdempotents_defectGroups_conj`**:
        **`k` 代数閉・`G` 有限のみを仮定して**、`k[G]` の block 冪等元の完全直交族が存在し
        (各々中心・非零)、**各 block の defect group は 1 つの `G`-共役類をなす**。
        ⚠ `k = 𝔽̄_p` は実際に使う設定 — 段 58 の `𝕎(𝔽̄_p)` の剰余体そのもの。
- [ ] **分裂体版 (代数閉でない `k`)** — 上は `IsAlgClosed k` を使う。有限体
      `GF(p^φ(n))` (段 58) で同じことを言うには **Brauer の分裂体定理**が要る (別項目)。
- [x] **`Br_P` の核** = `∑_{Q < P} Tr^P_Q((kG)^Q)` — 完了 (2026-08-03、段 88)。
      * `Algebra/ClassSum.lean` を一般化: 🎯 **`relTrace_single_apply`**
        (`Tr^P_{P ⊓ C_G(g)}(c·g)` は `P`-軌道和 = 各共役に係数 `c`)。
        段 80 の `relTrace_single_eq_classSum` (`K̂ = Tr^G_{C_G(g)}(g)`) は `P = ⊤` の系に。
      * `GroupTheory/PGroupRelIndex.lean` — `p`-群の真部分群は指数が `p` で割れる
        (Isaacs Ch09 `SubnormalClosure.lean` にあった重複を共有 leaf へ移設)。
      * `Algebra/BrauerKernel.lean` — 🎯 `brauerProj_relTrace_eq_zero` (⊇ 方向:
        `C_G(P)` 上の係数は `[P:Q]·a c` で `p ∣ [P:Q]`) と
        🎯🎯 **`brauerProj_eq_zero_iff`** (⊆ 方向は台の大きさに関する帰納法 —
        `g` の安定化群 `Q = P ⊓ C_G(g) < P` で `Tr^P_Q(b_g·g)` を引くと軌道 1 本が消える)。
      ⟹ **Brauer の第 1 主定理の計算部分が揃った**。
- [x] **`Br_P` と defect group の接続 (第 1 主定理の易しい半分)** — 完了 (2026-08-03、段 89
      `Algebra/BrauerDefect.lean`)。🎯 **`brauerProj_eq_zero_of_forall_not_le`**
      (`b ∈ A^G_D` で `P` がどの `ᵍD` にも入らないなら `Br_P b = 0`)。
      証明 = **Mackey (段 83) + 核 (段 88)**: `Res_P Tr^G_D(a) = ∑_g Tr^P_{P⊓ᵍD}(g·a)` で
      `P ⊓ ᵍD < P` の項は全部核に落ちる。対偶が
      🎯 `exists_le_conj_of_brauerProj_ne_zero` (`Br_P b ≠ 0 ⟹ ∃g, P ≤ ᵍD`) と
      `card_le_card_of_brauerProj_ne_zero` (`|P| ≤ |D|`)。
- [x] **Brauer 構成 `A(P) ≅ k[C_G(P)]`** — 完了 (2026-08-03、段 90)。
      `BrauerHomomorphism.lean` に `conj_mem_centralizer_iff` (正規化元による共役は
      `C_G(P)` を保つ) / `forall_smul_eq_of_support_subset` (`C_G(P)` 上に台を持つ元は
      `P`-不変) / `brauerProj_eq_self` / 🎯 **`exists_forall_smul_eq_brauerProj_eq`**
      (`Br_P` は `(k[G])^P` から `k[C_G(P)]` へ**全射**、切断つき) /
      🎯 **`brauerProj_conj_smul`** (`Br_P` は `N_G(P)`-同変 ⟹ `Z(k[G])` を
      `k[C_G(P)]^{N_G(P)}` へ送る = Brauer 対応の舞台)。
      `BrauerKernel.lean` に 🎯🎯 **`brauerProj_eq_iff_sub_mem`**:
      `(k[G])^P / ∑_{Q<P} Tr^P_Q ≅ k[C_G(P)]` (段 88 の核 + 上の全射性)。
- [x] **第 1 主定理の難しい半分** = `Br_D(e_B) ≠ 0` — 完了 (2026-08-03、段 91
      `Algebra/BrauerFirstMain.lean`)。**文献無しで自力再構成した**。
      ⚠ `A^G_D ∩ ker Br_D ⊆ ∑_{Q<_G D} A^G_Q` を `N_G(D)` の Mackey 分解で出そうとすると
      「`c ∈ A^N ∩ A^D_{<D}` から `Tr^G_N(c) ∈ A^G_{<D}`」で詰まる
      (`p ∣ [N_G(D):D]` があり得るので平均化が効かない)。**類和基底で回すと通る**:
      * 🎯 **`exists_isPGroup_le_centralizer_classSum_mem`** — 類和 `K̂` は
        `C_G(x)` の Sylow `p`-部分群 `S` からの相対トレース
        (`K̂ = Tr^G_{C_G(x)}(x)` (段 80) + `[C_G(x):S]` 可逆 (段 85) + 推移性)。
      * `mem_centralizer_of_le_conj` — `D ≤ ᵍS ≤ ᵍC_G(x)` なら `ᵍx ∈ C_G(D)`。
      * `Br_D(e) = 0` ⟹ `C_G(D)` と交わる類の係数が全部 0 ⟹ `e` は
        「`D ≰ ᵍS_K` なる `K̂`」の一次結合。
      * `e = e·e` に段 83 (`A^G_D · A^G_S ⊆ ∑_g A^G_{D⊓ᵍS}`) を食わせると
        **全項が `D` の真部分群からのトレース**。
      * Rosenberg (段 84) で 1 つに落ちて `D` の極小性に矛盾。
      支持補題: `relTrace_smul` / `smul_mem_relTraceIdeal` (トレースイデアルは `k`-部分加群) /
      `eq_sum_classSum` (段 80 の証明から抽出) /
      `GAlgebra.exists_mem_relTraceIdeal_of_sum_eq` (Rosenberg のトレースイデアル版、
      段 84 の適用を 1 本に括り出し)。
      ⟹ 段 89 と合わせて **defect group = `Br_P(e) ≠ 0` なる極大 `p`-部分群**
      (Brauer の特徴づけ)。
      これがあれば Rosenberg (段 84) + `D` の極小性で閉じる。
- [ ] **残り slice** = 下記「★ PDF gate 解除後の slice 確定」の 9 段。

⚠ 上の 3-5 は `kG`/`𝒪G` の**群環固有**の構造 (共役作用・部分群・相対トレース) を使う。
段 40-74 は「分裂半単純商を持つ有限次元代数」の一般論だったので、ここから先は
群論側の道具立てが増える。

## ★ PDF gate 解除 + slice 確定 (2026-08-04)

**PDF が届いた** (`references/navarro/`、issue 0147 参照)。本 issue が待っていた
「Ch.5–7 を精読して以降の段の範囲を確定する」を実施した結果:

### ⚠ 経路訂正 — **Z\*-定理は不要**

旧チェックリスト末尾の「2nd/3rd main theorem → **Z\*-定理** → Q₈ bridge」は**誤り**。
Navarro Ch.7 は **BS を先に直接証明**し (冒頭 "First, we need to prove the Brauer–Suzuki
theorem"、(7.2)–(7.6) → 書籍 pp.139–146 が本証明)、**そのあと** (7.7)(7.8) を足して (7.9) Z\*。
⟹ **Z\* と「Z\* → Q₈ bridge」は経路から落ちる**。しかも Navarro は Q₈ を名指しで狙い
`|S| > 8` は Isaacs に外出ししているので、repo 側の分担 (`|S| ≥ 16` 済) と教科書が一致する。
詳細 = `notes/meta/q8_modular_char_theory_frozen_project.md` §2''。

### BS 本証明 (pp.139–146) が直接引く結果

`Cor (6.13)` / `Cor (5.8)` + 第三主定理 / `Lemma (5.13.b,c,d)` / block orthogonality /
`(7.2)`–`(7.6)`。ここから逆に辿った**残り slice (段 92 以降)**:

- [x] **92: 分解行列 `D` の well-defined 化** — 完了 (2026-08-04、`Modular/DecompositionNumber.lean`)。
      段 63 の `exists_decomposition_trace` は `∃ d` までしか言わないので、`D` を行列にするには
      一意性が要る。中身は段 56 の一次独立性で、実作業は配管 2 本:
      🎯 `exists_pow_eq_zero_of_ker_eq_jacobson` (`ker π = J(kG)` → 核の一様冪零性。
      `kG` は体上有限次元 ⟹ Artin ⟹ semiprimary、`isArtinian_of_tower` が要る) と
      `AlgHom.mk'` + `AlgEquiv.refl` による bare `RingHom` の詰め替え。
      🎯 `eq_of_sum_irreducibleBrauerCharacter_eq` / `existsUnique_decomposition_trace` /
      `decompositionNumber` / `trace_eq_sum_decompositionNumber` / `eq_decompositionNumber`。

### ⚠ 依存の訂正 (2026-08-04、実測) — Cartan 行列より **ordinary 側**が上流

上のリストは当初「92 = Cartan 行列」を筆頭に置いたが、**それは順序として誤り**。
Navarro は `C = DᵀD` を**定義**として置く (書籍 p.25) ので、Cartan 行列を作るには
`D` の行添字 = **`Irr(G)`** が要る。ところが repo の modular 側は今のところ
「1 つの格子表現 `ρ` の分解数」までしか持たず、`Irr(G)` を添字集合として持っていない。
さらに `(6.13)` が要求する `Irr(B)` (ブロックごとの ordinary 指標) には
**`Irr(G) → Bl(G)` の block 写像**が要る。⟹ **ordinary 側の整備が Cartan 行列の上流**。

**着手前調査の結果 (2026-08-04 実測、再調査不要)** — 素材は思ったより揃っている:

* `OddOrder/Algebra/CentralCharacter.lean` — 中心指標 `ω_i : Z(A) →+* k` は
  **任意の体・任意の行列積への全射**で構築済 (`exists_scalar_of_mem_center` /
  `centralCharacter` / `SameBlock`)。
* `OddOrder/Algebra/BlockIdempotent.lean` — `Block π hπ hlin` = Wedderburn 添字を
  「中心指標が一致」で割った商。ブロック冪等元・原始性・完全直交系・defect group まで。
* `RepresentationTheory/CenterClassSumBasis.lean` — `Z(k[G])` の類和基底 (`centerBasis`)。
  **一般体で書かれている** (2026-08-04 の dedup で `CommSemiring` まで一般化)。
* `Modular/InvariantLattice.lean` — `exists_invariant_lattice` (`K`-表現は `𝒪`-格子を持つ)。
  repo で `K = Frac(𝒪)` 側に触れている唯一のファイル。
* repo の ordinary 指標論 116 leaf のうち **約半数 (50) は `[Field k]` で一般体**、
  58 が ℂ 固定。`Center*` クラスタは前者。

**⟹ 次の段 (93) = `𝒪`-側の中心指標と ordinary 指標の block**。`𝒪`-格子表現の中心指標が
`𝒪` 値であることは、`ρ` が `K` 上絶対既約なら Schur で `K`-スカラーになり、格子を保つので
基底で見て `𝒪` に入る、で出る (Navarro の「代数的整数だから」という議論は `𝒪`-格子の
定式化では不要になる)。そのあと `mod 𝔪` で `Z(kG)` の中心指標 = ブロックが決まる。

- [ ] **93: `𝒪`-側の中心指標 → `Irr(G) → Bl(G)` の block 写像** (上記; Cartan 行列の上流)
  - [x] **整数性の核** — 完了 (2026-08-04、`Modular/LatticeCentralCharacter.lean`)。
        🎯 `eq_smul_of_baseChange_eq_smul`: 自由 `𝒪`-加群の自己準同型が base change で
        `c • id` なら `c` は初めから `𝒪` に入り、写像は既にその `𝒪`-スカラー。
        ⟹ **Navarro が引く「`ω_χ(K̂)` は代数的整数」(Isaacs Characters (3.7)) が不要になる**。
        + `smul_id_injective` (スカラーの一意性) + `exists_smul_id_of_mem_center`。
  - [x] **`hscalar` を Schur で discharge** — 完了 (2026-08-04)。
        🎯 `exists_baseChange_smul_of_mem_center` (base change の乗法性 → 中心元は像と可換
        → 絶対既約性でスカラー) + 🎯 `exists_smul_id_of_mem_center_of_absolutelyIrreducible`
        (整数性との合成 = **絶対既約 ⟹ 中心指標が `𝒪` 値**)。

### ⚠⚠ 発見 (2026-08-04): `StandardSystem` は ordinary 側の分裂体として**不十分**

`StandardSystem p = 𝕎(𝔽̄_p)` の商体 `K = Frac(𝕎(𝔽̄_p))` は **`ℚ_p` の最大不分岐拡大の完備化**。
⟹ `p'`-乗根はすべて含むが **`ζ_p` を含まない** (`ℚ_p(ζ_p)/ℚ_p` は次数 `p−1` の完全分岐拡大)。
`p = 2` なら `i = ζ_4 ∉ K`。

* `StandardSystem.lean` の docstring が主張しているのは**剰余体側**の 2 条件だけ
  (`k` が群環を分裂させる = 代数閉、`k` が `|G|_{p'}` 乗根を持つ) で、**`K` の分裂には触れていない**。
  段 92 までは剰余体側しか使っていなかったので問題が表面化しなかった。
* ordinary 側 (`Irr(G)`・中心指標・分解行列の行添字) は `K` が `K[G]` を分裂させることを使う。
  Brauer の定理より `ℚ(ζ_{exp G})` は分裂体だが、`exp G` の `p`-部分に対応する乗根は
  **分岐**するので `Frac(𝕎(𝔽̄_p))` には入らない。

**⟹ 採った方針**: 絶対既約性を「**加群ごと**」の仮説として述べる (`hEnd`)。
「`K` が `K[G]` を分裂させる」という大域的仮説を置かないので、分岐拡大を作らずに先へ進める。
必要になった時点で個別に discharge する。

**⟹ 将来必要になる作業** (BS 本証明で `Irr(B₀)` を数える段で効くはず):
`𝒪` を `ζ_{exp G}` を含むように**分岐拡大**する (`𝕎(𝔽̄_p)[ζ_{p^a}]` 等) か、
局所体の整数環として splitting p-modular system を構成する。
`IsPModularSystem` 自体は分裂を要求していないので class の変更は不要 — 別の instance を作る話。
  - [x] **`ω` の AlgHom 化** — 完了 (2026-08-04)。
        🎯 `centralCharacter : Subalgebra.center 𝒪 A →ₐ[𝒪] 𝒪`
        (+ `centralScalar` / `apply_center_eq_centralScalar_smul` / `eq_centralScalar`)。
        Navarro の `ω_χ` そのものだが**初めから `𝒪` 値**。
  - [x] **`mod 𝔪` の道具立て** — 完了 (2026-08-04、`Modular/CenterReduction.lean`)。
        `λ_χ` を定めるのに要る**存在**と**一意性**の両側が揃った:
        * 前提として `CenterClassSumBasis` を `Field k` → `CommRing k` へ一般化
          (体の演算を一切使っていなかった = 無償の特殊化債務。本文無変更・消費側無変更で通った)。
          ⟹ 類和基底と `center_eq_sum_classSum` が **`𝒪` 上でも使える**。
        * 🎯 `exists_mem_center_mapRingHom_eq` — 係数写像が全射なら `Z(k'G)` の元は
          `Z(kG)` へ持ち上がる (類和は係数 `0`/`1` なので還元で不変、が鍵)。
        * 🎯 `apply_eq_zero_of_mapRingHom_eq_zero` / 🎯 `apply_eq_of_mapRingHom_eq` —
          **値は持ち上げに依らない** = `λ_χ` が well-defined。
  - [x] **`λ` の bundle** — 完了 (2026-08-04)。
        🎯 `reducedCentralCharacter : Subalgebra.center k' (k'[G]) →+* k'`
        (+ `centerLift` / `mapRingHom_centerLift` / `reducedCentralCharacter_eq`)。
        Navarro の `λ_χ(K̂) = ω_χ(K̂)^*` そのもの。
  - [x] **橋渡しの前半** — 完了 (2026-08-04)。
        🎯 `baseChange_apply_center`: 絶対既約格子の**還元でも中心はスカラー作用**し、
        そのスカラーは `algebraMap 𝒪 k (ω z)` (= `λ`)。⟹ 還元の**どの単純構成因子でも
        中心は同じ指標で作用する**ので、全部同じブロックに入る (Navarro (3.3) の核心)。

  - [x] **橋渡しの後半** — 完了 (2026-08-04)。
        🎯 `MatrixModule.eq_centralScalar_of_forall_smul_eq` /
        🎯 `MatrixModule.eq_centralCharacterAlg_of_forall_smul_eq`:
        中心元が第 `i` ブロック上でスカラー `c` 倍なら `c` はその中心指標値。
        `centralScalar_smul` と突き合わせて `Pi.single a 1` で評価するだけ。
        `centralCharacterAlg` の形にしたのは `blockSetoid` がこれを比較しているため。
  - [x] **還元と群環作用の両立** — 完了 (2026-08-04)。
        🎯 `asAlgebraHom_reduction_mapRingHom` (`Modular/Reduction.lean`):
        還元は群の元だけでなく群環の作用全体と両立する。中心指標を下へ運ぶ足場。

  - [x] **単純加群 → ブロック** — 完了 (2026-08-04、`Algebra/BlockOfSimpleModule.lean`)。
        🎯 `exists_eq_centralCharacterAlg_of_forall_smul_eq`。
        ⚠ 仮説は `algebraMap k A c • m` の形 (`M` は自前の `k`-構造を持たず、
        `A`-線型同値は `A`-作用しか尊重しないため)。
  - [x] **スカラー作用が部分表現へ降りる** — 完了 (2026-08-04、`MinimalSubrepresentation.lean`)。
        🎯 `coe_subrepresentation_asAlgebraHom` (部分表現は群環の作用全体の制限を担う) +
        🎯 `subrepresentation_asAlgebraHom_eq_smul`。

  - [x] **組み立て** — 完了 (2026-08-04、`Modular/BlockOfRepresentation.lean`)。
        🎯🎯 `exists_eq_centralCharacterAlg_of_asAlgebraHom_eq_smul`:
        **`Z(k[G])` が表現上でスカラー `c` 倍なら `c` はどれかのブロックの中心指標**。
        ⚠ `M := (ρ.subrepresentation W hWinv).asModule` を明示しないと
        `IsSemisimpleModule` の instance 解決が metavariable で詰まる。

**⟹ 段 93 完了 (2026-08-04)。ordinary → block の橋が通った。**
絶対既約 `𝒪`-格子について: `ω_χ` (整数性つき) → 還元で中心はスカラー `λ_χ` 作用 →
`λ_χ = centralCharacterAlg π i` = **`χ` の属するブロック** (Navarro (3.1)(3.3))。

### 次にやること (2026-08-04 時点の frontier)

  - [x] **分裂 `p`-modular system の構成** — 完了 (2026-08-04、
        [issue 9507 closed](closed/9507-splitting-p-modular-system.md))。
        🎯🎯 **`𝓞_ℂ_[p]` = `ℂ_[p]` の付値環**を採用 (mathlib
        `NumberTheory/Padics/Complex.lean` に既存)。商体 `ℂ_[p]` が**代数閉**なので
        `K[G]` の分裂は Wedderburn–Artin で即得られ、**剰余体も代数閉**なので `k[G]` 側も
        無条件 — **Brauer の分裂体定理も Lang (C₁) も使わない**。
        Henselian も完備性なしで出る (代数閉な商体では monic の根が初めから `A` に在り、
        `𝔪` が素であることで `a₀` と同じ剰余類の根が選べる)。
        * 新 leaf: `Algebra/AlgClosedFractionField.lean` /
          `Modular/PadicComplexSystem.lean`
        * 代償 = 離散性 (値群が可除)。既存機構を **DVR → `ValuationRing` に一般化**:
          `BrauerLinearIndependence` は一様化元+Nakayama を「割り切りの全順序」に置換、
          `EigenspaceDecomposition` は PID の構造定理を
          「有限生成 (レトラクト) + 捩れ無し ⟹ Bézout で平坦 ⟹ 局所で自由」に置換。
          DVR は局所+Bézout ゆえ `StandardSystem` 側は無変更で通る。

### 段 94 (Cartan 行列) の進行 — 2026-08-04

  - [x] **不変格子上の表現と、その指標 = 通常指標** — 完了
        (`Modular/LatticeRepresentation.lean` + `Algebra/ValuationRingFreeModule.lean`)。
        🎯 `free_of_isTorsionFree` (付値環上の有限生成捩れ無しは自由) /
        `Submodule.IsLattice.free_of_valuationRing` (mathlib の同名は PID を要求) /
        🎯 `repr_extendOfIsLattice` (mathlib の `Basis.extendOfIsLattice` が作る `K`-基底は
        格子ベクトルの上で `𝒪`-座標をそのまま読む) /
        🎯🎯 `algebraMap_trace_latticeRepresentation`
        (`algebraMap 𝒪 K (tr_𝒪 L (ρ_L g)) = tr_K V (ρ g)`) /
        🎯 `exists_isLattice_invariant`。
  - [x] **分解数は格子に依らない** — 完了 (`Modular/DecompositionOfOrdinary.lean`)。
        🎯🎯 `decompositionNumber_latticeRepresentation_eq` = 分解写像
        `Irr(G) → ℤ IBr(G)` の well-defined 性 (Navarro (2.9) / Isaacs Ch.15)。
  - [x] **分解行列 `D` を `Irr(G)` 添字で定義** — 完了
        (`Modular/OrdinaryIrreducibles.lean`)。行添字 = `K[G] ≃ ∏ M_{m_j}(K)` の成分。
        `wedderburnRepresentation` / `wedderburnLattice` / 🎯🎯 `decompositionMatrix` /
        定義性質・一意性・任意の不変格子で同じ。
  - [x] **Cartan 行列 `C = DᵀD` と `Φ_φ`** — 完了 (`Modular/CartanMatrix.lean`)。
        ⚠ **Navarro p.25 では `C = DᵗD` は定理でなく定義** ("we say that C = DᵗD is the
        Cartan matrix")。よって `D` が揃った時点で定義できる。
        `ordinaryCharacter` (不変格子上のトレースゆえ初めから `𝒪` 値) /
        `cartanMatrix` + `cartanMatrix_comm` / `projectiveIndecomposableCharacter` /
        🎯 `projectiveIndecomposableCharacter_eq_sum_cartanMatrix`
        (p-正則類上で `Φ_φ = Σ_μ c_{μφ} μ`) = **(2.13) の代数側の半分**。
  - [x] **分裂体 `K` 上の非対角第一直交関係** — 完了
        (`Modular/OrdinaryOrthogonality.lean`)。
        🎯 `asAlgebraHom_wedderburnRepresentation` / 🎯 `exists_asAlgebraHom_eq_id_eq_zero`
        (中心冪等元の引き戻し) / 🎯 `map_asAlgebraHom_of_intertwiningMap` /
        🎯 `subsingleton_intertwiningMap_of_ne` /
        🎯🎯 `sum_character_mul_character_inv_eq_zero` (`i ≠ j` で `Σ_g χ_j(g)χ_i(g⁻¹) = 0`)。
        ⚠ **代数閉性を一切使わない**のが非対角側の特徴。

  - [x] **第一直交関係を K 上で完成** — 完了 (`Modular/OrdinaryOrthogonality.lean`)。
        `Σ_g χ_j(g) χ_i(g⁻¹) = |G| δ_{ij}`。
        ⚠ **代数閉性は不要だった** (前回の見通しは過大見積もり) — 分裂性を仮定した時点で
        ブロックは `K` 上の*完全*行列環なので、行列単位 `E_{b a₀}` 一発で Schur が出る
        (`exists_eq_smul_id_of_intertwiningMap`)。
  - [x] **指標表の正方性** — 完了 (`Modular/OrdinaryIrrCount.lean`)。
        🎯 `card_eq_card_conjClasses` (`|Irr(G)| = |cl(G)|`; どちらも `Z(K[G])` の基底を数える)
        + `centerAlgEquivPi` + `equivConjClasses`。
  - [x] **第二 (列) 直交関係** — 完了 (`Modular/OrdinaryColumnOrthogonality.lean`)。
        `sum_eq_sum_conjClasses` (体に依らない類分解) / `isUnit_conjugacyClassSize`
        (⚠ 標数 p でも `|C|` は 0 になりうるので `|C|·|C_G| = |G|` から可逆性を出す) /
        `characterMatrix` · `characterMatrixInv` = 1 → 正方性で両側逆 →
        🎯🎯 `sum_character_inv_mul_character` (`Σ_χ χ(x⁻¹)χ(y) = |C_G(x)| δ_{x~y}`)。
  - [x] **Navarro (2.13) の解析側** — 完了
        (`Modular/ProjectiveCharacterVanishing.lean` + `DecompositionNumber` に
        🎯 `eq_zero_of_sum_irreducibleBrauerCharacter_ringHom` を追加)。
        🎯🎯 `algebraMap_sum_projectiveIndecomposableCharacter_mul_inv` —
        p-正則な `y` と任意の `x` で `Σ_φ Φ_φ(x) φ(y⁻¹) = |C_G(y)| δ_{y~x}` /
        🎯🎯 `projectiveIndecomposableCharacter_eq_zero` (`x` が p-特異なら `Φ_φ(x) = 0`)。

  - [x] **`[Φ_θ,φ]⁰ = δ_{θφ}` → `([θ,φ]⁰)` が `C` の逆行列** — 完了 (2026-08-04)。
        `Modular/PRegularClassIndex.lean`: 🎯 `card_eq_card_pRegularClass`
        (repo 既存の Brauer 数え上げを `π : →+*` 形へ bridge) + `equivPRegularClass` +
        `pRegularRep` + 🎯 `pRegularRep_isConj_iff`。
        `Modular/CartanInverse.lean`: 🎯 `isUnit_card_centralizer` /
        🎯🎯 `projMatrix_mul_brauerMatrix` (`A·B = 1`) /
        🎯🎯 `brauerMatrix_mul_projMatrix` (正方性で `B·A = 1`) /
        🎯🎯 `sum_brauer_mul_projectiveIndecomposableCharacter` /
        🎯 `sum_eq_sum_pRegularRep` · `sum_pRegular_eq_sum_pRegularRep` (類分解) /
        3 種の指標の `IsConj` 形類関数性 / `pairingZero` (Navarro の `[a,b]⁰`、
        ⚠ `|G|` は 𝒪 で可逆でないので値は `K`) /
        🎯 `pairingZero_eq_sum_pRegularRep` /
        🎯🎯🎯 `pairingZero_projectiveIndecomposableCharacter` (`[Φ_θ,φ]⁰ = δ`) /
        🎯🎯🎯 `sum_cartanMatrix_mul_pairingZero` (`Σ_μ c_{μθ} [μ,φ]⁰ = δ`)。

**⟹ 段 94 完了 (2026-08-04)。** 分解行列 `D`・Cartan 行列 `C = DᵀD`・射影不可分解指標
`Φ_φ`・分裂体上の第一/第二直交関係・Navarro (2.13) (`([μ,φ]⁰) = C⁻¹`) が揃った。

<details><summary>着手時の計画 (参考)</summary>

        材料は全部揃っている:
        * 行列等式 `A·B = I`。`x` を p-正則類の代表 `x_L` に走らせ
          `A_{L,φ} := Φ_φ(x_L)`、`B_{φ,K} := φ(x_K⁻¹) / |C_G(x_K)|` と置くと
          `algebraMap_sum_projectiveIndecomposableCharacter_mul_inv` がそのまま `A·B = I`。
        * **正方性** `|IBr(G)| = #{p-正則類}` は repo 既存 =
          `Modular/BrauerCount.lean` の `card_split_blocks_eq_card_pRegularClass`
          (`Nat.card ι = Nat.card {C : ConjClasses G // IsPRegularClass p C}`)。
        * `mul_eq_one_comm` で `B·A = I`、これが `[Φ_θ,φ]⁰ = δ_{θφ}`。
        * 最後に `Φ_θ|_{G°} = Σ_μ c_{μθ} μ`
          (= `projectiveIndecomposableCharacter_eq_sum_cartanMatrix`、既済) を代入して
          `C · ([μ,φ]⁰) = I`。
        ⚠ p-正則類の代表を取る仕掛け (`conjugacyClassRepresentative` の p-正則版) と
        `[Φ_θ,φ]⁰` の定義 (`(1/|G|) Σ_{g ∈ G°}`) をどう置くかが最初の設計判断。
</details>
- [ ] **94: Cartan 行列 `C = DᵀD`** + `([φ,θ]⁰)` が逆行列であること ((7.6) が使う)
### 段 95 (Brauer 対応 `b^G`) の進行 — 2026-08-04

⚠ **原文確認で構造が判明** (Navarro (4.13) 直前): `b^G` は `Br_P` からでなく
**中心指標の拡張**で定義される。`λ_b^G(K̂) = λ_b(Σ_{x ∈ K ∩ H} x)` が代数準同型に
なるとき `b^G` が「定義される」。`Br_P` が出てくるのは (4.14)
(`P·C_G(P) ≤ H ≤ N_G(P)` なら常に定義され `λ_b^G = λ_b ∘ Br_P`) の段階。
⚠ 誘導 block には非同値な定義が複数 (Brauer 版 / Alperin–Burry 版)。Navarro は Brauer 版。

  - [x] **`Σ_{x ∈ K ∩ H} x` が `Z(k[H])` の元** — 完了 (`Modular/TruncClassSum.lean`)。
        `truncClassSum` / 🎯 `coeff_truncClassSum` / 🎯 `truncClassSum_mem_center`。
  - [x] **`centerTrunc : Z(kG) →ₗ[k] Z(kH)` と `λ_b^G`** — 完了 (同ファイル)。
        類和基底の上で `Basis.constr`。⚠ **線型なだけ**で乗法性は別問題。
        `inducedCentralCharacter H λ_b = λ_b ∘ centerTrunc H`。
  - [x] **中心指標 → 一意な block (Navarro (3.11))** — 完了
        (`Algebra/CentralCharacterBlock.lean`)。
        🎯 `existsUnique_blockIdempotent_map_eq_one` /
        🎯🎯 `existsUnique_blockCharacter_eq` / `blockOfCentralCharacter`。
  - [x] **誘導 block `b^G` の定義** — 完了 (`Modular/InducedBlock.lean`)。
        🎯🎯 `inducedBlock` / 🎯 `blockCharacter_inducedBlock_classSumCenter` (定義性質) /
        🎯 `eq_inducedBlock`。乗法性は教科書どおり仮説。

  - [x] **Navarro (2.32)** 「正規 `p`-部分群は単純 `kG`-加群に自明に作用」— 完了
        (`Algebra/NormalPSubgroupTrivialAction.lean`)。
        `blockRepresentation` (splitting `π` の第 `i` ブロックを `G` の表現として見る) /
        🎯 `blockRepresentation_eq_one_of_mem_normal_pSubgroup` /
        🎯 `pi_single_eq_one_of_mem_normal_pSubgroup` (`π (single u 1) i = 1`)。
        ⚠ **エンジンは repo に既存だった**: `V^N ≠ 0` (char `p` の `p`-群固定ベクトル) は
        `GroupTheory/RepresentationTheory/PGroupFixedVector.lean` の
        `IsPGroup.invariants_ne_bot` (BG §2 由来、帰納法済) がそのまま使える。
        `Algebra/PGroupFixedVector.lean` として再実装しかけたが重複ゆえ削除した
        (着手前の grep 漏れ)。残りは「`V^N` が `kG`-部分加群 (`N ⊴ G`) + 単純性」だけ。
  - [x] **Navarro (4.7)** 「`K ∩ C_G(O_p(G)) = ∅` なら `K̂` は中心指標に殺される」— 完了
        (`Algebra/ClassSumOffCentralizer.lean`)。
        🎯 `pi_sum_ite_single_eq_zero` (**一般形**: `N`-共役不変で `C_G(N)` を外す任意の
        部分集合 `S` について `π(Σ_{x∈S} x) = 0`) /
        🎯🎯 `pi_classSum_eq_zero_of_notMem_centralizer` (`S` = 類の場合 = 原文の (4.7)) /
        🎯 `blockCharacter_classSumCenter_eq_zero`。
        論法 = (2.32) で `π(single · 1)` が `N`-共役軌道上定数 ⟹ 軌道長は全て `p` の倍数
        ⟹ 既存 `sum_eq_sum_fixedPoints` で消える。
  - [x] **Navarro (4.14) 第一部** `λ_b^G = λ_b ∘ Br_P` — 完了
        (`Modular/BrauerCorrespondence.lean`)。
        🎯 `mem_centralizer_conj_iff` (`N_G(P)` は `C_G(P)` を保つ) /
        `centralizerTruncClassSum` (= `Br_P(K̂)` を `k[H]` の中で見たもの
        `Σ_{x ∈ K∩H∩C_G(P)} x`) / 🎯 `centralizerTruncClassSum_mem_center` /
        🎯🎯 `pi_truncClassSum_eq_centralizerTrunc` /
        🎯🎯 `blockCharacter_truncClassSumCenter_eq` (`λ_b(Σ_{x∈K∩H} x) = λ_b(Br_P(K̂))`)。
        ⚠ **原文より短い経路を採った**: Navarro は残差を `H`-類に分解し `O_p(H)` に対する
        (4.7) を各類へ適用するが、ここでは `P ⊴ H` (∵ `H ≤ N_G(P)`) ゆえ **`P` 自身**で
        同じ軌道勘定が回る — 上の一般形 `pi_sum_ite_single_eq_zero` に
        `S = {h ∈ H : mk h = K ∧ h ∉ C_G(P)}` を入れて一発。`H`-類分解も `O_p(H)` も不要。
        なお仮説は `P ≤ H ≤ N_G(P)` のみで、`C_G(P) ≤ H` は不要 (次の段で使う)。
        補助: `ClassSumCore.sum_ite_mem_center` (共役不変集合の指示和は中心的) を新設。

  - [x] **Navarro (4.14) 第二部** `λ_b^G` の乗法性 ⟹ **`b^G` は常に定義される** — 完了
        (`Modular/BrauerTruncation.lean` + `Modular/InducedBlockDefined.lean`)。
        * `brauerTrunc P H : k[G] → k[H]` (`C_G(P)` を外す係数を落とす) + `coeff_brauerTrunc` /
          `brauerTrunc_zero/add/smul/one`。
        * `inclusionHom H : k[H] →+* k[G]` (`MonoidAlgebra.mapDomainRingHom`) +
          🎯 `inclusionHom_injective` + `coeff_inclusionHom_of_mem/notMem` /
          🎯🎯 `inclusionHom_brauerTrunc` (`C_G(P) ≤ H` なら既存 `brauerProj P` に一致)。
        * 🎯 `brauerTrunc_mem_center` (中心元の切り落としは中心的; `H ≤ N_G(P)` を使う) /
          🎯🎯 `brauerTrunc_mul_of_mem_center` (**乗法性** — 中心元は `P`-不変ゆえ既存
          `brauerProj_mul_of_invariant` が使え、単射 `inclusionHom` で引き戻す) /
          `brauerTrunc_classSum` (類和では第一部の `centralizerTruncClassSum` に一致)。
        * 🎯🎯 `brauerCenterHom : Z(kG) →ₐ[k] Z(kH)` /
          🎯🎯 `inducedCentralCharacterAlgHom` (= `λ_b ∘ Br_P`) /
          🎯🎯🎯 `inducedCentralCharacterAlgHom_toLinearMap` (**これが Navarro の `λ_b^G` に
          一致** — 両辺線型なので類和基底で比べればよく、第一部がその比較) /
          🎯🎯🎯 `inducedBlockOfNormalizer` (= `b^G`、乗法性の仮説**なし**で構成) /
          🎯 `blockCharacter_inducedBlockOfNormalizer` (`λ_{b^G}(K̂) = λ_b(Br_P(K̂))`)。

**⟹ 段 95 の (4.14) 本体は完了 (2026-08-04)。** `P·C_G(P) ≤ H ≤ N_G(P)` なら誘導 block
`b^G` は常に定義され、その中心指標は `λ_b ∘ Br_P`。
⚠ (4.14) の**後半 2 文** (`B = b^G` ⟺ `P` が `B` のある defect group に含まれる、
および `Br_P(e_B) = Σ_{b^G = B} e_b`) は未着手 — (4.8)/(4.11)/(4.13) に依存する。
第二主定理 ((5.2)) はこれらを使わないので、先に段 96–97 へ進んでよい。

- [ ] **95 続き: `(5.6)`/`(5.7)`** (第二主定理が使う `b^G` の性質)
- [x] **96: 一般化分解数 `d^x_{χμ}`** — 完了 (2026-08-04)。
  - `Modular/BrauerBasis.lean`: **IBr は `p`-正則類関数の基底**。
    🎯 `exists_isConj_pRegularRep` / `brauerCharacterMatrix` (表 `φ(x_j)`) /
    🎯🎯 `eq_zero_of_vecMul_brauerCharacterMatrix` (行の `K` 上一次独立 — `𝒪` 上の既存
    `eq_zero_of_sum_irreducibleBrauerCharacter_ringHom` を
    `IsLocalization.exist_integer_multiples_of_finite` で分母払いして持ち上げる) /
    🎯🎯 `isUnit_det_brauerCharacterMatrix` (正方 `|IBr| = #cl(G°)` + 独立 ⟹ 可逆) /
    🎯🎯🎯 `existsUnique_coeff_irreducibleBrauerCharacter`。
  - `Modular/GeneralizedDecomposition.lean`: **Navarro (5.1)**。
    🎯 `isConj_mul_of_isConj` / 🎯🎯🎯 `existsUnique_generalizedDecomposition` /
    `generalizedDecompositionNumber` (= `d^x_{χφ}`) /
    🎯 `sum_generalizedDecompositionNumber` / 🎯 `eq_generalizedDecompositionNumber`。
  - ⚠ **原文より一般**: `x` が `p`-元であることは使っていない (`H = C_G(x)` でありさえすれば
    `y ↦ χ(xy)` は `H`-類関数)。原文は `χ|_H` を `Irr(H)` に分解し `x ∈ Z(H)` がスカラー
    作用することを使う経路で、そちらは `d^x_{χφ} ∈ ℤ[ζ]` (整性) も出す。
    **整性は本 commit では出していない** — 必要になった段で別途。
- [x] **97: 🎯🎯🎯 第二主定理 `(5.2)` — 完了 (2026-08-04)** — `x` が `p`-元、`b ∈ Bl(C_G(x))`、`χ ∈ Irr(G)` が
      `Irr(b^G)` に属さないなら、全ての `φ ∈ IBr(b)` について `d^x_{χφ} = 0`。
      `Modular/SecondMainTheorem.lean` の `generalizedDecompositionNumber_eq_zero` (axiom-clean)。
      ((5.3)–(5.7) + (5.2) 本体すべて完了。(3.31) は下記のとおり形式化不要と判定済。)

  **依存関係 (2026-08-04 に原文 pp.100–104 を精読して確定)**:
  ```
  (5.3) J(R) ⊆ J(A)  [R ⊆ Z(A), A は R 上有限]      ← 純粋な環論
     └→ (5.4) f 冪等元, x ∈ f(𝒪G)f, x* = f*  ⟹ x は f(𝒪G)f で可逆
           └→ (5.5) λ_B(x*) = 1 ⟹ ∃ y ∈ f_B Z(𝒪G), xy = f_B
                 └→ (5.6) b^G = B ⟹ ∃ w ∈ 𝒪G: (a) (1-f_B)f_b = (1-f_B)w,
                       (b) w = f_b w f_b, (c) H は w を中心化, (d) supp w ⊆ G∖H
                       └→ (5.7) [Isaacs] C_G(h_p) ⊆ H, χ ∉ B ⟹ χ(f_b h) = 0
                             └→ 🎯 (5.2)
  ```
  - [x] **(5.3)** — 完了 (`Algebra/JacobsonCentralSubring.lean`)。
        🎯 `algebraMap_mem_ringJacobson`。⚠ **原文と違う証明を採った**: 教科書は単純
        `A`-加群 `M` に Nakayama を当てて `M·J(R) < M` を出すが、ここでは `A` 自身に
        当てる — `r ∈ J(R)`, `y ∈ A` に対し `u = y·r+1` と置くと `A = A·u + r·A` なので
        Nakayama で `A·u = A`、すなわち `u` は左可逆。これは `Ideal.mem_jacobson_iff`
        そのものなので、単純加群を量化せずに済む。
  - [x] **(5.3) の局所版** — `algebraMap_maximalIdeal_mem_ringJacobson` (`𝔪·A ⊆ J(A)`)。
        (5.4) が使う形。
  - [ ] **(5.4)** — ⚠ **真の隘路 = `𝒪G` の block 冪等元 `f_b` (`FG` の `e_b` の持ち上げ)**。
        **実測 (2026-08-04)**:
        * repo に無い。既存 `Algebra/BlockIdempotent.lean` は体 `k` 上の
          `π : A → ∏Matrix` 設定で、`𝒪` 側の持ち上げは未整備。
        * **mathlib にも無い**。`RingTheory/Idempotents.lean` の持ち上げ
          (`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` /
          `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`) は**核が冪零**の場合のみ。
          `𝒪G → FG` の核 `𝔪·𝒪G` は冪零でない。
        * **adic 完備性も使えない**: `IsPModularSystem` は `HenselianLocalRing` しか要求せず、
          実際 `𝓞_ℂ_[p]` は値群が可除ゆえ **`𝔪² = 𝔪`** で、`𝔪`-adic 完備性は
          `𝔪 = 0` を意味してしまう。Newton 反復は使えない。
        * mathlib の `HenselianLocalRing` は**単根の持ち上げのみ** (`TFAE` の 3 条件とも
          root lifting の言い換え)。**Hensel の因数分解補題**も「henselian 局所環上の
          有限代数は局所環の積」も無い。
        - [x] **冪等元の持ち上げ = 根の持ち上げに帰着した** (`Algebra/IdempotentLift.lean`)。
              🎯 `isUnit_two_mul_sub_one_of_sub_mem` / 🎯🎯 `exists_isIdempotentElem_sub_mem` /
              🎯 `eq_of_isIdempotentElem_of_sub_mem` (一意性) /
              🎯 `existsUnique_isIdempotentElem_sub_mem`。
              近似冪等元 `c` (`c² - c ∈ I`) は `X² - X` の**単根**である —
              `(2c-1)² = 4(c²-c) + 1 ≡ 1 (mod I)` なので導関数 `2c-1` は法 `I` で自分自身が
              逆元。よって mathlib の `HenselianRing.is_henselian` がそのまま使える。
              完備性は一切不要。一意性は `d = e - f` が `d³ = d` を満たし
              `d ∈ I ≤ J(R)` から `d² - 1` が単元になることから。
        - [ ] **残る隘路 = `HenselianRing C (𝔪·C)`** (`C = Z(𝒪G)`)。
              `jac` フィールド (`𝔪C ≤ J(C)`) は上の (5.3) 局所版で済んでいるので、
              **欠けているのは `C[X]` の根の持ち上げだけ**。
              一般の henselian `𝒪` については「module-finite な代数は henselian pair」
              (Stacks 09XI / 04GG) が要るが、これは mathlib に無く、単根持ち上げからの
              導出には多変数 Hensel (Bourbaki) が要る**別プロジェクト**。
              ⟹ **`𝒪` が `𝔪`-adic 完備な場合を先に通す** (`ℤ_p`・`W(𝔽̄_p)` は該当。
              `𝓞_ℂ_[p]` は `𝔪²=𝔪` ゆえ該当しないので、その一般化は上の別プロジェクト送り)。
              残る手順:
              - [x] `Algebra/AdicCompletePi.lean`: 🎯 `mem_pow_smul_top_self_iff` /
                    🎯 `mem_pow_smul_top_pi_iff` / 🎯🎯 `isAdicComplete_pi`
                    (有限直積の adic 完備性。mathlib に直積の instance が無かった)。
              - [x] `Algebra/AdicCompletePi.lean` 続き: 🎯 `map_equiv_pow_smul_top` /
                    🎯🎯 `isAdicComplete_of_linearEquiv` /
                    🎯🎯 `isAdicComplete_of_basis` (有限自由加群は完備環上で完備)。
              - [x] `Algebra/CenterGroupAlgebraHenselian.lean`:
                    🎯 `isAdicComplete_centerGroupAlgebra` (類和基底で移送) /
                    🎯 `isAdicComplete_centerIdeal` (mathlib `map_algebraMap_iff`) /
                    🎯🎯 `henselianRing_centerGroupAlgebra` /
                    🎯🎯🎯 `existsUnique_isIdempotentElem_centerGroupAlgebra`
                    (**`Z(𝒪G)` で冪等元が一意に持ち上がる**)。
              - [x] `Algebra/CenterIdempotentLift.lean`: `centerReduceHom` /
                    🎯🎯 `mem_centerIdeal_iff_mapRingHom_eq_zero` (**還元の核 = `I·Z(𝒪G)`**;
                    ⊆ は `I` が `0` に落ちること、⊇ は類和展開の係数が `I` に入ること) /
                    🎯🎯🎯 `existsUnique_isIdempotentElem_mapRingHom_eq`
                    (**`Z(FG)` の冪等元は `Z(𝒪G)` へ一意に持ち上がる** = block 冪等元 `f_B`)。
                    全射性は既存の `Modular/CenterReduction.lean`
                    (`exists_mem_center_mapRingHom_eq`) がそのまま使えた。
  - [x] **(5.4)** — 完了 (`Algebra/CornerInverse.lean`)。
        🎯 `isUnit_one_add_of_mem_ringJacobson` (**非可換環で `1 + J` は単元**;
        mathlib の `Ideal.isUnit_of_sub_one_mem_jacobson_bot` は可換仮定) /
        🎯 `map_maximalIdeal_le_ringJacobson` / 🎯🎯 `exists_corner_inverse`。
        ⚠ **原文と違う証明**: 教科書は `f(𝒪G)f` を単位元 `f` の環と見て (5.3) を当てるが、
        「単位元が `f` の環」の形式化は面倒。代わりに `u = x + (1 - f)` と置くと
        `u - 1 = x - f ∈ 𝔪·𝒪G ⊆ J(𝒪G)` なので **`u` は `𝒪G` の単元**で、
        `f u = u f = x` を確かめれば corner の逆元は `f u⁻¹ f` で済む。corner 環も
        corner に対する (5.3) も不要。
        論法の核は `exists_corner_inverse_of_isUnit` に切り出した (「`u = x + (1-f)` が
        単元なら corner の逆元は `f u⁻¹ f`」)。標数 `p` 版
        `exists_corner_inverse_of_isNilpotent` (`x - f` が冪零) も同時に用意 —
        (5.5) が `Z(FG)` で使う形。
  - [x] **(5.5) の標数 `p` 半分** — 完了 (`Algebra/BlockCornerInverse.lean`)。
        🎯🎯 `exists_corner_inverse_of_blockCharacter_eq_one`:
        `e` が block `c` の冪等元で `λ_c(x) = 1` なら `e x` は corner で両側可逆。
        理由は `e x - e = e(x-1)` を**全ての** block 指標が殺すこと
        (`λ_c` は `λ_c(x)=1` ゆえ、他は `e` を殺すゆえ) ⟹ `hnil` で冪零 ⟹
        前 commit の `exists_corner_inverse_of_isNilpotent`。
  - [x] **持ち上げの原理** — 完了 (`Algebra/CornerInverse.lean` の `Comm` 節)。
        🎯🎯 `exists_corner_inverse_of_approx`: 可換 `A` (𝒪 上有限、𝒪 局所) で
        corner の `w` が `x w ≡ f (mod 𝔪·A)` を満たすなら、corner の**厳密な**逆元が取れる
        ((5.4) が誤差を吸収する)。
  - [x] **中心の還元を中心値の環準同型にした** (`Algebra/CenterIdempotentLift.lean`)。
        🎯 `mapRingHom_mem_center` (係数写像は中心性を保つ — 中心性は
        「係数が共役類上定数」なので明らか) / `centerReduce : Z(𝒪G) →+* Z(FG)` /
        🎯 `mem_centerIdeal_iff_centerReduce_eq_zero`。
        block 指標は `Z(FG)` の元にしか適用できないので、(5.5)–(5.7) にはこの形が要る。
  - [x] **(5.5)** — 完了 (`Algebra/BlockCornerLift.lean`)。
        🎯🎯🎯 `exists_corner_inverse_blockCharacter`:
        `f` が block `c` の冪等元、`x ∈ Z(𝒪G)` が `λ_c(x*) = 1` なら
        `f x` は corner `f Z(𝒪G)` で可逆。
        剰余体での corner 逆元 → 持ち上げると近似逆元 → (5.4) で補正、の 3 段。
        ⚠ `Algebra/CenterIdempotentLift.lean` を「任意の全射 `φ : 𝒪 →+* F` で
        `RingHom.ker φ = I`」にパラメータ化した — `IsLocalRing.ResidueField` は
        `abbrev` でなく `def` なので `𝒪 ⧸ 𝔪` に `Field` instance が付かず、
        block 枠組 (`[Field k]` 要求) と繋がらなかったため。
  - [ ] **(5.5) の仮説について**: `[IsAdicComplete (maximalIdeal 𝒪) 𝒪]` を要求する
        (block 冪等元の持ち上げ由来)。一般の henselian `𝒪` への緩和は Stacks 09XI 待ち。
  - [x] **(5.6)** — 完了 (2026-08-04)。
        `Algebra/SubgroupTruncation.lean` (新設; `H ≤ G` に沿った `R[G]` の分解):
        🎯 `inclusionHom` (`BrauerTruncation` の `[Field k]` 版から一般環へ移設・dedup) /
        🎯 `subgroupTrunc` (係数の `H` への制限) / 🎯 `subgroupTrunc_mem_center` /
        🎯 `mapRingHom_subgroupTrunc` (還元と可換) /
        🎯🎯 `coeff_mul_inclusionHom_eq_zero` (`(G∖H)·H ⊆ G∖H`) /
        🎯 `commute_single_inclusionHom` (`H` は `ι(Z(RH))` を中心化)。
        `Modular/TruncClassSum.lean`: 🎯🎯 `coe_centerTrunc` — **類和基底で定義された
        `centerTrunc` は係数截断そのもの**。これが無いと `λ_b^G` の定義 (基底経由) と
        `f_B` の `H`-部分 (係数経由) が繋がらない。
        `Modular/InducedBlockWitness.lean` (新設):
        🎯 `centerReduce_subgroupTrunc` /
        🎯🎯🎯 `exists_inducedBlock_witness` — `b^G = B` なら `w ∈ 𝒪G` が在って
        (a) `(1-f_B)f_b = (1-f_B)w`、(b) `w f_b = w`、(c) `H` が `w` を中心化、
        (d) `supp w ⊆ G∖H`。
        ⚠ 教科書どおりの証明: `f_B = a - c` (`a` = `H`-部分、`c` = `G∖H`-部分) と割り、
        `b^G = B` が `λ_b(a*) = λ_B(e_B) = 1` を与えるので (5.5) が `a y = f_b` なる
        `y ∈ f_b Z(𝒪H)` を返す。`w = c·ι(y)` が全部を満たす。
        ⚠ 仮説 `b^G = B` は `(blockCharacter B).toLinearMap = inducedCentralCharacter H
        (blockCharacter b).toLinearMap` の形で持つ (`InducedBlock.lean` と同じ idiom)。
  - [x] **(3.13.a)** — 完了 (2026-08-04、`Modular/LatticeBlockIdempotent.lean`)。
        🎯 `eq_zero_or_one_of_isIdempotentElem` (局所環の冪等元は `0` か `1`) /
        🎯 `isIdempotentElem_centralScalar` / 🎯🎯 `centralScalar_eq_zero_or_one` /
        🎯🎯 `apply_eq_zero_of_reduce_centralScalar_eq_zero` (= `χ ∉ B ⟹ L f_B = 0`) /
        🎯🎯 `apply_eq_id_of_reduce_centralScalar_ne_zero` (= `χ ∈ B ⟹ f_B` は恒等) /
        🎯 `baseChange_apply_eq_zero_of_reduce_centralScalar_eq_zero` (= `M f_B = 0`)。
        ⚠ **`f_B = Σ_{χ ∈ Irr(B)} e_χ` を経由しない**。教科書は通常指標の中心冪等元の和として
        `f_B` を書き `X(f_B)` を計算するが、`𝒪`-格子の定式化では `ω_χ(f_B)` が **`𝒪` の冪等元**
        であること 1 点で済む — 局所環ゆえ `0` か `1` で、どちらかは剰余 (= `λ_χ(e_B)`) が決める。
        これが「mod `𝔪` の情報を `𝒪` 上の等式へ持ち上げる」段で、(5.7) が `M f_B = 0` を
        使うところの本体。`λ_χ` が実際にどれかの block 指標であることは段 93 の
        `exists_eq_centralCharacterAlg_of_asAlgebraHom_eq_smul` が与える。
  - [ ] **(5.7)**。`⟨h⟩` の `supp(w)` への軌道が長さ `p` の倍数であること + 固有空間の
        次元比較 (乗算 `s = Σ ω^{-i} w_i` が単射) という組み合わせ論 + 線型代数。
        (5.6) の (b)(c)(d) が軌道勘定に、(a) が最後の `s* = w*` に効く。
        残り部品:
  - [x] **(i) 巡回層への分割** — 完了 (2026-08-04、`Modular/ConjugationLayers.lean`)。
        🎯 `pPart_mem_zpowers_zpow` (`p ∤ k` なら `h_p ∈ ⟨h^k⟩`; `d = gcd(k, ord h)` が `p` と
        素 ⟹ `d ∣ ord h` の `p'`-部分 ⟹ `d ∣ h_p` の指数、Bézout で `kℤ + (ord h)ℤ` に入る) /
        🎯 `dvd_of_commute_zpow` (⟹ `C_G(h_p)` を外れた点の固定部分群は `⟨h^p⟩` の中) /
        🎯 `commute_pPart_conj_iff` / `conjBySetoid` · `conjRep` · 🎯🎯 `conjLevel`
        (軌道代表元へ戻す `h` の指数 mod `p`) / 🎯🎯 `conjLevel_eq` (well-defined) /
        🎯🎯 `conjLevel_conj` (`lev(h x h⁻¹) = lev(x) + 1`) /
        🎯 `conjLayer` (level 集合への制限) + `coeff_conjLayer` /
        🎯🎯🎯 `sum_conjLayer` (`Σ_i w_i = w`) /
        🎯🎯🎯 `conjLayer_conj_smul` (`h • w_i = w_{i+1}`)。
        ⚠ **剰余類の勘定でなく level 関数**で組んだ。教科書は `⟨h^p⟩ mod C_⟨h⟩(x)` の右剰余類を
        並べて `Δ^{h^i}` を作るが、ここでは「軌道代表元へ戻す指数 mod `p`」を直接定義し、
        well-definedness (= 固定部分群 ⊆ `⟨h^p⟩`) だけ示す。層は level 集合そのもの。
  - [x] **(ii) 固有ベクトル `s = Σ ω^{-i} w_i`** — 完了 (2026-08-04、
        `Modular/TwistedLayerSum.lean`)。
        🎯 `eq_one_of_pow_eq_one_expChar` (標数 `p` の体で `p` 乗根は `1` — Frobenius で
        `(a-1)^p = 0`; Navarro の `ω* = 1`) / `pow_mod_eq_pow` · 🎯 `pow_val_add`
        (`p` 乗根は `ZMod p` で冪指数が取れる) / 🎯 `twistedSum` /
        🎯🎯 `conj_smul_twistedSum` (`s^h = ω s`) /
        🎯🎯 `mapRingHom_twistedSum` (`s* = (Σ v_i)*`) /
        `sum_corner` · `conj_smul_corner` · `corner_idem` ·
        🎯 `corner_twistedSum` (`f_b s f_b = s`; 教科書の `w_i → f_b w_i f_b` 差し替え) /
        🎯🎯🎯 `exists_conj_eigen_corner` — **組み立て**: `h` で固定され `f` の corner に等しく
        `C_G(h_p)` を外れた台を持つ `w` から、`h • s = ζ • s` ∧ `f s f = s` ∧ `s* = w*` なる
        `s` を作る。(5.7) の代数側はこれで尽き、残るは加群側だけ。
  - [x] **(iii) `s` の単射性** — 完了 (2026-08-04)。
        `Algebra/GroupAlgebraIdeal.lean`: 🎯 `sum_single_coeff` (群基底での展開) +
        🎯🎯 `mem_groupAlgebraIdeal_iff_mapRingHom_eq_zero` (**`I·R[G]` = 係数還元の核**;
        中心版 `mem_centerIdeal_iff_mapRingHom_eq_zero` の全代数版で、基底が類和でなく `G`
        そのものなので短い)。
        `Algebra/EigenCornerInverse.lean`: 🎯🎯 `exists_corner_inverse_eigen` —
        `c` 中心冪等元・`e` 冪等元・`(1-c)e = (1-c)w`・`s ≡ w (mod 𝔪)`・`e s e = s` から
        `(1-c)s` が corner `f = (1-c)e` で両側可逆。/
        🎯🎯 `eq_zero_of_smul_eq_zero_of_corner_inverse` — `e v = v` かつ `c v = 0` なる `v`
        について `s v = 0 ⟹ v = 0`。
        ⚠ **左加群で書いた** (repo の `Representation` が左作用ゆえ)。教科書は右加群
        (`M f_b`, `vs`) だが、`f_b ∈ Z(𝒪H)` は `h` と可換なので左右どちらでも同じ論法が通る。
        ⚠ 中心元 `1-c` の結合律さばきは補題 `hstep : ((1-c)a)((1-c)b) = (1-c)(ab)` 一本に
        まとめると 3 つの検証 (冪等性・corner 性・差の評価) が各 1 行になる。
  - [x] **(iv) トレースの消滅** — 完了 (2026-08-04、`Algebra/EigenTraceVanishing.lean`)。
        🎯🎯 `trace_eq_zero_of_conj_smul` (`H T = ζ • (T H)` かつ `T` 単射 ⟹ `tr H = 0`) /
        🎯🎯🎯 `trace_idempotent_mul_eq_zero` (= **`χ(f_b h) = 0`**)。
        ⚠⚠ **教科書より遥かに短い経路を採った**。Navarro は「`α` と `ζα` は `h` の固有値として
        同じ重複度を持つ」を示し、固有値を `⟨ζ⟩`-軌道にまとめて和が `0` になると論じるが、
        それは**「`H` と `ζH` が相似」と言っているのと同じ**であり、トレースは相似不変なので
        `tr H = tr(T⁻¹(HT)) = tr(ζH) = ζ · tr H` ⟹ `(1-ζ) tr H = 0` ⟹ `tr H = 0` で終わる。
        **対角化も重複度も軌道の勘定も不要**。
        ⚠ さらに `V = M f_b` への制限も不要にした: 絡み作用素を `T = S + 1 - E`
        (= `V` 上で `S`、その外で恒等) に取ると `(EΦ)T = ζ • (T(EΦ))` が `M` 全体で成立する。
        ⟹ 直和分解 `M = V ⊕ M(1-f_b)` もトレースの制限も要らない。
  - [x] **(5.7) の組み立て** — 完了 (2026-08-04、`Modular/InducedBlockTrace.lean`)。
        🎯🎯🎯 `trace_blockIdempotent_mul_eq_zero` — (5.6) の witness `w` の 4 性質 +
        `C_G(h_p) ≤ H` + `ρ f_B = 0` ((3.13.a)) から **`tr(ρ(f_b) ρ(h)) = 0`**、
        すなわち `χ(f_b h) = 0`。5 部品を `ρ : 𝒪[G] →+* End K M` の設定で結線したもの。
        + 🎯 `commute_inclusionHom_of_forall_single` (`H` の各元が `w` と可換 ⟹ `𝒪H` の像全体が
        可換; `MonoidAlgebra.induction_linear`)。
        ⚠ 単射性補題は `Module A M` 版から **`ρ : A →+* End K M` 版**へ書き換えた
        (`eq_zero_of_apply_eq_zero_of_corner_inverse`) — (5.7) の加群は `K`-空間で `𝒪G` は
        `KG` 経由で作用するので、`Module (MonoidAlgebra 𝒪 G) M` を作る方が遠回りになる。
  ⟹ **(5.7) 完了 (2026-08-04)**。
  - [x] **(3.31)** — **形式化不要と判定 (2026-08-04)**。`ψ(f_b z) = ψ(z)` (`ψ ∈ Irr(b)`),
        `= 0` (otherwise) は、本 repo の定式化では (3.13.a) から `map_mul` 一手で出る:
        `ρ f_b` が `1` か `0` なので `tr(ρ(f_b z)) = tr(ρ(f_b) ρ(z))` がそのまま `tr(ρ z)` か
        `0`。**独立の補題として書くと薄いラッパーになる**ので書かない (CLAUDE.md ラッパー方針)。
        教科書で (3.31) が独立の補題なのは `f_B = Σ e_χ` 経由で `Irr(B)` を経由するため。
  - [x] **通常指標の block を函数にした** — 完了 (2026-08-04、`Modular/BlockOfLattice.lean`)。
        `CenterReduction` に 🎯 `reducedCentralCharacter_smul` + 🎯 `reducedCentralCharacterAlg`
        (`λ_χ` を `Z(FG) →ₐ[F] F` に束ねる; `blockOfCentralCharacter` が AlgHom を要求するため)。
        🎯🎯 `blockOfLattice` (= `χ` の属する block、Navarro (3.11) 経由) /
        🎯 `blockCharacter_blockOfLattice` / 🎯 `blockCharacter_blockOfLattice_mapRingHom` /
        🎯🎯 `reduce_centralScalar_blockIdempotent` (`ω_χ(f_B)^* = δ_{blockOfLattice, B}`) /
        🎯🎯🎯 `apply_eq_zero_of_blockOfLattice_ne` (**`χ ∉ B` ⟹ `L f_B = 0`**) /
        🎯🎯🎯 `apply_eq_id_of_blockOfLattice_eq` (**`χ ∈ B` ⟹ `f_B` は恒等**)。
        ⟹ (5.7)/(5.2) の仮説「`χ ∉ B`」が **`blockOfLattice ≠ B` という等式**として書ける。
  - [x] 🎯🎯🎯 その後 (5.2) 本体。**完了 (2026-08-04)**。
        最短経路の設計 (原文の計算を repo の一意性補題に載せ替える):
        1. `y ↦ χ(f_b x y)` は `H`-類関数 ⟹ `existsUnique_coeff_irreducibleBrauerCharacter`
           で `IBr(H)` に一意展開。(5.7) よりその係数 `c^b` は **0**。
        2. `Σ_{b'} f_{b'} = 1` ⟹ 一意性で `d^x_{χφ} = Σ_{b'} c^{b'}_φ`。
        3. ⟹ 残る唯一の欠落は **分解数の block 対角性**:
           `φ ∈ IBr(b'')` かつ `b'' ≠ b'` なら `c^{b'}_φ = 0`。
        - [x] **block 対角性の第一歩** — `exists_irreducibleBrauerCharacter_eq` を強化
              (2026-08-04)。単純加群が `i` 番目の Brauer 指標を持つとき、**同じ `i`** について
              「中心が `c` 倍で作用するなら `c = centralCharacterAlg π i`」も返すようにした。
              証明中に既に `kG`-線型同値 `e : ρ.asModule ≃ₗ blockModule π i` があるので、
              `BlockOfSimpleModule` の移送パターン 4 行を足すだけ。
              ⚠ **`exists_eq_centralCharacterAlg_of_forall_smul_eq` を別に呼ぶのでは駄目**
              — あちらは別の `∃ i'` を返すので `i = i'` が言えない。同じ `e` から取るのが要。
        - [x] `Representation.quotient` へのスカラー作用の降下 — 完了 (2026-08-04、
              `MinimalSubrepresentation.lean`): 🎯 `quotient_asAlgebraHom_mk` /
              🎯 `quotient_asAlgebraHom_eq_smul`。部分表現版と対で、合成列の帰納法が
              中心指標を保つための両輪。
        - [x] **`exists_decomposition_of_finrank_le` の強化** — 完了 (2026-08-04)。
              結論に「`d i ≠ 0` かつ中心元 `z` がスカラー `c` 倍で作用するなら
              `c = centralCharacterAlg π i z`」を追加。仮説を増やさない**無条件の形**にしたので
              下流はそのまま。帰納法は base で vacuous、step は
              新構成因子側 = 強化した `exists_irreducibleBrauerCharacter_eq`、
              商側 = `quotient_asAlgebraHom_eq_smul` + 帰納法の仮定。
        - [x] ⟹ 🎯🎯🎯 **`centralCharacterAlg_eq_of_decompositionNumber_ne_zero`**
              (`DecompositionNumber.lean`) = **分解数の block 対角性**。
              `exists_decomposition` / `exists_decomposition_trace` にも conjunct を通した。
        - [x] `x ∈ Z(H)` の中心元化 — `GroupAlgebra.single_mem_center_of_forall_commute`
              (2026-08-04)。`H = C_G(x)` なので `single x 1 ∈ Z(𝒪H)`、これを絶対既約格子の
              中心指標に食わせれば `x` は `ψ(x)/ψ(1)` 倍として作用する ((5.2) の step (ii))。
        - [x] **通常指標側の分解** ((5.2) の step (i)) — 完了 (2026-08-04、
              `Modular/OrdinaryDecomposition.lean`)。
              🎯🎯 `exists_ordinaryCharacter_eq` (単純表現は `i` 番目のブロック表現と同じ指標を
              持ち、**同じ `i`** で中心指標も返す — Brauer 側の強化と同型) /
              🎯🎯🎯 `exists_ordinary_decomposition_of_finrank_le` ·
              `exists_ordinary_decomposition` (`tr_V(g) = Σ_i d_i χ_i(g)` + block 対角性)。
              ⚠ 予想どおり **Maschke 補元**で帰納が回り、商もトレース加法性の自作も不要だった。
              仮説は `hkerJ : ker π = Ring.jacobson (K[G])` の**同じ形**で足りる
              (標数 0 では `Ring.jacobson (K[G]) = ⊥` なので Wedderburn 同型を意味する)。
              🎯 `trace_asAlgebraHom_eq_sum` — 分解を **`K[G]` 全体**へ延長 (両辺線型 + 単項式で
              一致)。(5.2) は `χ` を群の元でなく `f_b x y ∈ 𝒪H` で評価するのでこれが要る。
              ⚠ **設計上の要点 (2026-08-04 に判明)**: block 対角性の conjunct は
              「中心元 `z` がスカラー `c` 倍で作用」の形だが、これを **`z = f_{b'}`, `c = 1`**
              で使うのが (5.2) の鍵。`f_{b'} M` の上で `f_{b'}` は恒等なので、その構成因子 `ψ`
              はすべて `ω_ψ(f_{b'}) = 1` を満たす = `ψ ∈ Irr(b')`
              (`reduce_centralScalar_blockIdempotent` で読み替え)。
              `f_{b'}M` 全体には単一の中心指標が無いので「一般の `z`」では使えない — が、
              `z = f_{b'}` だけで十分だった。
        - [x] **中心元による選択** — 完了 (2026-08-04)。
              `BlockRepresentation.lean`: 🎯 `blockRepresentation_asAlgebraHom_smul`
              (ブロック表現は群環の作用全体を担う) /
              🎯🎯 `blockRepresentation_asAlgebraHom_center` (中心元はブロック上で
              `ω_i(z)` 倍)。
              `OrdinaryDecomposition.lean`: 🎯🎯 `trace_asAlgebraHom_center_mul` —
              `tr(ρ(z·a)) = Σ_i d_i · ω_i(z) · tr(blockRep_i(a))`。
              `z = f_{b'}` に取ると `ω_i(f_{b'}) ∈ {0,1}` が `Irr(b')` を切り出す。
        - [x] **二重の中心因子 + 冪等元の値** — 完了 (2026-08-04)。
              🎯🎯 `trace_asAlgebraHom_center_center_mul`:
              `tr(ρ(z·(w·g))) = Σ_i d_i ω_i(z) ω_i(w) χ_i(g)`。
              `z = f_b`, `w = single x 1` に取ると Navarro の
              `Σ_{ψ∈Irr(b)} [χ_H,ψ] (ψ(x)/ψ(1)) ψ(y)` の形になる。
              🎯 `centralCharacterAlg_eq_zero_or_one_of_isIdempotentElem` (体上の冪等元は
              `0` か `1`) — `ω_i(f_b)` が `Irr(b)` の指示関数であること。
        - [x] 🎯🎯 `trace_asAlgebraHom_blockIdempotent_mul` (2026-08-04) —
              `tr(ρ(f·a)) = Σ_{i : ω_i(f) = 1} d_i · tr(blockRep_i(a))`。
              `ω_i(f) ∈ {0,1}` なので和が `Irr(b)` に落ちる、を `Finset.filter` の形で述べたもの。
              (5.2) の最終段が消費する形。
        - [x] 🎯🎯🎯 **(5.2) の核** — 完了 (2026-08-04、`Modular/SecondMainCore.lean`)。
              `blockCoeff` (中心元 `g` が `IBr` 展開に寄与する係数
              `c^g_φ = Σ_i d_i ω_i(g) ω_i(w) D_{iφ}`) / `blockCoeff_add` /
              🎯🎯 `sum_blockCoeff_eq_trace` (`Σ_φ c^g_φ φ(y) = tr(ρ(g·w·y))`; 中心 2 因子 +
              各既約指標の Brauer 分解 + 和の入れ替え) /
              🎯🎯🎯 `blockCoeff_eq_zero_of_vanishing` = **(5.2) の核**。
              ⚠ **`f` と `1 - f` の 2 つの中心冪等元だけで済む**。教科書は暗に
              `Σ_{b'} f_{b'} = 1` と全 block にわたる和を取るが、必要なのは
              `c^1 = c^f + c^{1-f}` の 2 項分解だけ:
              `c^f = 0` ((5.7) + Brauer 指標の一次独立性)、`c^{1-f}_φ = 0` for `φ ∈ IBr(b)`
              (block 対角性) ⟹ `c^1_φ = 0`。block の族を扱わずに済む。
        - [x] **block の commutant はスカラー** — 完了 (2026-08-04、`Algebra/CentralCharacter.lean`)。
              🎯 `exists_smul_id_of_commute_blockAction`: `π` が全射なので `A` の像は第 `i` 成分で
              全行列環を覆い、それと可換な `k`-自己準同型は中心的行列 = スカラー。
              これが `LatticeCentralCharacter.centralCharacter` の要求する **`hEnd`
              (絶対既約性)** の中身。ordinary 側の Wedderburn 成分に `ω^𝒪` を付けるのに要る。
        - [x] **`ω^K` と `ω^𝒪` の橋** — 完了 (2026-08-04、`Modular/OrdinaryLatticeCharacter.lean`)。
              🎯🎯 `centralCharacterAlg_eq_algebraMap_centralScalar`:
              格子の base change が第 `i` ブロックと (作用を絡める `K`-線型同値で) 同一視されるなら
              `ω^K_i = algebraMap ∘ ω^𝒪_i`。
              これで `hblock` の連鎖が繋がる: `D i j ≠ 0` + `j ∈ IBr(b)` ⟹
              `λ_i(e_b) = 1` (block 対角性) ⟹ `ω^𝒪_i(f_b) = 1` (局所環の冪等元) ⟹
              `ω^K_i(f_b) = 1` (本橋)。
              ⚠ 同一視 (`e` と `hint`) は**仮説**にした — Wedderburn 成分に対して供給するのは
              `OrdinaryIrreducibles.wedderburnLattice` 側の別作業。
        - [x] ⚠ **設計の訂正 (2026-08-04)**: `hblock` の連鎖に **`hEnd` は不要**だった。
              `hEnd` (絶対既約性) が要るのは「一般の中心元 `z` に対しスカラーを**作る**」ため
              (`exists_smul_id_of_mem_center_of_absolutelyIrreducible`) だが、(5.2) が使うのは
              `z = f_b` **だけ**で、そのスカラーは block 構造から直接出る
              (`MatrixModule.centralScalar_smul`; `f_b` の像は `K[H]` で中心的なので `π` 経由で
              第 `i` 成分に定数倍として作用する)。あとは既存の整数性補題
              `eq_smul_of_baseChange_eq_smul` に食わせれば `ω^K_i(f_b) ∈ 𝒪` と格子上の作用が出る。
              さらに `ω^K_i(f_b)` は**体の冪等元 = 0 か 1** なので `𝒪` への所属も剰余の一致も自明。
              ⟹ instantiation では `hEnd` も `centralCharacter` も `centralScalar` も経由せず、
              `centralScalar_smul` + `eq_smul_of_baseChange_eq_smul` + 冪等元の 2 値性で足りる。
              (commit 116 の `exists_smul_id_of_commute_blockAction` は汎用 infra として有用だが
              (5.2) の必須経路ではない。)
        - [x] 🎯🎯🎯 **(5.2) の instantiation — 完了 (2026-08-04)**。
              `Modular/SecondMainTheorem.lean` の `generalizedDecompositionNumber_eq_zero`
              (axiom-clean)。仮説の供給元は `hd` = `exists_ordinary_decomposition` /
              `hD` = `trace_wedderburn_eq_sum_decompositionMatrix` /
              `hindep` = `eq_zero_of_sum_algebraMap_irreducibleBrauerCharacter` /
              `hvanish` = (5.7) `trace_blockIdempotent_mul_eq_zero` /
              `hblock` = `centralCharacterAlg_eq_one_of_decompositionMatrix_ne_zero` /
              `hfidem` = `centralCharacterAlg_eq_zero_or_one_of_isIdempotentElem`。
              最後に `eq_generalizedDecompositionNumber` で `blockCoeff … 1 w` を `d^x_{χφ}` と同定。
              新設 leaf 3 つ:
              * `SecondMainBridge.lean` — `𝒪G` / `K[H]` / `𝒪H` の 3 群環を往復する配管
                (`asAlgebraHom_comp_subtype` / `mapRingHom_inclusionHom` /
                `coe_latticeRepresentation_asAlgebraHom` /
                `latticeRepresentation_asAlgebraHom_eq_zero`)
              * `OrdinaryBlockSplitting.lean` — 標数 0 では Wedderburn 同型 `e` の block 表現が
                通常既約 (`blockRepresentation_algEquiv`, `rfl`)、`ker e = J(K[G]) = ⊥`
                (Maschke)、`D` の定義性質を `K` で読む
                (`trace_wedderburn_eq_sum_decompositionMatrix`)
              * `SecondMainWiring.lean` — `hindep` と `hblock`
              ⚠ **`hEnd` は本当に不要だった**。`ω^K_i(f)` が 0 なら `f` は第 `i` 通常既約 →
              その格子 → 剰余 を順に潰し、
              `centralCharacterAlg_eq_of_decompositionNumber_ne_zero` が `0 = ω^k_j(f̄) = 1`
              を出して矛盾、で足りる (`centralScalar` 経路も不要だった)。
              ⚠ `p`-元仮説を使うのは `(xy)_p = x` (`pPart_mul_eq_of_isPElement`) の 1 箇所のみ。
              (旧メモ: 当初の配線見積り)
              旧メモ: 素材は全部揃った。残りは配線のみ:
              `Irr(b)` 上の和 (上記) × `χ_ψ(y) = Σ_φ D_{ψφ} φ(y)`
              (`OrdinaryIrreducibles.trace_eq_sum_decompositionMatrix`) × 分解数の block 対角性
              (`centralCharacterAlg_eq_of_decompositionNumber_ne_zero`) →
              `IBr(b)` 上の和 → 一般化分解数の一意性 (`eq_generalizedDecompositionNumber`) →
              (5.7) の 0 と突き合わせ。
              ⚠ 署名が大きい (通常側の分裂 `π_K` と剰余体側の `π_k` の両方 + 格子 +
              `IsPModularSystem`)。`InducedBlockTrace.lean` と同じ「仮説を全部並べる」方式で
              書くのが素直。
        - [x] (旧計画メモ) 残り = 通常指標側の分解 ((5.2) の step (i))。
              `y ↦ χ(f_{b'} x y)` の `IBr(H)` 展開が `IBr(b')` に台を持つことを言うには、
              `K[H]`-加群の `Irr(H)` への重複度分解 `tr_V(g) = Σ_i n_i χ_i(g)` が要る。
              **設計** (`BrauerDecomposition` の帰納法をそのまま移す):
              次元の帰納 → 極小不変部分空間 `W` (単純) → Maschke 補元 `W'` (repo
              `MaschkeComplement.lean`) → `IsInternal {W, W'}` + mathlib
              `LinearMap.trace_eq_sum_trace_restrict` で `tr_V = tr_W + tr_{W'}` →
              `W` は Wedderburn 分解 `e : K[H] ≃ₐ ∏ Matrix` のどれか
              (`exists_linearEquiv_blockModule`、`ker e = ⊥` ゆえ annihilator 条件は自明) →
              `W'` に帰納。⚠ 商でなく**不変補元**を使うのが要点 (標数 0 なので Maschke が
              効き、SES に沿ったトレース加法性を自作せずに済む)。
              block 対角性の conjunct も同じ帰納法に乗る。
              - [x] **トレースの分裂** — 完了 (2026-08-04、`Algebra/TraceIsCompl.lean`)。
                    🎯 `trace_eq_add_trace_restrict_of_isCompl`: 互いに補な不変部分空間
                    `IsCompl W W'` に沿って `tr f = tr f|_W + tr f|_{W'}`。
                    mathlib の `DirectSum.isInternal_submodule_iff_isCompl` (`Fin 2` 添字) →
                    `LinearMap.trace_eq_sum_trace_restrict` → `Fin.sum_univ_two` の 3 手。
                    帰納法のエンジン。
        - [x] ⟹ (5.2) 本体の組み立て — 完了 (上記 instantiation)
- [ ] **98: `(5.8)` + `(5.13.b,c,d)` (一般化分解数の直交関係) + block orthogonality**

  **設計 (2026-08-04、(5.2) landing 直後に確定)**。(5.8) は「`χ ∈ Irr(B)` なら `d^x_{χφ}` の台は
  `⋃_{b^G = B} IBr(b)` に入る」= (5.2) の対偶を block の族に渡したもの。2 段で組む:

  - [x] **(a) (5.2) の block 形 — 完了 (2026-08-04、`Modular/SecondMainBlockForm.lean`)**。
        🎯 `generalizedDecompositionNumber_eq_zero_of_inducedBlock`。witness `w` は
        `exists_inducedBlock_witness` (= (5.6)) が `b^G = B` から出し、`f_b` の `K` 側・
        剰余体側の化身は `centerReduce` が出す。`φ_j ∈ IBr(b)` は
        `Quotient.mk (blockSetoid …) j = b` の形。
  - [x] **(b) 🎯🎯 (5.8) 本体 — 完了 (2026-08-04)**。
        `generalizedDecompositionNumber_eq_zero_of_blockOfLattice`。
        消滅仮説を「`χ` のブロック ≠ `b^G`」に置換。(3.13.a)
        `apply_eq_zero_of_blockOfLattice_ne` が格子側の消滅を出し、新補題
        `asAlgebraHom_eq_zero_of_latticeRepresentation` (格子は `K` 上張るので周囲も潰れる、
        `Submodule.IsLattice.span_eq_top`) で周囲空間へ持ち上げて (a) に食わせる。
        予告どおり **`hEnd` は (b) で初めて要る** (`blockOfLattice` の定義が使う)。
  - [x] (c) 教科書の (5.8) の**和の形** — 完了 (2026-08-05)。
        `sum_generalizedDecompositionNumber_inducedBlockOfCentralizer`。
        実装上は「和の入れ替え」でなく `Finset.filter` + `Finset.sum_filter_of_ne` で済んだ
        (`IBr(b)` の分割を明示的に扱う必要がない)。
        そのために新設した 2 つの土台:
        * `InducedBlockCentralizer.lean` — **`b^G` は側条件なしで定義される**。
          Brauer の定理 (`inducedBlockOfNormalizer`) の `P C_G(P) ≤ H ≤ N_G(P)` は
          `P = ⟨x⟩`, `H = C_G(x)` で全部成立 (`isPGroup_zpowers_of_isPElement` /
          `zpowers_le_centralizerOf` / `centralizer_zpowers_le_centralizerOf` /
          `centralizerOf_le_normalizer_zpowers`) ⟹ 🎯 `inducedBlockOfCentralizer`。
        * `BlockIdempotentLift.lean` — `Z(kG)` の block 冪等元を `Z(𝒪G)` へ持ち上げ
          (`exists_isIdempotentElem_blockCharacterPi_eq_single` = Navarro の `f_B`)。
        ⟹ 消滅定理 `..._eq_zero_of_inducedBlockOfCentralizer_ne` は
        「`φ_j` の block の誘導 ≠ `χ` の block」だけを仮説にする最終形になった。
  - [ ] **段 98 の残り = (5.10)/(5.11)/(5.12)/(5.13)**。`Irr(B)` の**族**と類関数の
        `B`-部分 `θ_B`、第二直交関係、`p`-section が要る。(5.8) より重い足場。
        ⚠ BS 本証明 (段 102) が直接引くのは **(5.8) + 第三主定理 (6.7)** なので、
        文書順どおりなら次は段 99 (第三主定理) を先に進める判断もありうる。
    - [x] **前提 1: `hEnd` (絶対既約性) の証明** — 完了 (2026-08-05、`LatticeBaseChange.lean`)。
          `BlockOfLattice` / `OrdinaryLatticeCharacter` が仮説で担いでいた同一視
          `K ⊗_𝒪 L ≃ₗ[K] V` を `latticeBaseChangeEquiv` で構成 (基底を
          `Module.Basis.baseChange` と `Module.Basis.extendOfIsLattice` で突き合わせ)、
          `exists_smul_id_of_commute_blockAction` を転送して
          🎯 `exists_smul_id_of_commute_baseChange` = `hEnd`。
          ⚠ 要点: `𝒪G` の像だけでは足りず、単項式から `K`-線型性で `K[G]` 全体へ広げる帰納。
    - [x] **前提 2: `blockOfIrr`** — 完了 (2026-08-05、`BlockOfIrreducible.lean`)。
          🎯 `blockOfIrr e i : Bl(G)` = **`χ_i` のブロック** (Navarro (3.11))。
          `nontrivial_of_isLattice` (非零空間の格子は非零) で `[Nontrivial L]` も供給。
          ⟹ `Irr(B) = {i | blockOfIrr e i = B}` が定義可能。
    - [x] **前提 3: 類関数の `B`-部分 `θ_B`** — 完了 (2026-08-05)。
          ⚠ **内積は使わなかった**。`K` は抽象的な分数体なので共役が無く内積が書けないが、
          Navarro の `θ_B = Σ_{χ ∈ Irr(B)} [θ,χ] χ` は「`Irr(G)` 展開の `Irr(B)` 部分」と
          読めば内積抜きで定義できる。
          * `OrdinaryBasis.lean` (新設) — 指標表が可逆正方行列なので類関数は `Irr(G)` に
            一意展開 (🎯 `existsUnique_coeff_ordinaryCharacter` / `ordinaryCoeff`)。
            `BrauerBasis` の標数 0 版。
          * `BlockOfIrreducible.lean` — 🎯 `blockPart` = `θ_B`、`blockPart_eq_of_isConj`
            (類関数性)、🎯 `sum_blockPart` (`Σ_B θ_B = θ`, `Finset.sum_fiberwise`)。
    - [x] **前提 4: `p`-section `S(x)`** — 完了 (2026-08-05、`PSection.lean`)。
          🎯 `mem_pSection_iff` (`u ∈ S(x)` ⟺ `∃ y ∈ C_G(x)` `p`-正則で `u ~ xy`) と
          🎯 `forall_pSection_iff` (類関数が `S(x)` 上で消える ⟺ 全ての `p`-正則
          `y ∈ C_G(x)` で `f(xy) = 0`)。(5.10) の仮説を一般化分解数が見る形に翻訳する。
    - [x] 🎯🎯🎯 **(5.10) 本体 — 完了 (2026-08-05、`BlockPartVanishing.lean`)**。
          `blockPart_eq_zero_of_forall_pSection`。`θ` が `S(x)` 上で消えるなら `θ_B` も消える。
          `θ_B(xy) = Σ_φ (Σ_{χ∈Irr(B)} c_χ d^x_{χφ}) φ(y)` に落とし、
          消滅 + `IBr(C_G(x))` の一次独立性で `Σ_{χ∈Irr(G)} c_χ d^x_{χφ} = 0` を得て、
          (5.8) が和の片割れを潰す (φ のブロックが `B` を誘導するか否かで場合分け)。
          ⚠ (5.8) を `σ = wedderburnRepresentation e i` で使うと消滅条件がちょうど
          `blockOfIrr e i` になる — `blockOfIrr` の定義がそう作ってあるのが噛み合わせの要点。
          ⚠ `Σ_B θ_B = θ` (`sum_blockPart`) は結局使わなかった (係数レベルで直接分離できた)。
    - [x] 🎯🎯 **(5.11) block orthogonality — 完了 (2026-08-05)**。
          `sum_character_blockOfIrr_eq_zero`。(5.10) を `θ = Σ_χ χ(h⁻¹) χ` に適用するだけで、
          追加物は `isConj_pPart` (共役元の `p`-部分は共役) のみだった。
    - [x] **`p`-section の類代表の完全性 — 完了 (2026-08-05)**。
          `mem_pSection_iff` (全射性) + `isConj_centralizer_of_isConj_mul` (単射性、
          `p`/`p'` 分解の一意性) で「`{x y_i}` が `S(x)` 内の `G`-類をちょうど 1 回ずつ走る」。
    - [ ] (5.12)/(5.13) 本体。(5.13) は一般化分解数の直交関係、(5.12) は `|G|` の分解。
          BS 本証明が引くのは (5.8) + 第三主定理なので優先度は下。
    - [ ] ⟹ **段 98 の主要部 ((5.8)/(5.10)/(5.11)) は完了**。次は段 99 = 第三主定理 (6.7)。
  - [ ] (5.10)/(5.11)/(5.12)/(5.13) は `Irr(B)` の**族**と類関数の `B`-部分 `θ_B`、
        第二直交関係、`p`-section が要る。(5.8) より重い足場なので後回し。
- [ ] **99: 🎯 第三主定理 `(6.7)`** — Okuyama の証明 ((6.1)–(6.6) 経由、非常に一般な形)

  **原文精読の結果 (2026-08-05)**: (6.7) は (6.6) (Okuyama) の系で、`χ = 1_G`, `χ_H = 1_H` が
  それぞれの主ブロックで height 0 であることから出る。(6.6) は **height / defect** と
  (3.24)/(3.20)/(3.22.a)/(6.5) を要求する — つまり (6.7) を Okuyama 経由で通すと
  height 理論一式が前提になる (重い)。

  **⚡ 分割案 (2026-08-05 に発見)**: 応用が実際に使う **「`b_0^G = B_0`」の向きだけなら
  height 抜きの短い証明がある**。`b^G` は `λ_b ∘ Br_P` で定義されるので:
  * 主ブロックの中心指標は**添加写像** (`λ_{B_0}(K̂) = |K|*`, `λ_{b_0}(Ĉ) = |C|*`)
    — 自明表現の中心指標がまさに添加写像だから。
  * ⟹ `λ_{b_0}^G(K̂) = λ_{b_0}(Br_P K̂) = |K ∩ C_G(P)|*`
  * ⟹ `b_0^G = B_0` ⟺ `|K ∩ C_G(P)| ≡ |K| (mod p)` (全ての `G`-類 `K` で)
  * これは **`P` が `K` に共役で作用し、固定点が `K ∩ C_G(P)`、軌道は `p`-冪サイズ**
    という数え上げそのもの = mathlib の `IsPGroup.card_modEq_card_fixedPoints`。

  - [x] (a) **主ブロックの定義** — 完了 (2026-08-05、`PrincipalBlock.lean`)。
        `augmentation k` (一般の可換環上) / `principalCentralCharacter` = `ε|_{Z(kG)}` /
        🎯 `principalBlock` / 🎯 `principalCentralCharacter_classSumCenter` (`λ_{B_0}(K̂) = |K|·1`)。
        ⚠ **特殊化債務は同日中に解消** (ユーザー指示): `OddOrder.Algebra.augmentation` を
        任意の可換環 `(R) (G)` へ一般化し、呼び出し側 3 file (~30 箇所) を `augmentation ℤ G`
        形へ更新。さらに **`CenterSimplesOrbit.aug` が `principalCentralCharacter` と完全に
        同一だった**ことが判明したので、自前定義を全て削除して `aug` を使う形に統一
        (`aug` 自身も `Algebra.augmentation` 経由に再定義)。
        ⟹ 群環の添加写像は repo 全体で 1 定義。
        ⚠ **教訓**: 「repo に無い」と判断する前に、記法 (`MonoidAlgebra.lift _ _ _ 1`) と
        概念名 (`aug`) の**両方**で grep すること — 今回 `augmentation` だけで grep して
        `aug` を見落とした ([[grep-concept-names-not-book-notation]] の再発)。
  - [ ] (b) **🎯 `b_0^G = B_0`** (第三主定理の易しい向き)。
    - [x] **数え上げ — 完了 (2026-08-05、`ClassCentralizerCount.lean`)**。
          🎯 `card_conjClass_modEq_card_centralizer`: `|K| ≡ |K ∩ C_G(P)| (mod p)`。
          `P` の共役作用の固定点が `K ∩ C_G(P)` (`mem_fixedPoints_conjClassCarrier_iff`) +
          `IsPGroup.card_modEq_card_fixedPoints`。
    - [x] 🎯🎯🎯 **配線 — 完了 (2026-08-05、`ThirdMainEasy.lean`)**。
          `inducedBlockOfNormalizer_principalBlock`: `P C_G(P) ≤ H ≤ N_G(P)` なら
          **`b_0^G = B_0`** (axiom-clean)。⚠ **height 理論を一切使っていない**。
          補助: `aug_centralizerTruncClassSumCenter` (`λ_{b_0}(Br_P K̂) = |K ∩ H ∩ C_G(P)|·1`) /
          `card_filter_centralizer_eq` / `card_filter_conjClass_eq`。
          (使った既存補題:)
          * `inducedCentralCharacterAlgHom_toLinearMap` + `inducedCentralCharacter_classSumCenter`
            ⟹ `λ_b^G(K̂) = λ_b(truncClassSumCenter H K)`
          * `blockCharacter_truncClassSumCenter_eq` (= Navarro (4.14) 前半) ⟹
            `λ_b(trunc) = λ_b(centralizerTrunc)` — `H`-切断でなく `C_G(P)`-切断で読める
          * `blockCharacter_principalBlock` ⟹ `b = b_0` なら `λ_b = aug`
          * `aug_classSumCenter` の `H` 版 ⟹ `aug(centralizerTrunc) = |K ∩ C_G(P)|·1`
          * `CharP.natCast_eq_natCast` で上の合同式を `k` の等式に
          * `Z(kG)` の類和基底 (`centerBasis`) 上で 2 つの AlgHom が一致 ⟹
            `blockOfCentralCharacter` の一意性 (`eq_blockOfCentralCharacter`) で結論。
  - [x] 🎯🎯🎯 **(c) 逆向き (`b^G = B_0 ⟹ b = b_0`) — 完了 (2026-08-05、段 154)**。
        **⚠ BS/Z\* の spine が実際に使うのはこの向き**
        (2026-08-05 に原文 p.145 (7.7) で確認): `χ ∈ Irr(B_0)`, `u` が `p`-元のとき
        `χ(uw) = Σ_{μ ∈ IBr(b_0)} d^u_{χμ} μ(w)` — (5.8) の和が `b_0` の項だけに潰れる、
        という主張なので、他の `b` を**排除**する逆向きが要る。
        - **Okuyama 経路 ((6.6)) の前提を精読 (2026-08-05)**: (6.3)–(6.6) は Chapter 2 の
          `~` 関数と Lemma (2.15)、Chapter 3 の (3.20)/(3.21) 付値/(3.22)/(3.24) height を
          使う。**defect group と height の理論一式**が前提になる (重い)。
        - **⚠⚠ 訂正 (2026-08-05): 近道はあった — Külshammer 経路** (原文 p.128 で発見)。
          Navarro 自身が (6.14) の直後に明記している:
          「As we will see in the Problems, this gives an **alternative proof of the third main
          theorem** (for subgroups `Q C_G(Q) ⊆ H ⊆ N_G(Q)`)」。
          ⟹ **Okuyama / height / `~` 関数 / Brauer の指標判定法 (誘導定理) を一切通らない**。
          しかも BS が使うのは `Q = ⟨t⟩` (`t` は involution)、`H = C_G(t) = C_G(Q)` なので
          仮説 `Q C_G(Q) ⊆ H ⊆ N_G(Q)` はそのまま成立する。
          **経路**:
          * 🎯 **(6.14) Külshammer の公式** — **骨格完了 (2026-08-05、`Modular/KulshammerFormula`)**:
            `pRegularSum_eq_sum_classSum` (`Ĝ⁰ = ∑_{C p-正則類} Ĉ`) と
            🎯🎯🎯 `coeff_pElementSum_mul_pRegularSum`
            (**`(Ĝ_p·Ĝ⁰)(x_C) = ∑_B λ_B(Ĝ⁰)·e_B(x_C)`** — (4.23) は `z` について加法的なので
            類和ごとに適用して足し直すだけ)。
            [x] 🎯🎯🎯🎯 **(6.14) 完了 (2026-08-05)**:
            `coeff_pElementSum_mul_pRegularSum_principalBlock` —
            **`(Ĝ_p·Ĝ⁰)(x_C) = |G⁰|*·e_{B₀}(x_C)`**。
            ⚠ `λ_B(Ĝ⁰) = 0` は仮説 `hvanish` としてパラメータ化 (証明済の
            `blockCharacter_blockOfIrr_pRegularSum_eq_zero` を各ブロックに適用する側は
            「B に属する既約 χ を取る」段が要るので呼び出し側に置く)。
            `|G⁰|* e_{B₀} = π(Ĝ_p · Ĝ⁰)`、すなわち
            `p`-正則な `g` で `e_g = |G⁰|*⁻¹ |{(x,y) ∈ G_p × G⁰ : xy = g}|*`、`p`-singular で `0`。
            (`π : Z(FG) → Z(FG)` は `p`-正則類へ切り詰める線型射影。)
          * [x] **Problem (6.1) 完了 (2026-08-05、`GroupTheory/PFactorPairCount.lean`)**:
            🎯🎯 `card_pFactorPairs_modEq_centralizer` —
            `|Ω(g)| ≡ |Ω(g) ∩ (C_G(Q) × C_G(Q))| (mod p)`。
            `Q` が `Ω(g) = {(x,y) : x は p-元, y は p-正則, xy = g}` に**同時共役**で作用
            (`mulActionPFactorPairs`; `g ∈ C_G(Q)` を使うのは
            `(uxu⁻¹)(uyu⁻¹) = ugu⁻¹ = g` の 1 箇所)、固定点は両成分が `C_G(Q)` の対
            (🎯 `mem_fixedPoints_pFactorPairs_iff`)。`ClassCentralizerCount.lean` と同じ型紙。
            ⚠ (6.14) 本体より**下流**だが自己完結なので先行 landing した。
          * [x] 🎯 **`|G⁰| ≡ |C_G(Q)⁰| (mod p)` 完了 (2026-08-05、`PFactorPairCount`)**:
            `card_pRegular_modEq_centralizer` (固定点 = `C_G(Q)⁰`)。Problem (6.1) と対の正規化。
          * [x] **数え上げ側 完了 (2026-08-05)**: `Algebra/PElementSumCount.lean` —
            🎯🎯 `coeff_pElementSum_mul_pRegularSum` (**`(Ĝ_p·Ĝ⁰)(g) = |Ω(g)|`**)、
            支持 `coeff_pElementSum_mul` / `pFactorPairsEquivPElement` (分解は p-部分で決まる)。
            さらに `pFactorPairsSubgroupEquiv` (`Ω_H(g) ≃ Ω_G(g) ∩ (H×H)`) /
            `pRegularSubgroupEquiv` (`H⁰ ≃ G⁰ ∩ H`) で部分群内部の数え上げと同定
            (`PFactorPairCount.lean`)。
          * [x] 🎯🎯🎯 **`Br_Q(e_{B₀}) = e_{b₀}` 完了 (2026-08-05、
            `Modular/KulshammerThirdMain.lean`)**。3 本の合同の突き合わせ:
            - 🎯 `card_pRegular_mul_coeff_principalBlock` = **(6.14) の数え上げ形**
              `|G⁰|*·e_{B₀}(g) = |Ω(g)|*` を**任意の `g`** で。(6.14) は類代表 `C.out`
              での主張なので、`Ĝ_p·Ĝ⁰` と `e_{B₀}` がともに中心元 (係数が共役類上一定、
              `coeff_center_of_mk_eq`) で `g` へ移送し、左辺を数え上げ側
              (`GroupAlgebra.coeff_pElementSum_mul_pRegularSum`) に置換。
              仮説 `hweak` も `C.out⁻¹` → `g⁻¹` (指標は類関数、`character_eq_of_isConj`)。
            - 🎯🎯 `eq_of_card_pRegular_mul_eq` = **突き合わせ本体**。ブロックのデータを
              一切担がず**数え上げだけ**で書けた: `|G⁰|*·a = |Ω_G(g)|*` かつ
              `|C_G(Q)⁰|*·b = |Ω_{C_G(Q)}(g)|*` なら `a = b`。
              合同 2 本 (Problem (6.1) + `pFactorPairsSubgroupEquiv` /
              `card_pRegular_modEq_centralizer` + `pRegularSubgroupEquiv`) は標数 `p` で
              等式になり、`p ∤ |G⁰|` (`not_dvd_card_isPRegular`) で約す。
            - 🎯🎯🎯 `coeff_principalBlock_eq_centralizer` =
              **`e_{B₀}^G(g) = e_{b₀}^{C_G(Q)}(g)`** (`Q` が `p`-部分群, `g ∈ C_G(Q)`)。
              上の 2 本の合成。`G` 側と `C_G(Q)` 側で別々の分裂データ (πG/πC) を取るので
              引数は多いが、内容は 3 行。
            ⚠ **`p`-正則性は不要だった** — `g ∈ C_G(Q)` だけで成立する
              (両辺とも `p`-singular では `0` になる)。
            ⚠ `Br_Q` (Brauer 準同型) を新たに定義せず**係数レベルの等式**にした。
              (6.14) の帰結が係数の等式なので、間に定義を挟むと往復が増えるだけ。
          * [x] 🎯🎯🎯 **逆向きへの変換 完了 (2026-08-05、段 154、同 leaf の `Converse` 節)**:
            - `brauerTrunc_eq_of_coeff_eq` — `H = C_G(Q)` では `Br_Q` は台の `H` への
              制限そのもの (`coeff_brauerTrunc` の条件が `y.2` で自明に成立) ⟹
              段 153 の係数等式が `Z(k[G]) →ₐ Z(k[C_G(Q)])` の等式
              **`Br_Q(e_{B₀}) = e_{b₀}`** になる。
            - 🎯🎯🎯 `eq_principalBlock_of_inducedBlockOfNormalizer_eq` —
              `Q` が**可換** `p`-部分群 (BS では `Q = ⟨t⟩` ゆえ自動; `Q C_G(Q) ≤ C_G(Q)`
              に必要) で `b` が `C_G(Q)` のブロック、`b^G = B₀` なら `b = b₀`。
              `b^G = blockOfCentralCharacter(λ_b^G)` は定義なので
              `blockCharacter_blockOfCentralCharacter` で `λ_{B₀} = λ_b ∘ Br_Q`;
              `e_{B₀}` で評価して左辺 `= 1` (`hB`)、右辺 `= λ_b(e_{b₀}) = δ_{b b₀}` (`hBC`)。
            ⚠ **Okuyama (6.6) / height 理論 / `~` 関数 / Brauer の指標判定法を一切通らない**
              — 段 99 の「(c) は重い」という見立ては Külshammer 経路で完全に回避された。
            - [x] **`Q` 可換仮定は除去済 (2026-08-05、段 157)**。
              🎯 `eq_principalBlock_of_blockOfCentralCharacter_eq` (`hQab` なし) を主定理にし、
              `..._of_inducedBlockOfNormalizer_eq` はその系 (`hQab` 付き) にした。
              ⚠ **訂正**: `hQab` は repo 側の特殊化ではなく**書籍の仮説 `Q C_G(Q) ⊆ H` を
              `H = C_G(Q)` に代入したもの** (`Q C_G(Q) ⊆ C_G(Q) ⟺ Q 可換`)。
              `λ_b ∘ Br_Q = λ_b^G` (Navarro (4.14)) の同定にしか要らない。
            - [x] 🎯🎯🎯 **債務完済 (2026-08-05、段 158-161)**:
                `H = C_G(Q)` 固定 → 一般 `Q C_G(Q) ≤ H ≤ N_G(Q)`。
              - [x] **第 1 段 = 数え上げ側 完了 (2026-08-05、段 158)**:
                `card_pFactorPairsMem_modEq_centralizer` (`|Ω_H(g)| ≡ |Ω_{C_G(Q)}(g)|`) /
                `card_pRegularMem_modEq_centralizer` (`|H⁰| ≡ |C_G(Q)⁰|`)。
                ⚠ `↥H` を新しい ambient 群に立て直す (subgroupOf 移送) 必要はなく、
                `G` の中の `Q` の作用を `H` 制限 subtype に載せ替えるだけで済んだ。
              - [x] **第 2 段 完了 (2026-08-05、段 160)**: `eq_of_card_pRegular_mul_eq_intermediate`
                / 🎯🎯 `coeff_principalBlock_eq_centralizer_intermediate`
                (`e_{b₀}^H(g) = e_{b₀}^{C_G(Q)}(g)`, `g ∈ C_G(Q)`)。
                Külshammer (段 153) は部分群を含まないので `G := ↥H` にそのまま
                instantiate でき、予想どおり subgroupOf 移送は不要だった。
                ⟹ 段 153 と合わせて `e^G` と `e^H` は `C_G(Q)` 上で一致。
              - [x] **第 3 段 完了 (2026-08-05、段 159 `Modular/BlockCharacterOffCentralizer`)**:
                🎯 `pi_classSum_subgroup_eq_zero_of_notMem_centralizer` (`C_G(P)` と交わらない
                `H`-類の類和は `π_H` の核) / 🎯🎯
                `blockCharacter_eq_of_coeff_eq_on_centralizer` (`z, w ∈ Z(k[↥H])` が `C_G(P)`
                上で同係数なら `λ_b z = λ_b w`)。
                ⚠ **engine を再実行しかけたが、既存
                `GroupAlgebra.pi_classSum_eq_zero_of_notMem_centralizer` (= (4.7)) を `↥H` の
                中で呼ぶだけで済んだ** (重複 4 例目、直後に refactor 済)。
              - [ ] ~~第 3 段 = `λ_b ∘ T = λ_b` on `Z(k[↥H])`~~ (旧記述)。
                既存 `pi_truncClassSum_eq_centralizerTrunc` は `G`-類で添字されているので
                そのままでは足りないが、engine の `pi_sum_ite_single_eq_zero` は
                **任意の `Q`-共役不変述語**を取るので、述語を「`H`-類 `L` に属する ∧
                `C_G(Q)` に入らない」に替えるだけで同じ証明が通る。
              - [x] **第 4 段 完了 (2026-08-05、段 161)**: 🎯🎯🎯
                `eq_principalBlock_of_blockOfCentralCharacter_eq_intermediate` /
                `..._of_inducedBlockOfNormalizer_eq_intermediate` (書籍の `b^G = B₀` 読み)。
                ⚠ `H = C_G(Q)` と違い `e_{B₀(H)}` は `C_G(Q)` 上に台を持つとは限らないので
                `Br_Q(e_{B₀(G)}) = e_{B₀(H)}` は**成り立たない**。両者が `C_G(Q)` 上で
                同係数 (段 153+160) であることと段 159 (ブロック指標は `C_G(Q)` 上の係数
                だけで決まる) の 2 本で閉じる。
              ⚠⚠ **2 つの逆向き定理は仮説が非可換**: `H = C_G(Q)` 版 (段 157) は `Q ≤ H` を
              要さない (そこでは `Br_Q(e_{B₀}) = e_{b₀}` がそのまま成立) が、一般版は
              (4.7) を `H` の中で使うので `Q ≤ H` が要る (= `H = C_G(Q)` なら `Q` 可換)。
              **合わせて書籍の範囲 `Q C_G(Q) ⊆ H ⊆ N_G(Q)` を覆い、さらに非可換 `Q` での
              `H = C_G(Q)` も覆う** ⟹ 債務は完済 (むしろ書籍より広い)。
              ⚠ **`b_C` を経由する当初の 6 段案は不要になった** — `Br_Q^{H→C}` を
              代数準同型として作る (= `↥H` を ambient にして subgroupOf 移送する) 必要が
              消え、4 段で閉じる。
              **経路は 2026-08-05 に確定** (原文 p.128-130 の Problems を精読;
              `pages/navarro-p129,130.png` を新規レンダリング)。`C := C_G(Q)` として:
              1. `Br_Q^{H→C} ∘ Br_Q^{G→H} = Br_Q^{G→C}` (係数の切り詰めの合成、自明)
              2. `λ_b ∘ Br_Q^{H→H} = λ_b` (∀`b ∈ Bl(H)`) — 既存
                 `inducedCentralCharacterAlgHom_toLinearMap` を `G := H, H := H` で使う
                 (`inducedCentralCharacter H θ = θ`)。⟹ `Br_Q^{H→C}(e_b) ≠ 0`。
              3. ⟹ ∃`b_C ∈ Bl(C)` で `λ_{b_C} ∘ Br_Q^{H→C} = λ_b` (`hnilC` で
                 `blockCharacterPi` が faithful、冪等元なので値は 0 か 1)
              4. 1+3 ⟹ `λ_{b_C} ∘ Br_Q^{G→C} = λ_b ∘ Br_Q^{G→H} = λ_{B₀(G)}`
              5. 段 157 (`H = C` の場合) ⟹ `b_C = B₀(C)`
              6. **easy half を `H` の中で**: `λ_{B₀(C)} ∘ Br_Q^{H→C} = aug_H = λ_{B₀(H)}`
                 (`|L| ≡ |L ∩ C_H(Q)| mod p`、`Q ≤ H` のみ使う ⟹ `Q` 可換不要)
                 ⟹ `λ_b = λ_{B₀(H)}` ⟹ `b = B₀(H)`
              ⚠ 6 は既存 `inducedBlockOfNormalizer_principalBlock` が `hPH : P ≤ H` を
              担いでいるが、その**証明本体 (`hlam`) は `hPH` を使っていない** ——
              `hlam` を独立の補題として切り出せば `Q` 可換なしで使える。
            ⚠⚠ **特殊化債務 (2026-08-05 記録、`H = C_G(Q)` 固定の分が残存)**:
              `eq_principalBlock_of_inducedBlockOfNormalizer_eq` は書籍 (原文 p.128 の注記
              「for subgroups `Q C_G(Q) ⊆ H ⊆ N_G(Q)`」) より**狭い**:
              * 書籍 = `Q C_G(Q) ≤ H ≤ N_G(Q)` の任意の `H` / 本形式化 = **`H = C_G(Q)` 固定**
              * その結果 **`Q` 可換** (`hQab : Q ≤ C_G(Q)`) を仮定している
                (`Q C_G(Q) ≤ H = C_G(Q)` から強制される。一般 `H` に広げれば自動で落ちる)
              **理由**: Problem (6.1) の固定点が `C_G(Q) × C_G(Q)` の対なので、数え上げが
              比較するのは `G` と `C_G(Q)` であって `H` ではない。一般 `H` では
              `Br_Q(e_{B₀})` は `C_G(Q)` 上に台を持つまま `H` の主ブロック冪等元と
              一致することを別途言う必要があり (`C_G(Q) ⊴ H` を使う一段)、係数比較だけでは
              閉じない。
              **BS への影響なし** (`Q = ⟨t⟩` 巡回・`H = C_G(t) = C_G(Q)`) ゆえ低優先だが、
              CLAUDE.md「特殊化債務はできる限り一般化する」の対象として残す。
          **(6.14) の上流** (これが残る仕事):
          * [x] **(4.22) 完了 (2026-08-05)**: `GroupTheory/SylowContaining.lean`
            (🎯 `card_sylow_containing_modEq_one` — `Q` を含む Sylow の個数 ≡ 1 mod p;
            mathlib `IsPGroup.sylow_mem_fixedPoints_iff` + Sylow 第三定理) と
            `Algebra/PElementSum.lean` (`pElementSum` = `Ĝ_p` / `pRegularSum` = `Ĝ⁰` +
            係数補題、🎯🎯 `pElementSum_eq_sum_sylow` = **`Ĝ_p = Σ_{P ∈ Syl_p} P̂`**)。
            支持: `coeff_subgroupSum` (`N̂` の係数 = 指示関数)、
            `isPGroup_zpowers_of_isPElement` / `isPElement_of_mem_of_isPGroup` を
            `PRegularElement.lean` へ集約 (重複解消)。
          * **Robinson 写像は定義**: `R(x) = Σ_{B} λ_B(x) e_B` (定理でない、原文 p.91)
          * [x] **(4.19) が技術的中心** (原文 p.92 で実測、2026-08-05; **完了は下の
            `residue_ordCompl_mul_sum_sylow_coeff` 項**):
            `(|Ω_{K,L}|/|K|)* = Σ_B λ_B(L̂) a_B(K̂)`
            (`Ω_{K,L} = {(y,z) ∈ K × L : P y = P z}`、`a_B(K̂)` = `e_B` の類和基底での係数)。
            必要な部品:
            - **Burnside の類積公式**を**一般の分裂体 `K` (標数 0) 上で**。
              ⚠ repo には ℂ 上の版が既にある
              (`RepresentationTheory/ClassSumCoefficientFormula.lean` の
              `classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter`、BG App.C 用)
              が、Külshammer 経路は p-modular system の `K` を使うので**係数環の一般化**が要る。
              **⚠ ただし `K`-Wedderburn 設定で直接導出する方が短い見込み (2026-08-05 に検討)**:
              `a_{K,L,M}` を `K̂ · L̂ = Σ_M a_{KLM} M̂` の構造定数とすると
              `ω_i(K̂) ω_i(L̂) = Σ_M a_{KLM} ω_i(M̂)` (中心指標は環準同型)。
              両辺に `χ_i(1) χ_i(z⁻¹)` を掛けて `i` で和を取り、
              `ω_i(M̂) χ_i(1) = |M| χ_i(x_M)` と**第二 (列) 直交関係**
              (既存 `sum_character_inv_mul_character`) を使うと右辺が
              `a_{K,L,cl(z)} · |cl(z)| · |C_G(z)| = a_{K,L,cl(z)} · |G|` に潰れ、
              左辺が `|K||L| Σ_i χ_i(x_K)χ_i(x_L)χ_i(z⁻¹)/χ_i(1)` になる ⟹ Burnside。
              **必要な新規部品は `ω_i(K̂) χ_i(1) = |K| χ_i(x_K)` のみ** — [x] **完了
              (2026-08-05、`Modular/CentralCharacterTrace.lean`)**:
              🎯 `trace_apply_single` (`χ_i(g)` は行列 `e(g)_i` のトレース) +
              🎯🎯 `centralScalar_classSum_mul_character_one`
              (`e(K̂)_i = Matrix.scalar (ω_i(K̂))` のトレースを 2 通りに読む)。
              ⟹ [x] 🎯🎯🎯 **Burnside 本体も完了 (2026-08-05)**:
              `sum_centralScalar_mul_character_eq_card_mul_coeff` (**除算なしの形**)
              `Σ_i ω_i(Ĉ) ω_i(D̂) χ_i(1) χ_i(z⁻¹) = |G| · (Ĉ·D̂)(z)`。
              組み立て 3 段 = (i) `centralScalar_mul` (乗法性) + 上記トレース公式、
              (ii) 和の入れ替え + 既存の第二直交関係、
              (iii) 中心元の係数が類上定数 (既存 `coeff_center_of_mk_eq`) ⟹
              残りは `|cl(z)|·|C_G(z)| = |G|` 倍。
              支持: `eq_sum_single` / `centralScalar_mul_character_one` (任意の中心元版)。
              ℂ 版の係数環一般化は不要だった (共役を一切使わない)。
            - [x] **`Σ_{x ∈ P} χ(x⁻¹) = |P| [χ_P, 1_P]` 完了 (2026-08-05、
              `RepresentationTheory/SumCharacterInvariants.lean`)**:
              🎯 `sum_character_eq_card_mul_finrank_invariants` (`∑_{h∈H} χ_ρ(h) = |H|·dim V^H`)。
              平均化写像は不変部分空間への射影 (mathlib `Representation.isProj_averageMap`)、
              射影のトレースは像の次元 (mathlib `LinearMap.IsProj.trace`)。
              ⟹ `[χ_P,1_P] = dim V^P` が**非負整数**であることが従い、`|P| = p^a` で
              割った後も付値環に留まる (剰余体への還元の要点)。
            - [x] **類の defect `d(K)` 完了 (2026-08-05、`GroupTheory/ClassDefect.lean`)**:
              `classDefect p C = ν_p(|C_G(x_K)|)` / 🎯
              `classDefect_add_factorization_conjugacyClassSize` (**`d(K) + ν_p(|K|) = ν_p(|G|)`**)
              / `ordProj_conjugacyClassSize_mul_pow_classDefect` (`|K|_p · p^{d(K)} = |G|_p`)。
          * [x] 🎯🎯🎯 **(4.23) `R(z) = π(Ĝ_p z)` 完了 (2026-08-05)**。
            - [x] **組合せ半分 完了 (2026-08-05、`GroupTheory/SylowCosetPairs.lean`)**:
              🎯 `factorThroughEquivCosetPairs` (`(x,y) ↦ (xy,y)` が
              `{(x,y) : x ∈ P, y ∈ T, xy ∈ S}` と
              **`Ω = {(u,y) ∈ S×T : u y⁻¹ ∈ P}`** の全単射) /
              `card_factorThrough_eq_card_cosetPairs` /
              🎯 `cosetPairsEquivConj` (`Ω` は Sylow の取り方に依らない)。
              (4.22) と合わせて `π(Ĝ_p L̂)` の `K̂`-係数 = `|Ω_{K,L}|/|K|`。
            - [ ] 指標側 (`R(L̂)` の `K̂`-係数も同じ値) = (4.19) 本体。
              [x] **原始中心冪等元 `e_{χ_i}` 完了 (2026-08-05、
              `Modular/OrdinaryIdempotent.lean`)**: `ordinaryIdempotent` /
              `ordinaryIdempotent_mem_center` (係数が類関数 ⟹ 中心的) /
              🎯🎯 `centralScalar_ordinaryIdempotent` (**`ω_j(e_{χ_i}) = δ_{ij}`**、
              `ω_j(w)χ_j(1) = ∑_g w(g)χ_j(g)` に第一直交関係を食わせるだけ) /
              🎯 `apply_ordinaryIdempotent` (`e(e_{χ_i}) = Pi.single i 1`)。
              ⟹ `a_B(K̂)` の出どころ (`e_B` は `Irr(B)` 上の `e_χ` の和の還元)。
              [x] **完全直交族 + スペクトル分解も完了 (2026-08-05)**:
              `ordinaryIdempotent_mul` / `isIdempotentElem_ordinaryIdempotent` /
              🎯 `sum_ordinaryIdempotent` (`∑_i e_{χ_i} = 1`) /
              🎯🎯 `eq_sum_centralScalar_smul_ordinaryIdempotent` (**`z = ∑_i ω_i(z) e_{χ_i}`**)。
              ⚠ 後者は「**通常側の Robinson 写像は恒等写像**」ということ (`Z(K[G])` が
              半単純だから)。剰余体側で恒等でなくなる分が (4.23) の中身。
              [x] **2 つの中心指標の一致 (2026-08-05、`Modular/CentralScalarBridge.lean`)**:
              🎯🎯 `algebraMap_centralScalar_eq` — 格子側 `ω^L_i` (`𝒪` 値、`blockOfIrr` の定義)
              と Wedderburn 側 `ω^K_i` (`K` 値、Burnside 公式) が `algebraMap` で一致。
              ⚠ **格子側で定義された `blockOfIrr` の分割を Wedderburn 側で読むための橋**。
              証明は「格子は張る」の定型 (既存 `asAlgebraHom_eq_zero_of_latticeRepresentation`
              + `asAlgebraHom_wedderburnRepresentation`)。
              [x] 🎯🎯🎯 **ブロック冪等元の整数性 完了 (2026-08-05、
              `Modular/BlockIdempotentOrdinary.lean`)**:
              `mapRingHom_blockIdempotent_eq_sum` — `e_B` の `Z(𝒪G)` への持ち上げの
              `K[G]` 像は **`∑_{χ∈Irr(B)} e_χ`**。
              (i) `ω^K_i(f)` は体の冪等元 ⟹ `0` か `1`、
              (ii) `= algebraMap(ω^L_i(f))` でその還元がブロック指標 ⟹ `Irr(B)` で `1`、
              (iii) スペクトル分解で組み立て。
              ⟹ **`a_B(K̂)` の正体 = `∑_{χ∈Irr(B)} (χ(1)/|G|) χ(x_K⁻¹)` の還元**。
              ⚠ 途中で `mapRingHom_mem_center` を書きかけたが既存だった
              (`Algebra/CenterIdempotentLift.lean`、任意の環準同型版)。**重複 3 例目** —
              新規補題は必ず概念名で先に grep する。
              [x] **p.93 の段 完了 (2026-08-05、`Modular/BlockSumOverPSubgroup.lean`)**:
              🎯 `sum_pSubgroup_sum_block_character` —
              `∑_{x∈P}∑_{χ∈Irr(B)} χ(y⁻¹)χ(x) = ∑_{χ∈Irr(B)} χ(y⁻¹)χ(1)`。
              ⚠⚠ **原文 p.93 精読の収穫**: (4.19) が使う「弱ブロック直交性」は
              **既に持っている (5.11) `sum_character_blockOfIrr_eq_zero`** そのもの。
              Navarro は Ch.3 版を使うがこちらは Ch.5 で先に landing 済で**循環しない**
              (本 repo の (5.11) は (5.10)←(5.8)←(5.2) 経由、(4.19)/(4.23) 不使用)。
              [x] 🎯🎯🎯 **(4.19) の除算なし版 完了 (2026-08-05、
              `Modular/OmegaBurnside.lean`)**: `sum_pSubgroup_coeff_classSum_mul` —
              **`|G| · ∑_{x∈P} (K̂·L̂')_x = |P| · ∑_χ ω_χ(K̂) ω_χ(L̂') χ(1) · dim V_χ^P`**
              (`L' = L⁻¹`; `Ω_{K,L}` は `(u,y) ↦ (u y⁻¹, y)` でこの和を数える)。
              組み立ては Burnside を `x ∈ P` で和 + `∑_{x∈P}χ(x⁻¹) = |P|·dim V^P` の 2 段。
              ⚠ Navarro は `p^{a-d(K)}` で割って付値環に入れるが、**両辺を整数のまま保つ**
              ので分裂体上で付値の管理なしに成立する。還元は最後にまとめて行う。
              [x] 🎯🎯 **`p`-部分を約した形 完了 (2026-08-05)**:
              `ordCompl_mul_sum_sylow_coeff_classSum_mul` —
              **`|G|_{p'} · |Ω_{K,L}| = ∑_χ ω_χ(K̂) ω_χ(L̂') χ(1) · dim V_χ^S`**
              (`S` = Sylow `p`-部分群)。両辺の `p^a` (`|G|` と `|S|`) を標数 0 で約すと
              **`p` が完全に消えた恒等式**になり、右辺は全項が付値環の中、
              左辺の `|G|_{p'}` は単元 ⟹ **剰余体への還元がそのまま通る形**。
              ⚠ Navarro の `|Ω|/p^{a-d(K)}` 正規化は、これに
              `|K| = p^{a-d(K)}|K|_{p'}` と `ω_χ(K̂)χ(1) = |K|χ(x_K)` を代入したものに
              一致する (検算済)。**本形式化は割り算を導入せずに同じ内容を持つ**。
              [x] 🎯🎯 **`𝒪` への降下 完了 (2026-08-05、
              `Modular/OmegaBurnsideReduction.lean`)**:
              `ordCompl_mul_sum_sylow_coeff_classSum_mul_over` — `K` 上の恒等式は
              **全項が `𝒪` の元の像**なので `FaithfulSMul.algebraMap_injective` で降りる
              (係数は `mapRingHom_classSum` で転送、`ω_χ` は前段の橋、`χ(1)`/`dim V^S` は自然数)。
              ⟹ **剰余体への還元が可能になった**。
              [x] 🎯🎯🎯 **(4.19) 完了 (2026-08-05)**: `residue_ordCompl_mul_sum_sylow_coeff` —
              **`|G|_{p'}* · |Ω_{K,L}|* = ∑_B λ_B(K̂) λ_B(L̂') ∑_{χ∈Irr(B)} χ(1)·dim V_χ^S`**。
              `𝒪` の恒等式を `residue` で落とし、`ω_χ` の還元がブロック指標であることから
              同じブロックの項は同じ係数を持つので `Finset.sum_fiberwise` で括れる。
              ⚠ 教科書の `(|Ω|/|K|)* = ∑_B λ_B(L̂) a_B(K̂)` とは形が違うが同内容
              (`ω_χ(K̂)χ(1) = |K|χ(x_K)` で `|K|` を出し `p^{a-d(K)}` を約すのが教科書の道)。
              **本形式化は割り算を一度も導入せず**、両辺整数のまま `p^a` を約して還元した。
              ⟹ **類の defect `d(K)` は結局 (4.19) の証明には要らなかった**
              (`ClassDefect.lean` は残すが (4.19) の依存ではない)。
              残り = **(4.23) `R(z) = π(Ĝ_p z)` の組み立て**。
              ⚠⚠ **(4.23) の設計判断 (2026-08-05 に検算して確定)**:
              (4.19) の現行形 `|G|_{p'}|Ω_{K,L}| = ∑_B λ_B(K̂)λ_B(L̂')c_B` から (4.23) を出すには
              **`|Ω_{K,L}|` でなく `|Ω_{K,L}|/|K|` が要る**。理由: `Ĝ_p L̂` は中心的なので
              係数は類上定数で `|K|·(Ĝ_p L̂)_{x_K} = |{(x,y) ∈ G_p×L : xy ∈ K}|` となり、
              `|K|` を掛けた形しか出ない ⟹ `p | |K|` のとき還元で情報が消える。
              対策 = `ω_i(K̂)χ_i(1) = |K|χ_i(x_K)`
              (🎯 `centralScalar_classSum_mul_character_one_out`、2026-08-05 landing) で
              `|K|` を露わにし、`|K| = p^{a-d(K)}|K|_{p'}` で `p`-部分を約す。
              ⟹ **類の defect `d(K)` は (4.19) では不要だったが (4.23) では要る**
              (`ClassDefect.lean` はここで使う)。
              ⚠ また `Ĝ_p` と単一 Sylow `Ŝ` の関係は整数レベルでは
              `∑_P |{(x,y) ∈ P×L : xy ∈ K}| = ∑_{x∈G_p} n(x)|{y∈L : xy∈K}|`
              (`n(x) = #{P : x ∈ P} ≡ 1 mod p`) で、`mod p` でしか一致しない。
              (4.23) の係数計算はこの合同を使う。
              [x] 🎯🎯 **鍵の補題 完了 (2026-08-05、`Algebra/PElementSum.lean`)**:
              `sum_sylow_subgroupSum_mem_center` — **`W := ∑_{P∈Syl_p} P̂` は任意の係数環で中心的**
              (共役が Sylow 群を置換する) + `conj_smul_subgroupSum_pointwise` (`g•N̂ = (gNg⁻¹)^`)。
              ⚠ **これで上の問題が回避できる**: `W` は `Ĝ_p` の**整数的な持ち上げ**
              (標数 `p` で一致) でありながら `∑_{x∈P}χ(x) = |P|·dim V^P` の `|P| = p^a` を
              露わに持ち、しかも中心的なので `(W L̂)` の係数は類上定数 ⟹
              `|K|·(W L̂)_{x_K} = |Syl_p|·|Ω_{K,L}|` が**整数のまま**書け、
              **`|K|` の約分を還元の前に整域 `𝒪` の中で行える**。
              残りの配線: (i) `|K|(W L̂)_{x_K} = |Syl_p||Ω|` (類上定数 + `Ω` の Sylow 非依存)、
              (ii) (4.19) の `𝒪` 版と合わせて `|K|` を約す、(iii) `|Syl_p| ≡ 1` で還元。
              [x] **(i) の入口 完了 (2026-08-05)**:
              🎯 `coeff_subgroupSum_mul` (`(N̂·w)(g) = ∑_{x∈N} w(x⁻¹g)`、`Algebra/SubgroupSum`) と
              **`classSum_mul_apply` の係数環一般化** (`ClassSumSections.lean`; ℂ 固定だった
              構造定数公式 `(Ĉ·D̂)(w) = |{(u,v) : u∈C, v∈D, uv=w}|` を `[CommRing k]` へ。
              無償の特殊化債務だった)。
              ⟹ `(P̂·L̂)_u = |{x∈P : x⁻¹u ∈ L}|` から `u ∈ K` で和を取れば
              `|FactorThrough P K L|` になる。
              [x] 🎯🎯🎯 **配線 (i) 完了 (2026-08-05、`RepresentationTheory/SylowSumClassCoeff`)**:
              `sum_class_coeff_sylowSum_mul` —
              **`∑_{u∈K}(W·L̂)(u) = |Syl_p|·∑_{x∈S}(K̂'·L̂)(x)`**。
              ⚠⚠ **数え上げの全単射は不要だった**。両辺を「1 での係数」に書き直す
              (`coeff_classSum_inv_mul_one` / `coeff_subgroupSum_mul_one`、いずれも
              「和を単項式に分解して係数を読む」だけ) と、あとは `W` を展開して
              各 `P̂` を共役で `Ŝ` に戻すだけの**純粋な代数**になる
              (1 での係数は共役不変 = `coeff_conj_smul_one`、`K̂'`・`L̂` は中心的で動かない)。
              当初見込んだ `FactorThrough`/`CosetPairs` の突き合わせ 3 本が丸ごと消えた。
              [x] 🎯🎯🎯 **配線 (ii) 完了 (2026-08-05、`Modular/OmegaBurnsideSylowSum`)**:
              `ordCompl_mul_coeff_sylowSum_mul` —
              **`|G|_{p'}·(W·L̂)(x_K) = |Syl_p|·∑_χ χ(x_K⁻¹) ω_χ(L̂) dim V_χ^S`**。
              `|K|` は**両側に同じ因子として立つ** — 数え上げ側は「中心元の係数は類上一定」
              (`sum_class_coeff_of_mem_center`)、指標側は Burnside
              (`ω_χ(K̂')χ(1) = |K'|χ(x_{K'})`、`|K'| = |K|` は
              `conjugacyClassSize_mk_inv`) — ので、標数 0 の `|K| ≠ 0` で
              `mul_left_cancel₀` するだけ。**`ℚ` に出ない**。
              ⚠ 副産物: `coeff_subgroupSum_mul_one` / `sum_class_coeff_sylowSum_mul` の
              statement 内 `letI := Fintype.ofFinite` を instance binder に変更
              ((4.19) 側と instance を揃えるため; `Fintype` は subsingleton なので
              証明側は `Subsingleton.elim` 1 本で吸収)。
              [x] 🎯🎯 **配線 (iii) 完了 (2026-08-05、`Modular/SylowSumReduction`)**:
              `ordCompl_mul_coeff_sylowSum_mul_over` (`𝒪` へ降下: `χ(x_K⁻¹)` は格子トレース
              `ordinaryCharacter`、`ω_χ(L̂)` は `algebraMap_centralScalar_eq`) と
              🎯🎯 `residue_ordCompl_mul_coeff_pElementSum_mul` —
              **`|G|_{p'}*·(Ĝ_p·L̂)*(x_K) = ∑_B λ_B(L̂)·∑_{χ∈Irr(B)}(χ(x_K⁻¹)·dim V_χ^S)*`**
              (`|Syl_p| → 1` = Sylow 第三定理、`W → Ĝ_p` = (4.22)、
              `∑_{Irr(G)}` は `blockOfIrr` の fiber ごとにまとまる)。
              [x] 🎯🎯🎯 **(4.23) 完成 (2026-08-05、`Modular/SylowSumReduction`)**:
              `coeff_pElementSum_mul_classSum` —
              **`(Ĝ_p·L̂)(x_C) = ∑_B λ_B(L̂)·e_B(x_C)`**。
              最後の 2 段 = p.93 の評価
              (`sum_block_character_mul_finrank_invariants`:
              `∑_{χ∈Irr(B)} χ(y⁻¹)·dim V_χ^S = |G|_{p'}·(∑_{χ∈Irr(B)} e_χ)(y)`。
              `|S|` を掛けて `∑_{x∈S}χ(x) = |S|dim V^S` で開き、p.93 の崩壊
              `sum_pSubgroup_sum_block_character` で `x ≠ 1` を消す。右辺は
              `(e_χ)_y = (χ(1)/|G|)χ(y⁻¹)` と `|G| = |S||G|_{p'}`) と、その `𝒪` 版
              (`ordCompl_mul_coeff_blockIdempotentLift`、
              `mapRingHom_blockIdempotent_eq_sum` で `f_B ↦ ∑_{Irr(B)} e_χ`)。
              ⟹ 両辺に `|G|_{p'}*` が立ち、`p ∤ |G|_{p'}` ゆえ剰余体で約せる。
              ⚠ **`ℚ` に一度も出ない 5 段構成**になった (Navarro は p.92-93 で 2 回割る)。
              ⚠ ブロック冪等元の持ち上げ族 `F`/`F'` と弱ブロック直交性 `hweak` は仮説として
              パラメータ化 ((5.11) は `C_G(g_p)` の分裂データを運ぶので展開すると
              statement が使えなくなる — `sum_pSubgroup_sum_block_character` と同じ設計)。
              `hweak` は `C` が p-正則なら (5.11) から出る
              (`pPart p x_C⁻¹ = 1 ≠ x = pPart p x`)。
              ⚠ **設計上の注意 (2026-08-05 に検算)**: `Ĝ_p` を使って
              `|G|(Ĝ_p L̂)_g = ∑_i ω_i(L̂)(∑_{x∈G_p}χ_i(x))χ_i(g⁻¹)` と書く道もあるが、
              左辺の `|G|` に `p` が残るので還元で潰れる。**単一の Sylow `S` を使って
              `∑_{x∈S}χ(x) = |S|·dim V^S` の `|S| = p^a` を露わにする** Navarro の
              仕掛けが必要 (`Ĝ_p = ∑_P P̂` は `k` でしか成り立たないので `p^a` が見えない)。
              **組み立ての鎖 (p.92-93)**:
              `|Ω_{K,L}| = ∑_{x∈P}|{(y,z) ∈ L×K⁻¹ : yz = x}|`
              → Burnside → `∑_{x∈P}χ(x⁻¹) = |P|[χ_P,1_P]`
              → `|Ω_{K,L}|/p^{a-d(K)} = (1/|C(x_K)|_{p'}) ∑_χ ω_χ(L̂) χ(x_K⁻¹)[χ_P,1_P]`
              (右辺は全部付値環の中!)
              → 還元してブロックごとにまとめ、上の p.93 の段で
              `∑_{χ∈Irr(B)} χ(x_K⁻¹)[χ_P,1_P] = |G|_{p'} (f_B)_{x_K}`
              → `(|Ω_{K,L}|/|K|)* = ∑_B λ_B(L̂) a_B(K̂)`。
              ⚠ **組み立ての設計メモ (2026-08-05)**: (4.23) は係数比較で書くのが素直。
              右辺 `π(Ĝ_p L̂)` の `g`-係数は整数 `|{(x,y) ∈ G_p × L : xy = g}|` の還元
              (割り算不要)。左辺 `Σ_B λ_B(L̂) e_B` の `g`-係数は
              `Σ_B λ_B(L̂) · residue((f_B)_g)` で、`(f_B)_g ∈ 𝒪` は
              `mapRingHom_blockIdempotent_eq_sum` により `K` で
              `Σ_{χ∈Irr(B)}(χ(1)/|G|)χ(g⁻¹)` に等しい。
              ⚠ ここで `ω_i(L̂)` はブロック内で**還元してからしか**一致しないので、
              `Σ_i` にまとめると `(L̂)_g` になってしまい情報が消える (実際に検算した)。
              ブロックごとにまとめたまま `d(K)` の付値で分母を管理する Navarro の
              手順が必要。
          * [x] 🎯🎯🎯 **(3.32) 完了 (2026-08-05)** — `λ_B(Ĝ⁰) = 0` (`B ≠ B₀`)。
            [x] **`λ_{B₀}(Ĝ⁰) = |G⁰|*` 完了 (2026-08-05、`Modular/PRegularSumBlock`)**:
            🎯 `blockCharacter_principalBlock_pRegularSum` (`λ_{B₀}` = augmentation) +
            `pRegularSum_mem_center` / `pElementSum_mem_center` (`Ĝ⁰`・`Ĝ_p` は任意の可換係数環で
            中心的 — p-正則性・p-元性は位数だけで決まるので共役不変) +
            🎯 `centralScalar_pRegularSum_mul_character_one`
            (**`ω_χ(Ĝ⁰)·χ(1) = ∑_{g∈G⁰} χ(g)`**)。
            ⚠⚠ **(3.32) の原文を確定 (2026-08-05、ページ画像
            `references/navarro/pages/navarro-p073.png`。text は OCR 崩壊で読めなかった)**:

            > (3.32) LEMMA. If `χ ∈ cf(G)`, `u_χ = ∑_{g∈G⁰} χ(g⁻¹)g` and `B ∈ Bl(G)`, then
            > `u_χ f_B = |G|_{p'} ∑_{ψ∈Irr(B)} ([χ̃,ψ]/ψ(1)) e_ψ = u_{χ_B}`.

            **和は p-正則元上**である点が肝 (`Ĝ`ではなく`Ĝ⁰`)。`χ = 1_G` を入れると
            `u_1 = Ĝ⁰` で、`1_G ∈ Irr(B₀)` ゆえ `(1_G)_{B₀} = 1_G` ⟹ **`Ĝ⁰ f_{B₀} = Ĝ⁰`**。
            そこから `λ_B(Ĝ⁰) = λ_B(Ĝ⁰ e_{B₀}) = λ_B(Ĝ⁰)δ_{B,B₀}` で `B ≠ B₀` は 0。
            ⟹ **残る本体は Lemma (3.20)** (原文 p.68 付近):
            「`χ ∈ Irr(B)` なら `χ̃` (= `χ|_{G⁰}` の 0 拡張、`|G|_p` 倍) は `Irr(B)` の ℤ-結合」。
            これは分解行列 `d_{χφ}` がブロックを跨がないこと + Cartan 逆行列から出る。
            ⚠⚠ **(3.20) の原文も確定 (2026-08-05、`references/navarro/pages/navarro-p063.png`)**。
            必要なのは実は (3.20) そのものでなく、その証明の "above discussion" の核:

            > **`[χ,ψ]⁰ ≠ 0` ⟹ `χ` と `ψ` は同じブロック**
            > (∵ `[χ,ψ]⁰ = ∑_{φ,μ∈IBr} d_{χφ} d_{ψμ} [φ,μ]⁰` で、非零項があれば
            > `[φ,μ]⁰ ≠ 0 ⟹ φ~μ` (逆 Cartan 行列がブロック対角) と
            > `d_{χφ} ≠ 0 ⟹ χ~φ` から `χ ~ φ ~ μ ~ ψ`)

            そして `ψ = 1_G` を取れば `[χ,1]⁰ = (1/|G|)∑_{g∈G⁰}χ(g)` なので、
            **`χ ∉ Irr(B₀)` ⟹ `∑_{g∈G⁰}χ(g) = 0`** — これが (3.32)+(3.20) の実質。
            ⟹ `ω_χ(Ĝ⁰) = 0` (`centralScalar_pRegularSum_mul_character_one` と合わせて) ⟹
            `λ_B(Ĝ⁰) = 0`。**`u_χ f_B` / `χ̃` / 一般の `χ ∈ cf(G)` は経由しなくてよい**。

            ✅ **repo 資産 (実測 2026-08-05)**: `Modular/CartanInverse.lean` に
            **`pairingZero`** (= Navarro の `[a,b]⁰`) と
            **`sum_cartanMatrix_mul_pairingZero`** (`([μ,φ]⁰)` が Cartan 行列の逆 = 定理 (2.13))
            が既にある。`Modular/CartanMatrix.lean` に `cartanMatrix = DᵀD` /
            `projectiveIndecomposableCharacter` / `ordinaryCharacter`。
            **残る新規部品は 3 本**:
            [x] (a) 🎯 **完了 (2026-08-05、`Modular/PairingZeroDecomposition`)**:
            `pairingZero_trace_eq_sum_decompositionNumber` —
            `[χ,ψ]⁰ = ∑_{φ,μ} d_{χφ} d_{ψμ} [φ,μ]⁰`。`[·,·]⁰` は p-正則元しか見ず、
            そこでは `χ = ∑_φ d_{χφ}φ` なので双線型性だけ (`g` p-正則 ⟹ `g⁻¹` p-正則)。
            [x] (b) 🎯🎯🎯 **完了 (2026-08-05、`Modular/CartanBlockDiagonal` + `Modular/PairingZeroBlock`)**。
            ⚠ **これが残る唯一の実質**。`C = DᵀD` はブロック対角
            (`d_{χφ}≠0 ⟹ χ~φ` から `C_{φμ} = ∑_χ d_{χφ}d_{χμ} = 0` for `φ≁μ`)、
            その逆 `B = ([μ,φ]⁰)` もブロック対角。標準論法 =
            ブロック射影 `P` は `C` と可換 ⟹ `PB = PC⁻¹ = C⁻¹P = BP` ⟹ `B` もブロック対角。
            ⚠ **より短い論法 (2026-08-05 に設計、可換性論法より軽い)**: 行列 `P` を経由せず
            **解の一意性**で済む。`b_μ := [μ,φ]⁰` は `∑_μ C_{μθ} b_μ = δ_{φθ}` (∀θ) を満たす。
            `X := {μ : μ ~ φ}` として `b' := b·1_X` (X の外を 0 に潰したもの) を作ると、
            `C` のブロック対角性から `b'` **も同じ方程式を満たす**
            (θ∈X なら X 外の項は `C_{μθ}=0` で落ちるので和が変わらない;
            θ∉X なら両辺 0)。`C` は可逆 (`Bᵀ C = 1` から `Matrix.mul_eq_one_comm`) なので
            `b = b'`、すなわち `μ ∉ X` で `b_μ = 0`。
            **必要な Matrix API**: `Matrix.mul_eq_one_comm` / `Matrix.mulVec_mulVec` /
            `Matrix.one_mulVec` のみ。

            **実装メモ (API 実測 2026-08-05)**:
            * `cartanMatrix hp hω hω' hπ hlin hkerJ e μ φ = ∑_{i:ι'} D_{iμ} D_{iφ}`
              (`CartanMatrix.lean:91`)、`decompositionMatrix ... e i = decompositionNumber ...
              (wedderburnLatticeRepresentation e i)` (`OrdinaryIrreducibles.lean:116`)。
            * ブロック同値 = `blockSetoid π hπ hlin` (`Algebra/BlockIdempotent.lean:47`):
              `i ~ j ↔ centralCharacterAlg π i hπ hlin = centralCharacterAlg π j hπ hlin`。
            * ⟹ `cartanMatrix_eq_zero_of_ne_block` は
              `Finset.sum_eq_zero` + `Nat.mul_ne_zero_iff` + 各 `z` について
              `centralCharacterAlg_eq_of_decompositionNumber_ne_zero` を 2 回
              (`c` が共通なので両者が一致) + `AlgHom.ext`/`Quotient.sound`。
              ⚠⚠ **より良い道 (2026-08-05 に発見)**: `(reduction ρ).asAlgebraHom z = c • id`
              の `c` を自分で作る必要はない。`πG := π` / `ιG := ι` と取れば
              **`blockOfIrr e hπ hlin hnil i : Block π hπ hlin = Quotient (blockSetoid π hπ hlin)`**
              がそのまま「`χ_i` のブロック」なので、欲しいのは

              > `d_{iμ} ≠ 0 ⟹ Quotient.mk (blockSetoid π hπ hlin) μ = blockOfIrr e hπ hlin hnil i`

              の 1 本。橋は 2 つとも既存:
              `blockCharacter_mk π hπ hlin i` (`Algebra/BlockIdempotent.lean:60`、
              `blockCharacter (mk i) = centralCharacterAlg π i`) と
              `blockCharacter_blockOfLattice` (`BlockOfLattice.lean:72`、
              `blockCharacter (blockOfLattice …) = reducedCentralCharacterAlg (centralCharacter K ψ)`)。
              ⟹ `centralCharacterAlg π μ = reducedCentralCharacterAlg (ω_{χ_i})` を示せば
              `blockCharacter` が単射なので両ブロックが一致。
              その等式が `centralCharacterAlg_eq_of_decompositionNumber_ne_zero` の内容
              (`d_{iμ} ≠ 0` なら `μ` の中心指標が `χ_i` の還元中心指標)。
              ⚠ 現状 `blockOfIrr` と `decompositionMatrix` を結ぶ補題は repo に**無い** (grep 実測)。
              これが (b) の実装の入口。
            [x] (c) **既存**: `centralCharacterAlg_eq_of_decompositionNumber_ne_zero`
            (`DecompositionNumber.lean`) — `d_{χφ} ≠ 0` なら `φ` の中心指標は `χ` のそれ。

            ⟹ 🎯🎯🎯 **(3.20) 完了 (2026-08-05)**:
            `pairingZero_trace_eq_zero_of_centralCharacterAlg_ne` —
            **`χ` と `ψ` が異なるブロックなら `[χ,ψ]⁰ = 0`**。内訳:
            * `exists_smul_id_asAlgebraHom_reduction` (`CartanBlockDiagonal`) —
              「足りない部品」だった「`(reduction ρ).asAlgebraHom z = c • id` なる `c`」は
              既存部品の合成だった (`centerLift` で `Z(𝒪G)` に上げ
              `apply_center_eq_centralScalar_smul` → `asAlgebraHom_reduction_mapRingHom` で降ろす)。
            * `centralCharacterAlg_eq_of_decompositionMatrix_ne_zero` /
              `cartanMatrix_eq_zero_of_centralCharacterAlg_ne` — `C = DᵀD` はブロック対角。
            * `pairingZero_eq_zero_of_centralCharacterAlg_ne` (`PairingZeroBlock`) —
              **逆行列もブロック対角**。共役論法でなく**解の一意性**で済んだ:
              `b` を `φ` のブロックに切り詰めた `b'` も同じ方程式を満たし、`C` 可逆ゆえ `b = b'`。
            ⟹ `ψ = 1_G` で **`χ ∉ Irr(B₀)` ⟹ `∑_{g∈G⁰}χ(g) = 0`**。
            [x] 🎯🎯🎯 **(3.32) の実質 完了 (2026-08-05)**:
            `sum_pRegular_trace_eq_zero_of_centralCharacterAlg_ne` (`PairingZeroBlock`) —
            **`∑_{g∈G⁰}χ(g) = 0`** ((3.20) を自明指標と組むだけ; `[χ,1]⁰ = |G|⁻¹∑_{g∈G⁰}χ(g)`、
            `|G|⁻¹ ≠ 0` と `algebraMap` 単射で `𝒪` の等式に) と
            `centralScalar_pRegularSum_eq_zero` (`PRegularSumVanishing`、新設) —
            **`ω_χ(Ĝ⁰) = 0`** (`ω_χ(Ĝ⁰)χ(1) = ∑_{g∈G⁰}χ(g) = 0`、`χ(1) = dim ≠ 0`)。
            ⚠ 自明指標は「トレースが恒等的に 1 の格子表現 σ」として仮説パラメータ化。
            [x] 🎯🎯🎯 **剰余体への配線も完了 (2026-08-05)**:
            `blockCharacter_blockOfIrr_pRegularSum_eq_zero` (`PRegularSumVanishing`) —
            **`λ_B(Ĝ⁰) = 0` (`B ≠ B₀`)**。
            `mapRingHom_pRegularSum`/`mapRingHom_pElementSum` (`Algebra/PElementSum`) を新設し、
            `algebraMap_centralScalar_eq` で `K` 側と繋ぎ
            `blockCharacter_blockOfLattice_mapRingHom` で剰余体へ降ろす。
            ⟹ **(3.32) 完成**。次 = (4.23) に `z = Ĝ⁰` を入れて **(6.14) Külshammer**
            `π(Ĝ_p·Ĝ⁰) = ∑_B λ_B(Ĝ⁰) e_B = |G⁰|* e_{B₀}`。
            ⚠ 検算: `ω_χ(Ĝ⁰) = (1/χ(1))∑_{g∈G⁰}χ(g)` は `χ ∉ Irr(B₀)` で **`K` の中で厳密に 0**
            (還元して 0 ではない)。`Z_q` (p∤q) / `S_3` (p=3) で確認済。
          ⟹ **見通し**: (4.19) が 2-3 段、(4.23)+(3.32)+(6.14)+(6.1) で 3-4 段。
          Brauer 誘導定理は不要のまま。
          ⟹ **段 99(c) は「Brauer 誘導定理が要る」という見積りが誤りだった**。
          初等的だが多段の古典計算 (Burnside 公式・Sylow 数え上げ) に置き換わる。
        - ⟹ **次の上流は Chapter 3 の defect / height**。(6.6) だけでなく (6.10)–(6.13) や
          Chapter 7 も height を使うので、いずれ通る道。
        - **既存の土台 (実測 2026-08-05)**: `Algebra/DefectGroup.lean` に
          `IsDefectGroup b D` (相対トレースイデアル `A^G_D` に属する極小な `D`) と
          `exists_isDefectGroup` / defect group が `p`-群であること /
          `exists_blockIdempotents_defectGroups_conj` (共役性) が**既にある**。
          ⟹ 新規に要るのは **defect 数 `d(B)` (`|D| = p^d`) と height**
          (`ν(χ(1)) = ν(|G|) - d(B) + ht(χ)`)、および Chapter 3 の (3.20)-(3.24)。
        - [x] **defect 数 `d(B)`** — 完了 (2026-08-05、`Algebra/DefectNumber` +
              `Modular/BlockDefect`)。
        - [x] 🎯🎯 **height の非負性 `ν(χ(1)) ≥ ν(|G|) - d(B)`** — 完了 (2026-08-05)。
              **⚠ Chapter 3 の足場 ((3.20)-(3.24)・`~` 関数・Brauer の指標判定法・付値論)
              を一切使わずに landing した**。Alperin 流の 2 行の論法:
              `f_B = Tr^G_D(c)` (defect group の定義) に**指標が類関数であること**を当てると
              `[G:D]` 個の共役和が指数倍に潰れ、`f_B` が `B` の表現で恒等に作用するから
              `χ(1) = [G:D]·χ(c)`、`χ(c) ∈ 𝒪` ⟹ `[G:D] ∣ χ(1)`。
              * `Algebra/RelativeTrace`: 🎯 `map_relTrace` (軌道不変な加法写像は
                `χ(Tr^H_K a) = [H:K]•χ(a)`; `a` の固定性すら不要)
              * `Algebra/RelativeTraceCharacter` (新設、**任意の可換環上**):
                対称加法写像 `τ` (`τ(xy)=τ(yx)`) と代数準同型の合成は共役不変 ⟹
                🎯 `index_dvd_finrank` (`f ∈ R[G]^G_D` が恒等に作用 ⟹ `[G:D] ∣ χ(1)`)
              * `Modular/PModularSystem`: 🎯 `pow_dvd_of_natCast_pow_dvd`
                (`p` 冪の整除は `𝒪` で判定してよい。**整域性不要** — 局所環で
                `1 - p^{i-e}t` が単元ゆえ `p^e = 0` となり `CharZero` に矛盾)
              * `Modular/BlockHeight` (新設): 🎯🎯 `pow_defect_dvd_finrank`
              ⟹ height `ht(χ) = ν(χ(1)) - ν(|G|) + d(B)` が自然数として定義可能。
        - [x] 🎯 **`p ∤ |G⁰|`** — 完了 (2026-08-05、`GroupTheory/PRegularElementCount`)。
              `not_dvd_card_isPRegular`。これは **`1_G` が主ブロックで height 0** である
              ことの具体形 (Navarro の `[1̃_G, 1_G] = |G⁰|/|G|_{p'}` が `p` で単元)。
              (6.6) の Okuyama 証明で (3.24) が供給する入力が、指標論抜きで得られた。
              論法: Sylow `P` の共役作用で `|G⁰| ≡ |C_G(P)⁰| (mod p)`、
              `C_G(P)` では全 `p`-元が `P` に入り `P ∩ C` は中心的 Sylow ⟹
              `C⁰ ≃ C/(P ∩ C)` で指数は `p` と素。
        - [x] 🎯🎯 **`d(B₀) = ν(|G|)` (主ブロックは full defect)** — 完了 (2026-08-05)。
              ⚠ `Br_P` 経由でなく**1 次元表現**で出た (より短い): 可換環への代数準同型 `ψ` を
              `f = Tr^G_D(c)` に当てると `1 = ψ(f) = [G:D]·ψ(c)` ⟹ `[G:D]` は単元。
              * `Algebra/RelativeTraceCharacter`: 🎯 `isUnit_index_of_mem_relTraceIdeal`
              * `Algebra/AugmentationIdeal`: `augmentation_mapRingHom` (係数変換と可換)
              * `Modular/BlockHeight`: 🎯🎯 `defect_eq_factorization_of_apply_eq_one` /
                `eq_one_of_isIdempotentElem_of_residue_ne_zero`
              * `Modular/PrincipalBlockDefect` (新設): 🎯 主ブロック冪等元 lift での実例 +
                🎯 `exists_isIdempotentElem_defect_principalBlock` (**充足可能性の実証**)
              ⟹ 次数 1 の `1_G` は `B₀` で height 0。

        **🧭 残りの道筋 (2026-08-05 に原文精読で確定)**。段 99 (c) までに要るものと難所:
        - **(6.10) `ker(B) = O_{p'}(ker χ)`** — 原文 p.126 の証明は**初等的で height 不要**:
          weak block orthogonality (= 既存の (5.11) `sum_character_blockOfIrr_eq_zero`) で
          `Ξ = Σ_{χ∈Irr(B)}χ(1)χ` が `p`-singular で消える ⟹ `ker(B)` は `p'`-群、
          `u = |N|⁻¹ Σ_{n∈N} n ∈ Z(SG)` の中心指標が `[ψ_N,1_N]/ψ(1)` に等しい ⟹
          Clifford で `N ≤ ker ψ`。**新規に要るのは `ker(B)`・`Irr(B)` 族・Clifford**。
        - [x] **(6.11) の archimedean 入力 — 解決済 (2026-08-05、`Algebra/RootsOfUnitySum`)**。
          🎯 `eq_one_of_pow_eq_one_of_sum_eq_card`: **標数 0 の任意の体**で
          `ε i^m = 1` かつ `∑ ε i = card` なら全部 1。円分多項式も `IsPrimitiveRoot` も不要:
          (i) 冪根は ℚ 上整 ⟹ 生成部分代数は ℚ 上代数的 ⟹ `IsAlgClosed.lift` で ℂ へ、
          (ii) 戻りは**単射性を使わず** `(ε-1)(1+ε+…+ε^{m-1}) = 0` の分解 + 後者を送ると
          `m = 0 in ℂ` で矛盾、という筋。⟹ (6.11) 本体は Brauer 指標の固有値持ち上げの
          配線だけになった。
        - **(6.6) Okuyama (第三主定理の両向き)** は (6.5) → (6.3) → **(3.20)/(3.22)/(3.24)**
          を要求し、そこで `~` 関数 (Navarro (2.15)) が要る。(2.15) の証明は
          **Brauer の指標判定法** (mathlib に無い; Brauer 誘導定理) を使う。
          ⟹ ここが最大の壁。ただし **(3.24) の数値内容 (height ≥ 0 / full defect /
          `p ∤ |G⁰|`) は上記 3 件で回避済**なので、残るのは
          「`[χ̃, ξ]` の付値」という形の部分だけ。
- [ ] **100: `(6.10)` `ker(B) = O_{p'}(ker χ)` → `(6.12)` → 🎯 `(6.13)`**
      (normal `p`-complement ⟺ `IBr(B₀)` 単元、Cartan 行列 `(|G|_p)`)
  - [x] 🎯🎯 **(6.11) 完了 (2026-08-05、`Modular/BrauerCharacterKernel`)**:
        `p`-正則な `g` で `ρ g = 1 ⟺ φ(g) = φ(1)`。
        `φ(g) = Σ_ζ d_ζ·ζ̂` かつ `Σ d_ζ = dim V` ⟹ 重複度込みで `dim V` 個の冪根の和が
        `dim V` ⟹ (前項の抽象体版補題で) 全部 1 ⟹ `ζ ≠ 1` の固有空間が `⊥` ⟹
        固有空間分解が `ζ = 1` に潰れる。⚠ 既約性不要 (任意の有限次元表現)。
  - [x] **(6.10) の核判定エンジン (2026-08-05、`Algebra/SubgroupSum`)**:
        `N̂ = ∑_{n∈N} n` を導入し 🎯 `ρ(N̂) = |N|·1 ⟺ ρ が N を潰す`
        (**任意の可換環・任意の対象代数**、半単純性も標数仮定も不要)。
        Navarro p.126 の `u = |N|⁻¹ Σ_{n∈N} n` の議論がこれに当たる。
  - [x] 🎯🎯🎯 **(6.10) 完成 (2026-08-05、`Modular/BlockKernel.lean` + `Algebra/SubgroupSum`)**。
        * 🎯 `blockKernel` = **(6.9)** `ker(B) = ⋂_{χ∈Irr(B)} ker χ`。`Irr(B)` は
          `blockOfIrr` のファイバーなので添字 subtype 上の `⨅` で書ける。ordinary
          irreducible が Wedderburn 成分そのものゆえ「ker χ」は `MonoidHom.ker` そのもの
          ⟹ 教科書が使う初等指標論 (「ker(B) は `Ξ = Σ χ(1)χ` の核」) は**定義に
          組み込まれて別段が不要**になった。
        * 🎯🎯 `isPRegular_of_mem_blockKernel` = **前半** (`ker(B)` は `p`-正則元からなる)。
          `Ξ(g) = Σ_{χ∈Irr(B)} χ(1)²` は標数 0 の `K` で非零 (自然数の和)、
          弱ブロック直交性は `p`-singular で 0。⚠ `p.Prime` は不要だった (linter が指摘)。
        * `not_dvd_card_blockKernel` (Cauchy) / `isPiSubgroup_blockKernel` /
          `blockKernel_le_opPi` (`ker(B) ≤ O_{p'}(G)`)
        * 🎯 `sum_character_one_mul_character_eq_zero` = 弱ブロック直交性
          = (5.11) の `h = 1`。⚠ (5.11) は `C_G(g_p)` の分裂データを担ぐので `g` ごとに
          変わる ⟹ 本体は `hweak` を仮説で受け、この補題が単一の `g` で discharge。
        * 🎯🎯 `le_blockKernel_of_normal_of_forall_eq_one` = **逆包含、Clifford 不要**。
          教科書 (p.126) は `u = |N|⁻¹ N̂` の中心指標を `[ψ_N,1_N]/ψ(1)` と同定して
          Clifford を当てるが、`N̂` を中心指標に直接通す方が短い:
          `N ⊴ G` ⟹ `N̂` 中心 ⟹ 各絶対既約格子上でスカラー `ω_i(N̂) ∈ 𝒪`;
          同じブロック ⟹ **還元が一致**; `χ_{i₀}` 上では `ω(N̂) = |N|` で `p ∤ |N|` ゆえ
          剰余体で非零 ⟹ `ω_i(N̂)` は局所環の単元 ⟹ 吸収律 `n·N̂ = N̂` で約せる。
          格子→周囲は `single n 1 - 1` を既存の
          `asAlgebraHom_eq_zero_of_latticeRepresentation` に通すだけ。
          ⚠ `|N|` を `𝒪` の中で逆にする必要すら無い。
        * 🎯🎯🎯 `isGreatest_blockKernel` = **(6.10) の完全形**: `ker(B)` は `ker χ` に
          含まれる `G`-正規 `p'`-部分群のうち最大 = `O_{p'}(ker χ)`
          (`O_{p'}(ker χ)` は `ker χ ⊴ G` で特性的ゆえ `G`-正規、逆に `ker χ` 内の
          `G`-正規 `p'`-部分群は `ker χ`-正規 ⟹ 最大元は同一。この形なら `ker χ` の
          部分群を `G` へ押し出す配管が要らない)。
        * `Algebra/SubgroupSum` に `mapRingHom_subgroupSum` / `subgroupSum_mem_center` /
          🎯 `map_single_eq_one_of_isUnit_map_subgroupSum` (核判定を「`ρ(N̂)` が単元」へ
          一般化) を追加し、`[Ring A]` → `[Semiring A]` へ一般化。
          ⚠ 一般化は必要だった: `Module.End 𝒪 L` の `Semiring` インスタンス経路が
          `Ring.toSemiring` 経由と一致せず `AlgHom` の型が unify しなかった。
        * `GroupTheory/PRegularElement` に `isPRegular_of_pPart_eq_one` /
          `isPRegular_iff_pPart_eq_one` (既存 `pPart_eq_one_of_isPRegular` の逆)。
  - [x] **(6.12) 前半 + (6.13) の BS が引く向き — 完了 (2026-08-05)**。
        * `Algebra/SubgroupSumBlockAction.lean` (新設) = **(2.32) の `p'` 版**:
          🎯 `pi_single_eq_one_of_isUnit_centralScalar` — `ω_i(N̂)` が単元なら第 `i`
          ブロックは `N` を潰す (吸収律 `n·N̂ = N̂` から可逆スカラー行列を約すだけ)。
        * `Modular/BlockKernel.lean`: 🎯 `blockCharacter_subgroupSum` (= `λ_B(N̂*) = |N|`、
          (6.10) の核を補題に括り出し) と 🎯🎯 `pi_single_eq_one_of_blockOfIrr`
          (= **(6.12) 前半** `ker(B) ≤ ker φ`, `φ ∈ IBr(B)`)。
        * `Algebra/NormalPSubgroupTrivialAction.lean`:
          🎯 `blockRepresentation_eq_one_of_sup_eq_top` — `N` が自明作用 + `G = N·P`
          (`P` が `p`-部分群) ⟹ `G` 全体が自明作用。`P`-固定空間が自動的に `G`-固定
          (`g = n x` ⟹ `g·w = n·(x·w) = w`) ゆえ非零部分加群 ⟹ 単純性。
          ⚠ `G/N` で (2.32) を使うのと同値だが**商へ `π` を移送せずに済む**。
        * `Modular/PrincipalBlockKernel.lean` (新設) — **主ブロックでは全部初等的**:
          中心指標が添加写像そのものなので 🎯 `blockCharacter_principalBlock_subgroupSum`
          (`λ_{B₀}(N̂) = |N|`, 任意の正規部分群) が**通常指標も格子も `𝒪` も経由せず**出る。
          ⟹ 🎯🎯 `pi_single_eq_one_principalBlock` ⟹
          🎯🎯🎯 **`pi_single_eq_one_principalBlock_of_normalPComplement`** =
          **(6.13) の BS が引く向き**: `G` が正規 `p`-補群を持てば主ブロックの単純加群は
          全部自明。`G = N·S` は既存 `GroupTheory.sylow_sup_eq_top_of_isPGroup_quotient`。
        ⚠ 教科書は (6.12) 経由で `⋂_{φ∈IBr(B₀)} ker φ = O_{p'p}(G)` を出してから (6.13) に
        至るが、主ブロックの中心指標 = 添加写像を使えば **(6.12) の重い側を通らずに**
        BS が使う向きだけ取れる。
  - [x] 🎯🎯🎯 **`IBr(B₀) = {1_{G⁰}}` — 完了 (2026-08-05)**。段 47-49 の同型類議論は不要で、
        **全射性だけ**で出た (`Algebra/NormalPSubgroupTrivialAction`):
        * 🎯 `pi_eq_scalar_augmentation` — `π(g)_i = 1` (∀g) なら `π(x)_i = scalar(ε(x))`
        * 🎯 `subsingleton_of_forall_pi_single_eq_one` — **次数 1** (像がスカラーだけなのに
          `π` は全射 ⟹ 非対角の `Matrix.single a b 1` が取れない)
        * 🎯🎯 `eq_of_forall_pi_single_eq_one` — **高々 1 つ** (2 つあると両成分とも `ε(x)` で
          分離できないが、全射性は `Pi.single i 1` を出す ⟹ `ε(x) = 1` かつ `= 0`)
        * `Modular/PrincipalBlockKernel`: 🎯🎯🎯 `eq_of_principalBlock_of_normalPComplement` /
          `subsingleton_of_principalBlock_of_normalPComplement`
  - [ ] **(6.13) の残り = Cartan 行列 `= (|G|_p)`** (`Σ_{χ∈Irr(B₀)} χ(1)² = |G|_p`)。
        BS は「`C` が正規 2-補群を持つ ⟹ `b₀` の Cartan 行列は `(4)`」の形で引く。
        **設計は確定 (2026-08-05)**: `u = |N|⁻¹ N̂` (中心冪等元) の左乗法のトレースを 2 通りに
        数える。土台は `Algebra/TraceMulLeft.lean` (新設、完了):
        * 🎯 `trace_mulLeft_monoidAlgebra` — `tr(L_a) = |G| · a(1)` ⟹ `tr(L_u) = |G|/|N|`
        * 🎯 `trace_mulLeft_pi_matrix` — `tr(L_v) = Σ_i m_i · tr(v_i)` ⟹ `e(u)` の各成分が
          中心冪等 = `0` か `1` なので `Σ_{ω_i(u)=1} m_i²`
        ⚠ **冪等元の階数 = トレース** という線型代数 (mathlib に無い) を経由しない。
        * [x] **代数的な中身は完了 (2026-08-05、`Algebra/SubgroupSumWedderburn.lean`)**:
          `apply_subgroupSum_eq_scalar` (`e(N̂)_i = ω_i(N̂)·1`) /
          🎯 `centralScalar_subgroupSum_eq_zero_or_card` (**`ω_i(N̂) ∈ {0, |N|}`**、
          `N̂² = |N|·N̂` + 体) / 🎯 `sum_sq_centralScalar_subgroupSum`
          (**`Σ_i m_i² ω_i(N̂) = |G|`**) / 🎯🎯 `card_mul_sum_sq_eq_card`
          (**`|N| · Σ_{ω_i(N̂)≠0} m_i² = |G|`**)。
          支持: `SubgroupSum` に `subgroupSum_mul_subgroupSum` / `coeff_subgroupSum_one`、
          `TraceMulLeft` に 🎯 `trace_mulLeft_algEquiv`。
        * [x] 🎯🎯🎯 **完了 (2026-08-05、`Modular/PrincipalBlockCartan.lean`)**。
          `G = N·P` (正規 `p`-補群の形) のとき:
          - 🎯 `centralScalar_subgroupSum_ne_zero_iff` (通常側: `ω_i(N̂) ≠ 0 ⟺ N ≤ ker χ_i`)
          - 🎯🎯🎯 `forall_eq_one_iff_blockOfIrr_eq_principalBlock`
            (**`Irr(B₀) = {χ_i : N ≤ ker χ_i}`**)。(⟸) は主ブロックの中心指標 = 添加写像
            ⟹ `λ_{B₀}(N̂*) = |N|* ≠ 0`; (⟹) は「そのブロックが `N` を潰す ⟹ `G = N·P` で
            `G` 全体を潰す ⟹ `eq_of_forall_pi_single_eq_one` で一意」
          - 🎯🎯🎯 `card_mul_sum_sq_principalBlock` = **`|N| · Σ_{χ∈Irr(B₀)} χ(1)² = |G|`**
          支持: `BlockKernel` の `forall_eq_one_of_residue_centralScalar_ne_zero`
          ((6.10) 逆包含の核を括り出したもの)。
  - [x] ⟹ **段 100 = (6.10)/(6.11)/(6.12 前半)/(6.13) 完了 (2026-08-05)**。
        BS 本証明が「`C` が正規 2-補群を持つ ⟹ `b₀` の Cartan 行列は `(4)`」の形で引く部分が揃った。
        残る (6.12) 後半 (`M/ker(B)` が `p`-群) は BS 経路では不要 (主ブロックの中心指標 =
        添加写像で迂回済)。
  - [ ] **(6.12) 本体 (後半)**。原文 p.127 の証明が要求するのは
        (i) `ker(B) ≤ ker φ` (`φ ∈ IBr(B)`) — 上の逆包含の **`k` 側版**
        (`λ_B(N̂*) = |N|*` ≠ 0 ⟹ block 表現上で `N̂` が単元 ⟹ 核判定) でほぼ同型に書ける、
        (ii) **Lemma (2.32)** `O_p(G)` は単純 `kG`-加群を潰す — ✅ **既に存在した**
        (`Algebra/NormalPSubgroupTrivialAction.lean` の
        `blockRepresentation_eq_one_of_mem_normal_pSubgroup` /
        `pi_single_eq_one_of_mem_normal_pSubgroup`、Navarro (4.7) 用に段 xx で整備済)。
        ⚠ 2026-08-05 に一度書き直しかけて重複に気付いた — 教科書番号 ((2.32)) でなく
        概念名 (`normal_pSubgroup` / `invariants`) で grep すべきだった
        ([[grep-concept-names-not-book-notation]] の再発)。
        (iii) `M/ker(B)` が `p`-群 — `x ∈ M` が `p`-正則なら `χ(x) = χ(1)` を経由するので
        **通常指標版の (6.11)** (`χ(x) = χ(1) ⟹ ρ(x) = 1`, 標数 0) が要る。
        `Algebra/RootsOfUnitySum` の抽象体版補題は使えるが、`K` が `p'`-乗根を
        十分持つかは設定依存 (`ℂ_p` なら自明)。
- [ ] **101: `(7.2)` Klein four Sylow-2 / `(7.3)` basic set / `(7.4)` / `(7.5)` / `(7.6)`**
  - [x] **(3.18)(b)⟹(c) 完了 (2026-08-05、段 155 `Modular/DefectZeroDegree`)**:
        `ordProj_dvd_finrank_of_character_eq_zero` — `p`-singular で消える指標は
        `|G|_p ∣ χ(1)`。Sylow `S` 上で和が `χ(1)` に潰れ = `|S|·dim V^S`。
        ⚠ `p`-modular system 不要 (標数 0 の体だけ)。
  - [x] 🎯🎯 **「主ブロックの χ は `p`-singular 元で全消滅しない」完了
        (2026-08-05、段 156 `Modular/PrincipalBlockNonvanishing`)**:
        `not_dvd_card_of_character_eq_zero_of_pSingular` /
        `exists_not_isPRegular_character_ne_zero`。新規に要ったのは予告どおり
        🎯 `forall_apply_eq_of_invariants_ne_bot` (不変ベクトルがあれば Wedderburn
        表現は自明) 1 本のみ + `isUnit_centralScalar_pRegularSum_of_blockOfIrr_principal`。
        `card_filter_isPRegular` は `PRegularElementCount` へ移設 (2 箇所で使用)。
  - [ ] **⏸ 次の一手 = (7.2) 本体の残り部品**。原文 p.131-132 (`pages/navarro-p131,132.png`)
        より、まだ repo に無いもの (**2026-08-05 現在の残り = ★ の 2 件のみ**):
        * ~~**Burnside の正規 `p`-補群定理**~~ — ✅ **既存 (2026-08-05 実測)**:
          `OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer`
          (`Isaacs/Ch05_Transfer/Basic.lean:491`、`N_G(P) ≤ C_G(P) ⟹ HasNormalPComplement p G`、
          mathlib の `MonoidHom.transferSylow` 経由)。新規形式化は不要。
        * [x] 🎯 **完了 (2026-08-05、段 179、`GroupTheory/KleinFourAutomorphism`)**:
          `eq_or_eq_or_eq_iterate_of_klein` = 「位数 3 の自己同型に対し任意の involution `b` は
          `a`, `f a`, `f² a` のいずれか」。支持 = `eq_one_or_eq_or_eq_or_eq_of_klein`
          (Klein 四元群は `{1,a,b,ab}`) / `exists_ne_ne_one_of_klein` /
          `eq_of_fixed_of_klein` (3 乗が恒等で involution を 1 つ固定すれば恒等)。
          ⚠ `Aut(Z₂×Z₂) ≅ Sym(3)` 全体は作らない (必要なのは巡回性だけ)。
        * **(5.12)** `k(B) = Σ_i Σ_{b ∈ Bl(C_G(x_i)), b^G = B} l(b)` (第二主定理の系)
          - [x] 🎯🎯 **第一段 完了 (2026-08-05、段 174、`Modular/PSectionClassCount`)**:
            `k(G) = Σ_{[x] : p-元類} #cl(C_G(x)⁰)`。`p`-部分の類が `[x]` の `G`-類は
            `C_G(x)` の `p`-正則類と全単射 (`pSectionClassEquiv`)。`p`-元類の代表は選ばず
            `pPartClass` のファイバーで分割する。⟹ 一般化分解行列 `J` が正方の片側。
          - [x] 🎯🎯 **第二段 完了 (2026-08-05、段 175-176)**。
            **⚠ 前回書いた「束ね structure が必要」という設計判断は誤りだった** —
            族は素の `variable` (依存型の族 `ι : PElementClass p G → Type*` 等) で足りる。
            さらに **Navarro の経路 (`J̄ᵗ J = diag(Cartan)` = (5.13) 経由) を採らない方が短い**:
            * `Modular/GeneralizedDecompositionMatrix` (新 leaf):
              `generalizedDecompositionMatrix` = `J` (行 `Irr(G)`、列 `(D, μ)`) /
              `sectionCharacterMatrix` = `E`, `E_{χ,(D,n)} = χ(x_D z_{D,n})` /
              🎯 `sectionCharacterMatrix_eq_mul_blockDiagonal` = **`E = J·diag(B)`**
              (中身は (5.1) の定義式を行列の言葉に直しただけ) /
              `sectionClassIndexEquiv` (段 174 を `IBr` の添字づけへ移送) /
              `sectionCharacterMatrix_submatrix` (`E` は列を並べ替えると **`G` の通常指標表**) /
              🎯🎯 `isUnit_det_generalizedDecompositionMatrix` = **`J` は正則**。
              ⟹ **(5.13) も `x⁻¹` 側の数も使わない**。
              ⚠ mathlib に `Matrix.det_blockDiagonal'` (可変サイズ版) が無いので
              ブロックごとの逆行列を明示する。
            * `Algebra/BlockPartitionedMatrix` (新設、純線型代数):
              🎯 `card_eq_card_of_det_ne_zero` = 「行を `f`、列を `g` で分割し対角ブロック外が
              0 の正方行列の行列式が非零なら各ブロックの大きさは一致」。
              ⚠ **rank 論法でなく Leibniz 展開** — 非零行列式から `M (σ j) j ≠ 0` を全 `j` で
              満たす置換 `σ` が取れ、その `σ` が 2 つの分割を突き合わせる。前回書いた
              「rank 論法が最短」より短く、`Aᵗ A` も (5.13) も要らない。
          - [x] 🎯🎯🎯 **第三段 完了 = (5.12) 本体 (2026-08-05、段 177)**:
            `card_blockOfIrr_eq_card_inducedBlockOfCentralizer` (`Modular/BlockCharacterCount`)。
            * 🎯 (5.8) の `Irr(G)` 版 = `Modular/SecondMainBlockOfIrr` の
              `generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne`。
              **調査事項の答**: repo の第二主定理ブロック形は「表現 `σ` + 不変束 `L`」で
              述べられているが、通常既約は正準な束 `wedderburnLattice` を持ち
              `wedderburnLatticeRepresentation = latticeRepresentation (wedderburnRepresentation)`
              が **definitional** なので、`blockOfIrr` 版は **1 行の cite で特殊化できた**
              (`Representation.character = LinearMap.trace` も定義通り)。
            * 列側の「`μ` を含むブロック」写像は新規に要らなかった —
              `Block π hπ hlin` は `ι` の商なので `Quotient.mk (blockSetoid π hπ hlin) μ` が
              そのまま使える (`blockOfBrauer` 相当は不要)。
            * 仕上げは `inducedBlockOfColumn` を定義して
              `card_eq_card_of_det_ne_zero` に食わせるだけ。
        * **(5.13)(b)** 一般化分解数の直交性 — ✅ **完了 (段 172)**。
          **⚠ 設計上の懸案は解決 (2026-08-05)**: 原文 (p.107 のページ画像で確定) は
          `Σ_{χ∈Irr(G)} conj(d^x_{χμ}) d^x_{χφ} = c_{μφ}` と**複素共役**で書くが、
          抽象的な分裂体 `K` には共役が無い。**共役は不要**と分かった:
          - Brauer 指標は `μ(y⁻¹) = conj(μ(y))` (固有値の持ち上げが逆元で逆元になる)
          - `χ(xy) = Σ_μ d^x_{χμ} μ(y)` を共役すると
            `χ(x⁻¹z) = Σ_μ conj(d^x_{χμ}) μ(z)` (`z = y⁻¹`、`C_G(x⁻¹) = C_G(x)`)
          - (5.1) の一意性より ⟹ **`conj(d^x_{χμ}) = d^{x⁻¹}_{χμ}`**
          ⟹ 抽象版の statement は
          **`Σ_{χ∈Irr(G)} d^{x⁻¹}_{χμ} · d^{x}_{χφ} = c_{μφ}`** (共役ゼロ)。
          BS が使うのは `x = t` (involution) で `x⁻¹ = x` ゆえ
          `Σ_χ (d^t_{χμ})(d^t_{χφ}) = c_{μφ}` になる。
          **証明経路** (原文 p.108): `Φ^x_μ ∈ cf(G)` = `C_G(x)` の射影不可分指標を
          `p`-section `S(x)` へゼロ拡張したもの、を作り
          `[Φ^x_μ, χ] = conj(d^x_{χμ})` を示して `[Φ^x_μ, Φ^x_φ]` を 2 通りに計算する。
          **既存で使えるもの**: `Modular/PSection.lean` (`pSection` / `mem_pSection_iff` /
          `isConj_centralizer_of_isConj_mul` = 助変数化の単射性 = `Φ^x_μ` の well-defined 性) /
          `CartanMatrix.projectiveIndecomposableCharacter` (`Φ_φ`、`x = 1` の場合) /
          `CartanInverse.pairingZero_projectiveIndecomposableCharacter` (= (2.13)
          `[Φ_θ,φ]⁰ = δ`) / `ProjectiveCharacterVanishing` (`Φ_φ` は `p`-singular で 0)。
          **新規**: `Φ^x_μ` (一般 `x` へのゼロ拡張) とその 2 性質。
          - [x] **`p`-section の分割 完了 (2026-08-05、段 162)**: `mem_pSection_pPart` /
            `isConj_of_mem_pSection_of_mem_pSection` / `pSection_eq_of_isConj`。
          - [x] 🎯 **`Φ^x_μ` 完了 (2026-08-05、段 163
            `Modular/SectionProjectiveCharacter.lean`)**:
            `sectionProjectiveCharacter` (choice で定義、`S(x)` の外は 0) と
            `_eq_zero` / 🎯 `_of_isConj_mul` (インタフェース) / `_mul`
            (`Φ^x_μ(xy) = Φ_μ(y)`) / 🎯 `_eq_of_isConj` (類関数)。
            well-defined 性の核 = `projectiveIndecomposableCharacter_eq_of_isConj_mul`。
            ⚠ 以降 definition を unfold せず `_of_isConj_mul` を使う。
          - [x] **内積計算の土台 完了 (2026-08-05、段 164-169)**:
            * 段 164 `centralizerOf_mul_eq_inf` (`C_G(xy) = C_G(x) ⊓ C_G(y)`)
              ⚠ 結果的にこの経路では**未使用** (二重和にしたら類の大きさが要らなくなった)
            * 段 165 `mem_centralizerOf_and_conj_of_conj_mul` (具体的な共役元版)
            * 段 166 `fiberEquivCentralizerOf` / `card_fiber_eq_card_centralizerOf`
              (`(g,y) ↦ g(xy)g⁻¹` のファイバー ≃ `C_G(x)`)
            * 段 167 `card_centralizerOf_smul_sum_pSection`
              (`|C_G(x)| • Σ_{u∈S(x)} f = |G| • Σ_{y∈C⁰} f(xy)`, `f` 類関数)
            * 段 168 `card_centralizerOf_smul_sum_sectionProjectiveCharacter` (内積の前半)
            * 段 169 `centralizerOf_inv` (`C_G(x⁻¹) = C_G(x)`)
          - [x] 🎯🎯 **内積計算の後半 完了 (2026-08-05、段 170)**
            `inner_sectionProjectiveCharacter_eq` = `[Φ^x_μ, χ] = d^{x⁻¹}_{χμ}`。
            `x⁻¹` 側の分裂データを一切持ち込まず、**`d : ι → K` を引数で受け、その
            特徴づけを `C_G(x)` の中だけで書く**: `hd : ∀ y ∈ C_G(x)⁰,
            Σ_τ d τ · μ_τ(y⁻¹) = χ((xy)⁻¹)`。これは `d^{x⁻¹}` の定義
            `χ(x⁻¹z) = Σ_τ d_τ μ_τ(z)` を `z = y⁻¹` で読んだもので
            (`C_G(x⁻¹) = C_G(x)` = 段 169)、`y⁻¹` は部分群の中の逆元なので型が 1 つで済む。
            ✅ **前 session の `Finset.filter` `Decidable` インスタンス障害の解法**:
            filter を自分で書いて `rw` しようとするのが誤り。**`pairingZero` 側の filter と
            段 168 側の filter を `Finset.sum_congr` + `Finset.ext` + `isPRegular_coe_iff` で
            一度だけ橋渡し**すればよい ([[lean-instance-defeq-traps]] に近い罠)。
          - [x] 🎯 **段 171 (refactor)**: 上の中核を `CartanInverse` の
            `sum_projectiveIndecomposableCharacter_mul_eq` に括り出した —
            「`p`-正則類上で `F(y) = Σ_τ d_τ τ(y⁻¹)` と展開される任意の `F`」について
            `Σ_{y∈G⁰} Φ_μ(y) F(y) = |G| d_μ`。⚠ **和の範囲を `Finset.filter` でなく
            `p`-正則性で特徴づけられた抽象 `Finset s` で受ける** ので、呼び出し側が
            `pairingZero` の `Decidable` インスタンスに合わせる必要が消える。
            以降 (5.13) の全ステップがこの 1 本で書ける。
          - [x] 🎯🎯🎯 **(5.13)(b) 完了 (2026-08-05、段 172、新 leaf
            `Modular/GeneralizedDecompositionOrthogonality.lean`)**:
            `sum_mul_generalizedDecompositionNumber_eq_cartanMatrix` =
            **`Σ_{χ∈Irr(G)} d^{x⁻¹}_{χμ} · d^x_{χφ} = c_{μφ}`**。
            `x⁻¹` 側の数は `C_G(x)` の中で書いた定義式を満たす族 `dinv` として受け取る
            (移送ゼロ)。**教科書と違い `Φ^{x⁻¹}_φ` を作らない**経路:
            * 両方の一般化分解数を段 171 で `C_G(x)⁰` 上の和に直す
              (🎯 `card_centralizerOf_mul_generalizedDecompositionNumber` =
              `|C_G(x)| d^x_{χφ} = Σ_{z∈C⁰} Φ_φ(z) χ(x z⁻¹)`)
            * 生じた二重和を `G` の**第二直交関係** `sum_character_inv_mul_character`
              (`Modular/OrdinaryColumnOrthogonality`、既存) で潰す
            * 🎯🎯 `sum_character_mul_generalizedDecompositionNumber` =
              `Σ_χ χ((xy)⁻¹) d^x_{χφ} = Φ_φ(y⁻¹)` (= `Φ^{x⁻¹}_φ` の section 上の値を
              その関数を作らずに計算したもの)
            * 重み `|C_G(xy)| = |C_{C_G(x)}(y)|` が `y⁻¹` の `C_G(x)`-類の大きさを
              `|C_G(x)|` に対して打ち消す (🎯 `PSection` の
              `card_centralizerOf_mul_eq_card_centralizer_subtype` = **段 164
              `C_G(xy) = C_G(x) ⊓ C_G(y)` の初めての消費点**; 段 164 の「未使用」注記は解消)
            支持: `OrdinaryColumnOrthogonality` に `sum_eq_card_smul_of_forall_isConj` /
            `card_mul_card_centralizer_of_forall_isConj` (共役で切り出した `Finset` での
            類の勘定) を新設。
            ⚠ **`Finset` を `set` で置くと `Finset.sum_filter` が let-値を透かして
            誤爆する** — 抽象化したい `Finset` は `obtain ⟨s, hs⟩ : ∃ s, ∀ z, z ∈ s ↔ P z`
            で不透明に取る。
            ⚠ `IsConj` は `def` なので `rw` 後に `∃ c, SemiconjBy …` へ展開されることがあり、
            `h.inv'` / `h.symm` のドット記法が壊れる → `IsConj.inv' h` と明示する。
          実測 (2026-08-05): (5.1) `generalizedDecompositionNumber` /
          (5.2) `generalizedDecompositionNumber_eq_zero` / (5.8)
          `..._sum_generalizedDecompositionNumber_inducedBlockOfCentralizer` は**既存**
          (`Modular/GeneralizedDecomposition.lean`, `SecondMainTheorem.lean`,
          `SecondMainBlockForm.lean`)。Cartan 行列 `cartanMatrix` も既存
          (`Modular/CartanMatrix.lean`)。⟹ (5.13) は「既存の 2 つを繋ぐ」段。
        * [x] 🎯 **完了 (2026-08-05、段 178、`RepresentationTheory/CharacterInvolution`)**:
          `exists_intCast_character_of_mul_self_eq_one` = 「`t² = 1` なら `χ(t) ∈ ℤ` の像」
          (`character_eq_of_mul_self_eq_one`: `χ(t) = 2·dim V₊ − dim V`、
          `(1 + ρ t)/2` が `+1`-固有空間への射影)。
          ⚠ **設計判断**: 原文の注 `d^x_{χφ} ∈ ℤ[ζ]` は `χ|_H` の `Irr(H)` 分解を要するが、
          (7.2) がそれを使うのは involution `t` の `d^t_{χ1} = χ(t)` の形だけなので、
          **対合の指標値の整数性を直接示す方が短く、標数 ≠ 2 の任意の体で成り立つ**
          (代数的整数論も 1 の冪根も不要)。repo の (5.1) が基底論法ゆえ整数性を
          見ていない件はこの経路では問題にならない。
        ⟹ **(7.2) の部品は 2026-08-05 に全て揃った**。次は (7.2) 本体の組み立て:
        第 1 部 (involution の類が 1 個か 3 個) と第 2 部
        (`k(B₀) − l(B₀) = 1` から `Irr(B₀) = {1_G, χ₁, χ₂, χ₃}` と `χ_i(t) = ±1`)。
        - [x] 🎯 **第 1 部の核 完了 (2026-08-05、段 180)**:
          `eq_or_eq_or_eq_iterate_of_odd_of_klein` =「**奇数回反復が恒等**な非自明自己準同型は
          Klein 四元群の involution 上で推移的」。⚠ `Aut(Z₂×Z₂) ≅ Sym(3)` も `|Aut(P)| = 6` も
          `Equiv.Perm` の位数計算も要らない — downstream で要るのは
          「`N_G(P)/C_G(P)` は奇位数」(`P` が可換 Sylow-2 ゆえ) だけ。
          支持 = `eq_of_fixed_two_of_klein` / `forall_cube_eq_self_of_klein`。
        - [x] 🎯🎯 **第 1 部の主内容 完了 (2026-08-05、段 181、`GroupTheory/KleinFourSylowFusion`)**:
          `isConj_of_klein_sylow` =「`P` が Klein 四元群 Sylow-2 で `N_G(P)` に `P` を
          中心化しない**奇位数**の元があれば `G` の任意の 2 つの involution は共役」。
          支持 = `exists_conj_mem_sylow_of_mul_self_eq_one` (任意の involution は
          Sylow-2 の中へ共役)。⚠ 仮説を「`N_G(P) ≠ C_G(P)`」でなく「奇位数の `g` が在る」
          の形にした (両者の同値性 = `|N_G(P) : C_G(P)|` が奇数、は独立した Sylow の勘定)。
        - [x] 🎯🎯 **第 1 部 完了 (2026-08-05、段 182)**:
          `isConj_of_klein_sylow_of_not_centralizes` =「`N_G(P)` が `P` を中心化しない
          ⟹ involution の類は 1 個」。支持 = `exists_odd_not_centralizes` (証人は奇位数に
          取り直せる) + `mem_of_isPElement_of_mem_normalizer` (`p`-元が Sylow `p`-部分群を
          正規化するならその中に入る — mathlib の `IsPGroup.inf_normalizer_sylow` から)。
          ⚠ **経路案どおり `|N:C|` の奇数性の勘定 (relindex/Sylow 指数) を丸ごと回避できた**。
        - [x] 🎯🎯 **第 1 部の BS 向き 完了 (2026-08-05、段 183、
          `GroupTheory/KleinFourNormalComplement`)**:
          `hasNormalPComplement_of_not_isConj` =「共役でない involution が 2 つあれば
          正規 2-補群」(段 182 の対偶 + 既存 Burnside)。
          `exists_not_isConj_of_mem_center` =「中心的 involution `t` の類は `{t}` なので
          Klein 四元群 Sylow-2 を持つ群は単一類を持てない」(原文 "C cannot have a unique
          class of involutions (because t is central in C)" に対応)。
          ⟹ **BS が要求する「`C_G(t)` は正規 2-補群を持つ」が繋がった**。
          ⚠ 「正規 2-補群 ⟹ 類はちょうど 3 個」の側は BS では使わないので未着手 (低優先)。
        - [ ] **第 2 部 (指標側)** = `Irr(B₀) = {1_G, χ₁, χ₂, χ₃}`、`χ_i(t) = ε_i = ±1`、
              `χ_i(1) ≡ ε_i mod 4`、`1 + Σ ε_i χ_i(s) = 0`。
          **⚠ 経路の短縮 (2026-08-05 に確定)**: `k(B₀) = 4` に (5.12) は要らない。
          (5.13)(b) の対合版 + `b₀` の Cartan 行列 `(4)` + 非零性 + 整数性 + `d^t_{1_G,1} = 1`
          だけで `Σ_{χ∈Irr(B₀)} (d^t_{χ1})² = 4` の分解が `4 = 1+1+1+1` に限られる。
          `|IBr(B₀)| = 3` の側だけが `k(B₀) − l(B₀) = l(b₀) = 1` = (5.12) を要する。
          - [x] 🎯🎯 **段 184 (`Modular/DecompositionBlockDiagonal`)**: `D` はブロック対角
                (`d_{χφ} ≠ 0 ⟹ φ ∈ B(χ)`)。既存 `CartanBlockDiagonal` は 2 つの Brauer 指標の
                中心指標が等しいまでで、`blockOfIrr` と `Quotient.mk blockSetoid` を結ぶ形が
                無かった。支持 = `asAlgebraHom_reduction_center_eq`。
          - [x] 🎯🎯 **段 185 (`Modular/PrincipalBlockCartanEntry`)**: (6.13) の Cartan 行列版
                `|N| · c_{φ₀φ₀} = |G|` (= `b₀` の Cartan 行列は `1×1` の `(|G|_p)`)。
          - [x] 🎯🎯 **段 186 (`Modular/GeneralizedDecompositionInvolution`)**:
                (5.13)(b) の対合版 `Σ_{χ∈Irr(G)} (d^t_{χφ})² = c_{φφ}`
                (`t⁻¹ = t` ゆえ同じ族が `dinv` の条件を満たす)。
          - [x] 🎯🎯 **段 187 (`Modular/SecondMainPrincipalBlock`)**: `χ(x y) = d^x_{χφ₀}`
                (原文 p.132「By Corollary (5.8) and the third main theorem」)。
                = (5.8) + **第三主定理の逆** (`eq_principalBlock_of_inducedBlockOfCentralizer_eq`
                = 既存 Külshammer 版を `Q = ⟨x⟩` へ特殊化) + (6.13)
                (`irreducibleBrauerCharacter_principalBlock_eq_one`: `B₀` の唯一の Brauer 指標は
                `p`-正則類上で定数 1)。
                ⚠ `[DecidablePred (· ∈ C_G(⟨x⟩))]` を section 変数にすると
                `inducedBlockOfCentralizer` 内部の `Classical` 実例と食い違って defeq が壊れる。
          - [x] 🎯 **段 188**: 第三主定理の**易しい向き**の `p`-元版
                (`inducedBlockOfCentralizer_principalBlock`) ⟹ `Irr(B₀)` の外で `d^t_{χφ₀} = 0`
                (段 186 の平方和が `Irr(B₀)` 上の和になる) +
                `Algebra/SumSquaresFour` (`Σ a_i² = 4`, 全非零, ある `a_{i₀} = 1`
                ⟹ 全項 ±1 かつ項数 4)。
          - [x] 🎯🎯 **段 189-190 (`Modular/SecondMainPrincipalBlock`)**:
                * `character_eq_generalizedDecompositionNumber_of_not_isPRegular`:
                  「非自明な `p`-元は全て `x` に共役」の下で**全 `p`-特異元** `u` に対し
                  `χ(u) = d^x_{χφ₀}` (`u = u_p u_{p'}` を `c` で戻して段 187)。
                  ⚠ `rw` は `⟨_, hmem⟩` の証明部が `x` 依存で motive が壊れる → `change` 経由。
                * `generalizedDecompositionNumber_ne_zero_of_blockOfIrr_principal`:
                  `χ ∈ Irr(B₀)`, `x ≠ 1` なら `d^x_{χφ₀} ≠ 0` (対偶 + Navarro (3.18))。
                  ⚠ 原文は「involution で消える」から (3.18) へ飛ぶが、(3.18) が要るのは
                  **全 2-特異元での消滅**なので段 189 を先に経由する必要がある。
          - [x] 🎯🎯🎯 **段 191-192 完了 (2026-08-05、`Modular/PrincipalBlockInvolution`)**:
                * `sum_sq_character_involution_eq_cartanMatrix`:
                  `Σ_{χ∈Irr(B₀)} χ(t)² = c_{φ₀φ₀}` (段 186 + 段 188 + 段 187 を `y=1` で読む)。
                * `nontrivial_blockOfIrr_principal`: `|Irr(B₀)| ≠ 1`。弱ブロック直交性
                  `Σ_{χ∈Irr(B₀)} χ(1)χ(t) = 0` ((5.11) の `h=1`) が単元集合を許さない。
                  ⟹ **自明指標の添字を Wedderburn 分解から取り出す必要が無い** (当初想定より短い)。
                * `card_blockOfIrr_principal_eq_four_and_character_involution`:
                  **`|Irr(B₀)| = 4` かつ `χ(t) = ±1`** (段 178 の整数性 + 段 190 の非零性 +
                  `Algebra/SumSquaresFour`)。
                * `intCast_card_add_three_mul_character_involution` /
                  `card_modEq_character_involution`: **`χ(1) ≡ ε mod 4`**。
                  内積を作らず既存の `sum_character_eq_card_mul_finrank_invariants`
                  (`Σ_{h∈H} χ(h) = |H|·dim V^H`) を `ρ|_P` に適用する (整数性が次元から自動)。
                ⚠ 実装メモ: `Finset.sum_subtype s h f : Σ_{a∈s} f a = Σ_{a:Subtype p} f ↑a` を
                使うので、整数値の族は **`κ` 上の関数**として取る (subtype 上に取ると滑る)。
                ⚠ 最後の等式 `1 + Σ ε_i χ_i(s) = 0` は既存のブロック直交性 (5.11)
                (`sum_character_blockOfIrr_eq_zero`) を `g = t`, `h = s` で読むだけなので
                新規補題は不要。
          - [x] 🎯🎯 **段 193-194 (2026-08-05): (7.4) が要る「階数 3」を (5.12) 抜きで取得**。
                (7.4) は `l(B₀) = 3` を「`|𝒴| = |IBr(B₀)|` ゆえ 3 元が basic set」の形で使うが、
                実際に効いているのは **`{χ⁰ : χ ∈ Irr(B₀)}` の張る格子の階数が 3** ということだけ。
                そして関係式の空間は**高々 1 次元**であることが直接示せる:
                `Σ_χ a_χ χ` が `G⁰` で消えるとき、`p`-特異元上では各 `χ ∈ Irr(B₀)` が `χ(t)` を
                取る (段 189+187) ので、その関数は「2-特異元の指示関数の `c = Σ a_χ χ(t)` 倍」。
                ⟹ `a ↦ c` は単射 (`eq_zero_of_vanishing_on_pRegular`)、
                従って `c' • a = c • a'` (`smul_eq_smul_of_vanishing_on_pRegular`)。
                `|Irr(B₀)| = 4` (段 191) と合わせて階数 = 4 − 1 = 3。
                ⟹ **下記の (5.12) 適用 + `C_G(1) = ⊤` 移送は不要になった** (記録として残す)。
          - [x] 🎯🎯 **段 195-196 (2026-08-05): (7.4) の中核が揃った**。
                * `sum_character_mul_character_involution_eq_zero`:
                  `Σ_{χ∈Irr(B₀)} χ(s)χ(t) = 0` (`s` は `p`-正則)。
                  ⚠ **(5.11) は型が合わない** — `C_G(pPart p g)` 上の datum を要求し、
                  `pPart p t = t` は命題的等式 (`g = s` に取ると `C_G(1) = ⊤`)。代わりに
                  `sum_character_mul_generalizedDecompositionNumber_eq_zero` を `v = s` で使うと
                  **`C_G(t)` 上の datum のまま**通る。
                * `eq_zero_of_vanishing_on_pRegular_of_apply_eq_zero`:
                  関係式空間 = `(χ(t))` の張る直線 (定数 `Σχ(t)² = c_{φ₀φ₀} = 4 ≠ 0`) で
                  全座標非零 ⟹ **任意の 3 つの `χ⁰` が独立**。張る側は上の関係式から直接。
                ⟹ (7.4) に残るのは **basic set という語彙の定義層と行列 `D`/`C` の書き下し**のみ。
          - [ ] ~~**残り = `l(B₀) = |IBr(B₀)| = 3`**~~ (段 193-194 で迂回済; `l(B₀)` そのものを
                数える必要が出たら以下の経路)
                経路 = 既存の (5.12) (`card_blockOfIrr_eq_card_inducedBlockOfCentralizer`) を
                (7.2) の状況に当てる:
                * 2-元の `G`-類はちょうど 2 個 (`[1]` と `[t]`) — Klein 四元群 Sylow-2 で
                  非自明 2-元は involution、かつ involution の類は 1 個。
                * `D = [t]` の項 = `l(b₀) = 1` (段 187 の第三主定理の逆 + (6.13))。
                * `D = [1]` の項 = `l(B₀)`。
                ⟹ `k(B₀) = l(B₀) + 1`、`k(B₀) = 4` (段 191) より `l(B₀) = 3`。
                ⚠ **唯一の摩擦 = `centralizerOf (1 : G) = ⊤` の移送**。(5.12) の列は
                `IBr(C_G(x_D))` で添字づけられており、`D = [1]` では `C_G(1) = ⊤` なので
                `↥⊤` 上の modular datum になる。必要なのは:
                  (i) `pElementRep [1] = 1` (`Quotient.out` の類が `[1]` ゆえ 1);
                  (ii) `π D₀` を `G` の datum の**引き戻し**に取る (5.12 は任意の datum で成り立つ
                       ので instantiate してよい) ⟹ 添字型 `ι D₀ = ιG` が**構成的に一致**し、
                       `IBr(↥C_G(1)) ↔ IBr(G)` の対応が自明になる。
                       道具 = `MonoidAlgebra.domCongr k k f : k[H] ≃ₐ[k] k[G]`
                       (mathlib、`domCongr_single` / `coeff_domCongr` 付き)、
                       `f : ↥(centralizerOf 1) ≃* G` は
                       `Subgroup.equivOfEq (centralizerOf_one) ≪≫* Subgroup.topEquiv`。
                       ⟹ **一般の `MulEquiv` 沿いの modular datum 移送**として新 leaf 化するのが
                       筋 (`hπ`/`hlin`/`hkerJ`/`hnil` が全て機械的に移る)。
                  (iii) `Q = ⟨1⟩ = ⊥` に対し `Br_⊥ = id` (`brauerTrunc` の台が `C_G(⊥) = ⊤`)
                       ⟹ `b^G = b`、つまり `D = [1]` の列は通常の分解数。
                ⚠ **`D = [t]` 側だけなら移送不要**: 2-元類がちょうど 2 個なので
                `card{D₀ の列} = k(B₀) − card{D₁ の列} = 4 − 1 = 3` は移送なしで出る。
                移送が要るのはそれを **`G` 側の `|IBr(B₀)|`** と同一視する所だけ。
        ⚠ (5.12)/(5.13) は Ch.5 なので**文書順で先**。上流優先で (5.13)(b) →
        (5.12) → (7.2) の順に当たる。
        - [x] 🎯🎯 **(5.13)(a) 前半 完了 (2026-08-05、段 173)**:
          `sum_mul_generalizedDecompositionNumber_eq_zero` =
          「`x`, `y` が共役でない `p`-元なら `Σ_{χ∈Irr(G)} d^{x⁻¹}_{χμ} · d^y_{χφ} = 0`」。
          支持 = 🎯 `sum_character_mul_generalizedDecompositionNumber_eq_zero`
          (`v⁻¹ ∉ S(y)` なら `Σ_χ χ(v) d^y_{χφ} = 0` = `Φ^{y⁻¹}_φ` の section 外での消滅) +
          `BrauerBasis` の `eq_zero_of_sum_irreducibleBrauerCharacter_eq_zero`
          (**`IBr` の線型独立性**)。
          ⚠ **どちらも射影不可分指標を使わない** — 係数は `IBr` の線型独立性で決まるので、
          各中心化群について必要なのは modular datum `π` だけで Wedderburn 分解 `e` は不要。
          Navarro 自身の論法 ("by the linear independence of the elements of IBr(H)") と同じ。
          結果として仮定が減り `unusedFintypeInType` lint も自然に解消した
          (**linter が数学的により良い証明を指していた**例)。
        **⏸ 次の一手 = (5.12)** (`k(B) = Σ_i Σ_{b ∈ Bl(C_G(x_i)), b^G = B} l(b)`)。
        (5.13)(b) は 2026-08-05 に完了 (段 172)、(5.13)(a) 前半も同日 (段 173)。
        **(5.12) の証明 (原文 p.110、ページ画像で確認済)**:
        * `R_i` = `C_G(x_i)` の `p`-正則類の代表系とすると `{x_i y}_{i, y∈R_i}` が
          `G` の共役類の完全代表系 ⟹ `k(G) = Σ_i |IBr(C_G(x_i))|`
          (`p`-section が `G` を分割する = 段 162、section の助変数化 = `mem_pSection_iff` +
          `isConj_centralizer_of_isConj_mul`、`|IBr(H)| = #cl(H⁰)` = `OrdinaryIrrCount` 既存)
        * `k(G) × k(G)` 行列 `J = (d^{x_i}_{χμ})` を作ると (5.13) より
          `J̄ᵗ J = diag(C^{(x_1)}, …, C^{(x_k)})` ⟹ **`J` は正則**
          (Cartan 行列が正則 = `sum_cartanMatrix_mul_pairingZero` から従うはず)
        * 第二主定理 (5.8 = `..._eq_zero_of_inducedBlockOfCentralizer_ne`、既存) より
          `J` は `Irr(B_s)` × `{(x_i,μ) : bl(μ)^G = B_s}` でブロック対角
        * 正則なブロック対角行列の各ブロックは正方 ⟹ `k(B) = Σ_i Σ_{b^G=B} l(b)`
        ⚠ 必要な新規インフラ: (i) 全 `p`-元類にわたる添字型と `J` の構成、
        (ii) 「正則なブロック対角行列の各対角ブロックは正方」の線型代数、
        (iii) `Irr(G)` / `∐_i IBr(C_G(x_i))` のブロック別分割。
        **(7.2) が (5.12) を使う形 (原文 p.132)**: `p = 2`、`P = Z₂×Z₂` が Sylow で
        involution が 1 類のとき `k(B₀) − l(B₀) = l(b₀) = 1`
        (2-元の類は `1` と `t` の 2 つだけ; `C_G(t)` は正規 2-補群を持つので
        `IBr(b₀) = {1}` = 段 100 の (6.13))。
  - [ ] (旧) 次の一手の詳細 (2026-08-05 に確定した経路、実装済):
        (2026-08-05 に原文 p.62 のページ画像で (3.18) の証明を確定した結果、
        **教科書の (d)⟹(e) 経由 (`e_χ ∈ Z(𝒪G)` + Thm (3.9)) より短い道**が見えた)。
        `p ∣ |G|`・`blockOfIrr i = B₀`・「`χ_i` が全 `p`-singular 元で 0」から矛盾:
        * `Σ_{g∈G⁰} χ(g) = Σ_{g∈G} χ(g) = |G|·d`, `d = dim V^G`
          (`sum_character_eq_card_mul_finrank_invariants` を `H = G` で)
        * `ω^L_i(Ĝ⁰)` は **𝒪 の単元**: `blockCharacter_blockOfLattice_mapRingHom` で
          `residue(ω^L_i(Ĝ⁰)) = λ_{B₀}(Ĝ⁰*) = |G⁰|*`、`p ∤ |G⁰|`
          (`not_dvd_card_isPRegular`) ゆえ非零。
        * `centralScalar_pRegularSum_mul_character_one` で
          `ω_χ(Ĝ⁰)·χ(1) = Σ_{g∈G⁰}χ(g) = |G|·d`。
        * **`d = 0` の場合**: 左辺は単元×`χ(1) ≠ 0` で非零、右辺 0 ⟹ 矛盾。
        * **`d ≠ 0` の場合**: `V^G ≠ ⊥` ⟹ 表現が自明 ⟹ `χ(g) = χ(1) ≠ 0` (∀g)。
          Cauchy で位数 `p` の元 (= `p`-singular) を取ると仮説に矛盾。
        **新規に要るのは 1 本だけ** = 🔨 `wedderburnRepresentation e i` が
        `V^G ≠ ⊥` なら自明であること。証明は module の単純性を経由せず:
        不変ベクトル `v ≠ 0` に対し `(e a i).mulVec v = ε(a)•v` (∀`a ∈ K[G]`、
        `single g 1` 上で確認して線型性)、`e` の全射性で任意の行列単位 `E_{l j}`
        (`v j ≠ 0` なる `j`) を取ると `Pi.single l 1 ∈ span{v}` ⟹ `card (m i) = 1`
        ⟹ スカラーで `ρ g v = v` ⟹ `ρ g = 1`。
        ⚠ **教科書の (d)⟹(e) (`e_χ` の整数性 + Thm (3.9) で `Irr(B) = {χ}`) は
        通らなくてよい** — (7.2) が要るのは矛盾だけ。
- [ ] **102: 🎯🎯🎯 BS 本証明 (pp.139–146)** → `brauerSuzuki_quaternionSylow_q8` の `sorry` 置換

  ### 依存の洗い出し (2026-08-05、原文 p.138-139 の前置きと本文から確定)

  ⚠ これまで「BS 本証明 8 ページの中身は未読 = 唯一の未知」と flag していた件の答え。

  **(A) modular 側の引用** (本文中に現れるもの): (3.9) / (5.8)×2 / (5.10) /
  (6.10) / (6.11) / (6.12) / (6.13)×2 / **(7.4)** / **(7.6)**。
  ⟹ **Ch.5 側は本 session で全て揃った**。Ch.6 も (6.10)-(6.13) は段 100 で完了。
  残る modular 依存は **(7.4) と (7.6)** だけ (どちらも (7.3) basic set の上に乗る)。

  **(B) 群論側の標準事実** — Navarro が p.138 で「several standard group theoretic facts」
  として明示的に列挙しているもの。repo 実測 (2026-08-05):
  * `Aut(Q₈) ≅ Sym(4)` — **部分的**。`Isaacs/Ch03_SplitExtensions/Problems3F.lean` に
    `quaternionSwapIJAut` / `quaternionSwapIKAut` / `quaternionTwo_exists_mulAut_map_zpowers`
    (`Aut(Q₈)` の推移性) はあるが `≅ Sym(4)` 全体は無い。
    BS が使うのは「`N_G(P)/C_G(P) ≤ Sym(4)`」+「その Sylow-2 は `PC_G(P)/C_G(P)` が唯一」
    +「位数 3 の元が取れる」なので、段 179-180 と同じく**全同型を作らずに済む可能性が高い**。
  * 巡回 Sylow-2 ⟹ 正規 2-補群 — `Isaacs.Ch05.hasNormalPComplement_of_isCyclic_sylow_of_dvd_index`
    (`Problems5C12.lean:61`) が近い。仮説の形を要確認。
  * 「involution 2 つが生成する群は位数 `2·o(t₁t₂)` の二面体群」— **無い**。
    (`Isaacs/Ch06_FrobeniusActions/Main.lean` の
    `dihedralOrQuaternionOrSemiDihedral_of_...` は別の主張。)
  * 「正規 `p`-補群 ⟺ `P` が `G`-fusion を制御」— ✅ **既存**
    (`Isaacs.Ch05.hasNormalPComplement_iff_controlsOwnFusion` = Isaacs Thm 5.25)。
  * `Q₈` の指標表 (5 類、1 次 4 個 + 2 次 1 個) — **無い**。

  **(C) 証明の骨格** (p.139): `P` を位数 8 の四元数 Sylow-2、`t` をその involution とし
  `t ∈ Z(G)` を示す。真の正規部分群 `N` で `t ∈ N` なるものが取れれば、`P ⊓ N` が巡回なら
  `N` は正規 2-補群を持ち `O_{2'}(G) = 1` から `N` は巡回 2-群 ⟹ `t ∈ Z(G)`;
  `P ≤ N` なら `|G|` の帰納法。⟹ **目標は「`t` を核に含む主ブロックの非自明指標を見つける」**。
  最初の段は「位数 4 の元は全て `G`-共役 (実は `C_G(t)`-共役)」で、
  ここで fusion 制御 + `Aut(P) = Sym(4)` を使う。以降 "Analysis at y" (p.139-) と続く。

  ### (7.3)-(7.6) の読解 (2026-08-05、原文 pp.133-137 のページ画像で確定)

* **(7.3) DEFINITION (p.133)**: ブロック `B` の **basic set** = アーベル群
  `{Σ_{χ∈Irr(B)} a_χ χ⁰ | a_χ ∈ ℤ} ⊆ cf(G⁰)` の基底。`IBr(B)` はその一例。
  basic set `𝓑` に対し `χ⁰ = Σ_{φ∈𝓑} d_{χφ} φ` で整数 `d_{χφ}` が一意に決まり、
  `D_𝓑 = D_B U` (`U ∈ GL(n,ℤ)` は `IBr(B) → 𝓑` の基底変換)、
  Cartan は `C_𝓑 = Uᵗ C_B U` (p.134)。
* **p.134 の remark (実際に使う basic set の作り方)**: `𝒴 ⊆ Irr(B)` で `|𝒴| = |IBr(B)|`、
  かつ `Irr(B) − 𝒴` の各 `χ` について `χ⁰` が `{η⁰ : η ∈ 𝒴}` の整数結合なら、
  任意の符号 `ε_η = ±1` に対し `{ε_η η⁰ : η ∈ 𝒴}` は basic set。
  (⟸ は Lemma (3.16): 各 `φ ∈ IBr(B)` は `{χ⁰}` の整数結合。)
* **(7.4) COROLLARY (p.134)**: (7.2) の仮定 + involution の類が 1 個のとき、
  記号を `ε₁ = 1`, `ε₃ = −1` に取れる。このとき `(χ₃)⁰ = 1_{G⁰} + (χ₁)⁰ + ε₂(χ₂)⁰` で
  `{1_{G⁰}, (χ₁)⁰, ε₂(χ₂)⁰}` は **奇数次数**の basic set、
  `D = [[1,0,0],[0,1,0],[0,0,ε₂],[1,1,1]]`, `C = [[2,1,1],[1,2,1],[1,1,2]]`。
  ⚠ **`l(B₀) = 3` を使う** (上記 remark の `|𝒴| = |IBr(B)|`)。
  ⚠ `1 + ε₁χ₁(s) + ε₂χ₂(s) + ε₃χ₃(s) = 0` を `s = 1` で使って「符号は 2 種類ある」を出す
  ので、**自明指標 `χ₀ = 1_G` を Irr(B₀) の元として名指しする**必要がここで初めて生じる。
* **(7.5) LEMMA (pp.135-136)**: basic set 版の (5.8)(a) と (5.13)(a)/(b)。
  一般化分解数の basic-set 版 `d^x_{χφ} = Σ_{ψ∈Irr(b)} [χ_H, ψ] (ψ(x)/ψ(1)) d_{ψφ}` を定義し、
  旧版との関係 `d^x_{χφ} = Σ_{μ∈IBr(b)} d^x_{χμ} u_{μφ}` (式 (1)) から (a)-(d) が従う。
  (d) は `Σ_{χ∈Irr(B)} conj(χ(xz)) d^y_{χη} = 0` (`y` が `x` に非共役)。
* **(7.6) THEOREM (p.137)**: `P ⊴ G` が `p`-部分群で `G/C_G(P)` が `p`-群なら、
  `Ḡ = G/P` について `B̄ ↦ B` は `Bl(Ḡ) → Bl(G)` の全単射で、`IBr(B̄) = IBr(B)`、
  `C_B = |P| C_B̄`。証明の鍵は `G⁰ → Ḡ⁰` が全単射 (`G⁰ ⊆ C_G(P)` ゆえ `o(yz) = o(y)o(z)`) と
  `[φ,θ]⁰_G = (1/|P|)[φ̄,θ̄]⁰_Ḡ`。

⟹ **着手順** (文書順): ~~(7.2) 第 2 部~~ (2026-08-05 完了、段 184-192) →
  ~~`l(B₀) = 3`~~ (段 193-194 で「関係式は高々 1 次元」に置換、(5.12) 不要) →
  ~~(7.4) の中核~~ (段 195-196 で完了) →
  ~~(5.13)(b) の一般化~~ (段 197-198 で完了) →
  **(7.3) basic set の定義層 → (7.4) の行列 `D`/`C` → (7.5) → (7.6)** →
  上記 (B) の群論 3 件

### ⚠ BS 本証明 pp.139-140 の読解 (2026-08-05) — **設計に効く発見**

"Analysis at y" (p.139-140) は **(7.2) 第 2 部と同じ機械**を、対合 `t` でなく
**位数 4 の元 `y`** に対して回す:
`⟨y⟩` が `C_G(y)` の巡回 Sylow-2 ⟹ 正規 2-補群 ⟹ (6.13) で `IBr(b₀) = {1}` ⟹
(5.8)+第三主定理で `χ_i(y) = d^y_{χ_i 1}` ⟹ Cartan `(4)` と (5.13)(b) で
`Σ_i χ_i(y)² = 4` ⟹ ブロック直交性で `Σ_i χ_i(y)χ_i(1) = 0`。
⟹ **段 185/187/188/195 は既に `x` について一般**で、そのまま `y` に使える。
段 186 (平方和) だけが `t*t = 1` を使っていたので、段 197-198 で
`x ~ x⁻¹` (四元数群の位数 4 の元が満たす) へ一般化した。
~~残る `y` 固有の課題 = `χ_i(y) ∈ ℤ`~~ → **段 199 で完了**
(`RepresentationTheory/CharacterOrderFour`): `y⁴ = 1` なら `u = (ρy + ρy⁻¹)/2` が `u³ = u`
なので `e_± = (u² ± u)/2` は冪等、`χ(y) + χ(y⁻¹) = 2(dim im e₊ − dim im e₋)`。
`y ~ y⁻¹` なら左辺 = `2χ(y)`。⚠ 原文の `ℤ[ζ₄]` + Galois を使わず、標数 ≠ 2 だけで済む
(段 178 と同じ設計)。

⟹ **BS "Analysis at y" (p.140) の 4 部品は全て揃った**:
  `χ_i(y) = d^y_{χ_i1}` (段 187) / `b₀` の Cartan `(4)` (段 185) /
  `Σ_i χ_i(y)² = 4` (段 197-198) / `Σ_i χ_i(y)χ_i(1) = 0` (段 195)。
  ~~「`⟨y⟩` が `C_G(y)` の Sylow-2 ⟹ 正規 2-補群」~~ → **段 200 で完了**
  (`GroupTheory/CentralSylowComplement`: `P ≤ Z(G)` なら `N_G(P) ≤ C_G(P) = G` で既存 Burnside)。
  ⚠ `hasNormalPComplement_of_isCyclic_sylow_of_dvd_index` は別物 (`N ⊴ G` 用) で使わない。

### ⚠ "Analysis at t" (p.141) の読解 — **basic set の枠組みが本当に要る所**

`C_G(t)/⟨t⟩` は Klein 四元群 Sylow-2 を持ち involution の類は 1 個 (`P` の位数 4 の元が
`C_G(t)`-共役だから) なので **(7.4) がそこで使える**: `b̄₀` の basic set `{1, ψ₁, ψ₂}`
(奇数次数) と Cartan `c_ij = 1 + δ_ij` が得られる。次に **(7.6)** で `C_G(t)` 自身の `b₀` へ
持ち上げる (同じ basic set、Cartan は `|⟨t⟩| = 2` 倍)。そのうえで **(7.5)(a)** と第三主定理から
  `χ_i(tu) = Σ_{j=0}^{2} d^t_{χ_iψ_j} ψ_j(u)`  (`u ∈ C_G(t)⁰`)
となり、(7.5)(b,c,d) が `(D^t_i, D^t_j) = 2(1+δ_ij)`, `(D^y_0, D^t_j) = 0`,
`(χ(1), D^t_j) = 0` を与える。

⟹ (7.3)/(7.5)/(7.6) は迂回できない。うち **(7.5) は段 201 で完了**
(`Modular/BasicSetDecomposition`)。

⚠ **設計判断 (段 201)**: basic set を「格子 `L_B = {Σ a_χ χ⁰}` の基底」として型で作ると重いが、
(7.5)/(7.4) が実際に使うのは **`IBr(b)` からの整数基底変換行列 `U`** だけ。原文 p.135 の式 (1)
`d^x_{χφ} = Σ_μ d^x_{χμ} u_{μφ}` を**定義**に採ると (7.5) は既存 `IBr` 版の上の**双線型代数**に
還元される: (a) は「`u_{μφ} ≠ 0` の全 `μ` で `d^x_{χμ} = 0`」の合成、(b)(c) は 2 列の内積が
`IBr` 列の内積行列の **`U`-合同 `Uᵗ c U`** になること (段 197 の (5.13)(b) を入れて `UᵗCU`)。
⟹ **格子・基底の型を作らずに済む**。段 202 で展開の形
`Σ_φ d^x_{χφ} η_φ(w) = χ(xw)` (原文 p.141 の `χ_i(tu) = Σ_j d^t_{χ_iψ_j} ψ_j(u)`) も追加。
⚠ **`U` の向き**: 整合するのは「`μ` を `η` で表す」向き (`μ = Σ_φ u_{μφ} η_φ`)。
`D_𝓑 = D_B U` と両立するのはこちらで、逆向きだと `UUᵗ = I` が要って成立しない。
残るのは **`U` の構成 = (7.4)** と、**(7.6)**。
⚠ (7.4) の出力は Navarro では `D_𝓑` (= `Irr(B₀) × 𝓑` 行列) であって `U` ではない。

### (7.4) の `U` について確定した設計事項 (2026-08-05)

段 195-196 から `𝓑 = {ε_j χ_j⁰ : j ≠ j₀}` (3 元) に対する `D_𝓑` は**直接書き下せる**:
  `i ≠ j₀` の行 = `ε_i` を第 `i` 成分に、それ以外 0;
  `i = j₀` の行 = 全成分 `−ε_{j₀}`。
Navarro の正規化 (`ε_{j₀} = −1`) で `D = [[1,0,0],[0,1,0],[0,0,ε₂],[1,1,1]]`、
`C_𝓑 = D_𝓑ᵗD_𝓑 = 1 + δ` (対角 2、非対角 1) も直ちに出る。
- [x] **段 203 完了**: その `j₀` (= `χ(t) = −1` なる添字) の存在。

⚠ しかし **(7.5)(c) を `C_𝓑` に繋ぐには `U` が要る** (`C_𝓑 = D_𝓑ᵗD_𝓑 = (D_B U)ᵗ(D_B U) = UᵗCU`)。
`U` の存在について:
 - **`K` 上の存在**: **段 204 で完了** (`Modular/BrauerFromOrdinary`) —
   `μ₀ = Σ_χ a_χ χ⁰` (`a_χ = Σ_τ d_{χτ}[τ,μ₀]⁰`) が既存の
   `sum_cartanMatrix_mul_pairingZero` (Navarro (2.13)) から 1 行で出る。
   「Cartan の逆 `([τ,μ]⁰)` もブロック対角」= **段 205 で完了**
   (`P'_{τμ} := if 同ブロック then P else 0` が `CᵀP' = 1` を満たす + `mul_eq_one_comm` で
   逆の一意性)。⟹ 段 204 の係数 `a_χ` は `χ ∉ Irr(B)` で消える (段 184 と合わせて)。
   **段 206 で block 局所形も完了** (`sum_ordinaryCombination_block_eq_irreducibleBrauerCharacter`:
   `μ₀ ∈ IBr(B)` は `{χ⁰ : χ∈Irr(B)}` の `K`-結合)。
   ⟹ **`U` の `K` 上の存在の前提は全て揃った**。

### ✅ (7.4) 完成 (段 207-209、2026-08-05)

`PrincipalBlockBasicSet.lean` (新 leaf) で (7.4) を閉じた。

- **段 207** (純代数): 単一の符号関係 `Σ_{i∈S} ε_i c_i = 0` (+ `ε_i² = 1`) だけから
  `signRelationRow ε j₀ i j = δ_{ij} ε_j − δ_{i j₀} ε_{j₀}` を定義し、
  `c_i = Σ_{j≠j₀} (D_𝓑)_{ij}(ε_j c_j)` / `Σ_i a_i (D_𝓑)_{ij} = a_j ε_j − a_{j₀} ε_{j₀}` /
  `C_𝓑 = D_𝓑ᵗD_𝓑 = 1 + δ` を示した。モジュラーの語彙を一切使わない。
  併せて (7.5) の `U` を **ℤ 値から K 値へ一般化** (使うのは双線型性だけ; 消費者ゼロで無コスト)。
- **段 208**: `principalBasicSet` (= `η_j`, 𝓑 の外では 0) と `principalBasicSetMatrix` (= `U`,
  `u_{μj} = a_{μj} ε_j − a_{μj₀} ε_{j₀}`) を定義し、`φ_μ = Σ_j u_{μj} η_j` (`μ ∈ IBr(B₀)`) を証明。
  `μ ∉ IBr(B₀)` では `u_{μj} = 0`。
- **段 209**: `D_𝓑 = D_B U` (両辺が `χ_i⁰` の 𝓑-座標 + 段 202 の独立性) と、
  **`UᵗCU = 1 + δ`** (`C = D_BᵗD_B` を展開して通常指標の添字でまとめると `D_B U` の Gram 行列)。

⟹ (7.5)(c) と噛み合う形が揃った (`sum_mul_basicDecompositionNumber_eq_cartanMatrix` の RHS が
これ)。full build green / AxiomsCheck OK (新規 7 件) / lint --strict clean。

### ⚠ 整数性は迂回できない — Brauer の指標判定 (Brauer induction) が prerequisite

原文 p.141-142 を読み直して確定した (以前の「段 178 型の別ルートが使える見込み」は**誤り**):

- p.141: 「the columns `D^t_i` are columns of integers since `t` is an involution」。
  対合であることは「代数的整数が有理整数になる」部分しか担わず、そもそも
  `d^t_{χψ_j} = Σ_μ d^t_{χμ} u_{μψ_j}` が代数的整数であるためには **`U` の整数性**が要る。
- p.142 の中核 (`2u_1 = D^y_0 + D^t_0 − D^t_1 − D^t_2` 等で整数列を作り、`(u_i,u_i) = 3` から
  「非零成分はちょうど 3 個で `{1,1,−1}`」を出す) は**整数性がないと完全に崩れる**。

`U` の整数性 = Navarro **(3.16)**。その証明は **(2.16)** (`φ ∈ IBr(G)` は `{χ⁰ : χ∈Irr(G)}` の
ℤ-結合) のブロック局所化にすぎず、ブロック局所化の部分は**段 205-206 で既に済んでいる**
(K 上でやったのと同じ議論が ℤ 上でも通る)。したがって残るのは **(2.16) 本体**で、
Navarro の証明は **(2.15)** (`θ ∈ ℤ[Irr(G)] ∪ ℤ[IBr(G)]` なら `θ̂`/`θ̃` は generalized character)
経由、(2.15) は **Brauer's characterization of characters** に依拠する。

- ⚠ **実測**: Brauer induction / 指標判定は **mathlib にも repo にも無い**
  (`Mathlib/RepresentationTheory/` に該当ファイル無し、repo grep もヒット無し)。
- 出典は Isaacs *Character Theory of Finite Groups* Thm 8.4 で、**スコープ 3 冊の外**
  (`Isaacs Ch.8` は *Finite Group Theory* の「置換群」で別物)。⟹ 共有インフラとして新規に建てる。
- ルート: Brauer induction (`1_G = Σ a_H Ind_H^G λ_H`, `H` elementary) → (2.15) → (2.16) →
  ((3.16) はブロック局所化を段 205-206 の型で反復)。
- 代替案 (`det C_{b̄₀} = 4` から `det V = ±1` を出す Cauchy–Binet ルート) も検討したが、
  `det C` の値自体がブロック論の別結果を要するので短くならない。

### (7.6) の進捗 (段 210-211、2026-08-05)

原文 p.137 の証明を 4 段に分けたうち **(i) と (ii) が完了**。

- **段 210** = (i) `x ↦ x̄` が `G⁰ → Ḡ⁰` の全単射 (`GroupTheory/PRegularQuotient`、新 leaf)。
  全射は任意の正規部分群で成立 (原像 `g` の `p`-部分の像は `p`-元かつ `ȳ` の冪 = `p`-正則 ⟹ 1)。
  単射だけが仮説を使う: `mem_of_isPRegular_of_isPGroup_quotient` (「`G/N` が `p`-群なら
  `p`-正則元は `N` に入る」) を `N = C_G(P)` に当てて `G⁰ ⊆ C_G(P)` を出し、
  `x⁻¹y ∈ P` が可換な 2 つの `p`-正則元の積 = `p`-正則 かつ `p`-元 ⟹ 1。
  `bijOn_mk_isPRegular` / `commute_of_isPRegular_of_le_center` (BS の `P ≤ Z(G)` の場合)。
- **段 211** = (ii) `k[G/N]` の分裂を `k[G]` の分裂から誘導 (`Modular/QuotientSplitting`、新 leaf)。
  ⚠ **(2.32) は repo に既にあった** (`Algebra/NormalPSubgroupTrivialAction`,
  `pi_single_eq_one_of_mem_normal_pSubgroup`: 正規 `p`-部分群は全単純 `kG`-加群に自明作用)。
  そこで `blockPiHom π : g ↦ π(single g 1)` が `N` を潰す ⟹ `G/N` を経由 ⟹ 群環の普遍性で
  `quotientPi : k[G/N] →ₐ ∏_j M_{n_j}(k)`。**添字集合 `ι` と行列サイズが `π` と同一**なのが
  原文の「`φ ↦ φ̄` が `IBr(G) → IBr(Ḡ)` の全単射」の形式化。
  `ker_quotientPi : ker π̄ = J(k[G/N])` は `ker π̄ = f(ker π)` + `ker f ≤ ker π = J(kG)` +
  `Ring.map_jacobson_of_ker_le`。

- **段 212** = (iii)(a) `IBr(G)` と `IBr(G/N)` の**値の一致** (`Modular/QuotientSplitting`)。
  `pRegularExponent_quotient` (`|G| = |G/N|·|N|` で `|N|` が `p` 冪 ⟹ `p'`-部分不変) で
  両者の Brauer 指標が同じ 1 の冪根で取られ、`blockRepresentation_quotientPi` で作用素が
  literally 同一なので `irreducibleBrauerCharacter_quotientPi : φ(g) = φ̄(ḡ)`。
- **段 213** = (iii)(b) pairing 恒等式 (`Modular/QuotientPairing`、新 leaf)。
  段 210 の全単射で `p`-正則和 `Σ a(g)b(g⁻¹)` は**そのまま**移り (`sum_pRegular_quotient`)、
  違うのは正規化因子だけ ⟹ `card_mul_pairingZero_quotient : |N|·[a,b]⁰_G = [ā,b̄]⁰_Ḡ`。

### ✅ (7.6) 完成 (段 214-215、2026-08-05)

- **段 214** = (iii)(c) **`C = |P| C̄`** (`Modular/QuotientCartan`、新 leaf)。
  純線型代数の補題 `eq_of_sum_mul_eq_ite` (「同じ行列を右逆に持つ 2 つの族は一致」を
  `sum_cartanMatrix_mul_pairingZero` が供給する添字形 `Σ_μ c_{μθ} P_{μφ} = δ` で述べ、
  転置して `Matrix.inv_eq_left_inv` の一意性に落とす) に、
  `card_mul_pairingZero_irreducibleBrauerCharacter_quotientPi`
  (段 212 の `φ(g)=φ̄(ḡ)` を段 213 の pairing 恒等式に食わせた `|N|·[φ,θ]⁰_G = [φ̄,θ̄]⁰_Ḡ`) を
  合わせる。ℕ 版は `CharZero K` (= `CharZero 𝒪` + `IsFractionRing` の単射) で K 版から戻す。
- **段 215** = 原文 p.138 の remark、**basic set 版 `C_𝓑 = |P| C_𝓑̄`**
  (`sum_sum_mul_cartanMatrix_quotientPi`)。IBr が同じ `ι` で値も一致 ⟹ 変換行列 `U` が共通に
  取れる ⟹ (7.5)(c) の congruent 行列 `UᵗCU` も `|N|` 倍。**BS 証明 p.141 が引くのはこの形**
  (`H = C_G(t)`, `N = ⟨t⟩` で「Cartan 不変量が 2 倍」)。

⚠ **(iv) のブロック全単射 `Bl(Ḡ) ≃ Bl(G)` は形式化しない**。原文 p.138 の証明は
Problem (3.4) (ブロックの Cartan 行列は分解不能) を使うが、**BS 証明が実際に要るのは
主ブロック同士の対応だけ**で、それは「自明指標を含む」ことから直接出る。上記 (iii)(c) と
段 215 が解析的な内容の全部。

### ✅ issue 9508 完了 (2026-08-06) — 上流前提はもう無い

[9508](closed/9508-brauer-characterization-of-characters.md) (Brauer's characterization of
characters → Navarro (2.15)/(2.16)/(3.16) → `U` の整数性) を **closed**。9506 に残っていた
**唯一の本質的な上流前提が消えた**。下流が使える形:

- `inducedVirtualCharacters_eq_virtualCharacters` = `v(G) = ch(G)`
- `mem_inducedVirtualCharacters_of_restrict` = Brauer の指標判定本体
- `exists_int_block_sum_eq_irreducibleBrauerCharacter_of_isAlgClosed` = **(3.16) 無条件版**
  (`[IsAlgClosed (ResidueField 𝒪)]` + `[IsAlgClosed K]` だけ; BS の具体系
  `PadicComplexSystem` は両方満たす)
- `intBasicSetMatrix` + `sum_decompositionMatrix_mul_intBasicSetMatrix`
  (`D_𝓑 = D_B U` over ℤ) + `sum_intBasicSetMatrix_mul_cartanMatrix` (`UᵗCU = 1 + δ` over ℤ)
  ⟹ **p.141-142 の「`D^t_j` は整数列」の土台**

### 段 216 (2026-08-06): **BS endgame を Sylow 非依存に抽出 — frontier が 1 点になった**

`brauerSuzuki_of_quaternionSylow` (|S|≥16) の証明を読み直したところ、**Sylow 2-部分群について
何も使っていなかった** — 使うのは `orderOf z = 2` と `z̄ ∈ Z(Ḡ)` (`Ḡ = G/O_{2'}(G)`) だけ。
⟹ `oPiCore_sup_centralizer_eq_top_of_mk_mem_center` として抽出 (`BrauerSuzukiEndgame.lean`)。

⟹ 新 leaf **`GroupTheory/BrauerSuzukiQ8.lean`**: Q₈ 分枝に残る数学が

> `q8_mk_mem_center` : Sylow-2 が `Q₈` なら `z̄ ∈ Z(G/O_{2'}(G))`

**の一点だけ**になった (= Navarro pp.139-146 の中身そのもの)。
`brauerSuzuki_quaternionSylow_q8` (RankOneAffineModel) はその適用に置換済で、
**sorry は移動しただけ (増減なし)**。以後 pp.139-146 の形式化はこの 1 文を埋める作業。

⚠ Navarro は `O_{2'}(G) = 1` の下で `t ∈ Z(G)` を示す。一般形にするには `Ḡ` へ移して
「`O_{2'}(Ḡ) = 1`」と「`Ḡ` の Sylow-2 も `Q₈`」(奇核は Sylow-2 と自明に交わる) が要る
— これも `q8_mk_mem_center` の証明の中で処理する。

### 段 217 (2026-08-06): **p.139 の reduction を全部証明 — frontier は指標論の 1 文**

`GroupTheory/BrauerSuzukiQ8.lean` に p.139 の第 1-2 段落を**帰納法込みで全部**入れた。
現在の鎖 (下から上へ、`sorry` は 1 箇所だけ):

| 名前 | 状態 |
|---|---|
| `q8_exists_proper_normal` | ⚠ **sorry** = Navarro pp.139-146 の指標論 |
| `q8_mem_center_of_oPiCore_eq_bot` | ✅ `Nat.card G` の帰納法で組立 |
| `q8_mk_mem_center` | ✅ `Ḡ = G/O_{2'}(G)` への移行 |
| `brauerSuzuki_q8` | ✅ endgame (|S|≥16 と共有) |
| `brauerSuzuki_quaternionSylow_q8` | ✅ 上の適用 (RankOneAffineModel) |

支持補題 (すべて証明済・AxiomsCheck 登録済):
- `sylowTwo_inf_oPiCore_eq_bot` / `oPiCore_subgroup_eq_bot` (奇核の遺伝)
- `quaternionTwo_sq_eq_one` (`Q₈` の対合は一意、`decide`) /
  `quaternionTwo_a_two_mem_center` (中心的、`decide`) /
  `isCyclic_of_card_dvd_four_of_unique_involution` (汎用) /
  `isCyclic_of_ne_top_of_quaternionTwo` (真部分群は巡回)
- `not_two_dvd_index_inf_subgroupOf` (`T ⊓ N` が `N` の Sylow-2) /
  `q8_mem_center_of_mem_normal_of_not_le` (巡回分枝) /
  `mem_sylow_of_mem_center_of_orderOf_eq_two` + `q8_mem_center_of_mem_center_normal` (`P ≤ N` 分枝)
- `not_hasNormalPComplement_of_oPiCore_eq_bot` / `not_controlsOwnFusion_of_oPiCore_eq_bot`
  (指標論パートの第 1 歩)

⚠ **設計上の省力点**: Navarro が `Z(N) = {1,t}` を経由する所は、`Z(N)` を部分群として構成せず
「`N` の中心的対合は `⟨u⟩` が正規 2-部分群ゆえ全 Sylow-2 に入る ⟹ `T ≅ Q₈` の唯一の対合に一致」
で直接落とした (mathlib `IsPGroup.le_sylow_of_normal`)。

### ⏸ 次 session の着手点 (2026-08-06 更新)

**`q8_exists_proper_normal` を埋める = BS 本証明 pp.139-146 の指標論**。
p.139 の残り = 「位数 4 の元は全て `G`-共役 (実は `C_G(t)`-共役)」。原文の論法:
`T` は fusion を制御しない (段 217 で証明済) ⟹ 位数 4 の 2 つの `T`-類が `G` で融合 ⟹
`y^g = z` なる `g`; `⟨y⟩^g = ⟨z⟩` で `N_G(⟨y⟩)^g = N_G(⟨z⟩)`、`Q₈` の部分群は全部正規ゆえ
`T, T^g ∈ Syl_2(N_G(⟨z⟩))` ⟹ Sylow 共役で `g` を `N_G(T)` に取り直せる ⟹
`Aut(Q₈) = Sym(4)` から `N_G(T)/C_G(T) ≤ Sym(4)` で `gC_G(T)` の位数は 3
(2 冪だと `y, z` が `T`-共役になって矛盾) ⟹ `z^g = (yz)^{±1}`。
`Z(T) = {1,t} ⊴ N_G(T)` ゆえ `g ∈ C_G(t)`。

⚠ **`Aut(Q₈) ≅ Sym(4)` は構成しなくてよい (2026-08-06 に設計確定)**。原文がそれを使うのは
「`gC_G(T)` の位数が 2 冪でない ⟹ 3」の一点だが、同じ結論は index の偶奇だけで出る:
`N_G(T)` の「位数 4 の巡回部分群 3 つ」への作用は `T·C_G(T)` を核に含む
(Q₈ の部分群は全部正規 = `zpowers_normal_of_quaternionTwo`、`C_G(T)` は自明作用) ので
**奇位数の商** (`not_two_dvd_relIndex_sup_centralizer`) を経由し、`Sym(3)` の奇位数部分群は
自明か推移的 ⟹ 1 つ融合すれば 3 つとも融合する。段 218 で材料を証明済。

**段 218-219 で証明済の材料** (`BrauerSuzukiQ8.lean`、全て AxiomsCheck 登録済):
- `quaternionTwo_conj_eq_self_or_inv` (decide) → `zpowers_normal_of_quaternionTwo`
  (= 原文「every subgroup of `P` is normal in `P`」)
- `quaternionTwo_exists_conj_eq_inv` (decide) → `conj_eq_iff_of_quaternionTwo`
  (= 位数 4 の元の `T`-共役類はちょうど `{w, w⁻¹}` の 2 元 = **ブロック構造**)
- `not_two_dvd_relIndex_sup_centralizer` (= `[N_G(T) : T·C_G(T)]` は奇数)
- `orbit_eq_univ_of_odd_of_card_eq_three` (= 奇位数群の 3 元集合への作用は固定か推移)

- `sylowQ8_le_normalizer_zpowers` (= `T ≤ N_G(⟨w⟩)`、原文「every subgroup of `P` is normal」)
- `exists_mem_normalizer_conj_mem_zpowers` (= **融合元 `g` を `N_G(T)` に取り直せる**;
  `T, T^g ∈ Syl_2(N_G(⟨z⟩))` + Sylow 共役)
- `quaternionTwo_card_inversePairs` (= `Q₈` の位数 4 巡回部分群はちょうど 3 個)

⚠ **`Ω` の表し方 (2026-08-06 に確定)**: 「部分群の集合」ではなく
**「対 `{w, w⁻¹}` の `Finset` を集めた `Finset`」**で表すと `decide` で濃度 3 が出る
(部分群の集合は decidable に列挙できない)。

- `exists_smul_eq_of_mem_inversePairs` (2026-08-06 完成) = **`Aut(Q₈) = Sym(4)` 段の代替**:
  `N_G(T)` は 3 つの inverse pair に共役で作用し、`T` が各対の安定化群に入り
  `[N_G(T):T]` が奇なので軌道は奇位数 ⟹ 1 か 3 ⟹ **1 つでも動けば推移的**。

⚠ **綴りの罠 2 つ (解決済、再発注意)**:
(a) `Subgroup.normalizer` は **`Set` 引数**なので、ソート位置では
`↥(Subgroup.normalizer ((T : Subgroup G) : Set G))` と coercion を明示する
(型注釈も dot notation も効かない)。
(b) `Finset` への誘導作用 (`Finset.mulActionFinset`) は
`Mathlib.Algebra.Group.Action.Pointwise.Finset` の **scoped instance** なので、
その import と `open scoped Pointwise` の両方が要る (`SMul` だけは別ファイルにあるので
`MulAction` だけ落ちる、という紛らわしい失敗をする)。

**残る組み立て** (次 session の着手点、論法は 2026-08-06 に確定済):

`¬ T.ControlsOwnFusion` (段 217) をほどくと `x, y ∈ T` で `G`-共役だが `T`-共役でないものが取れる
(`Subgroup.ControlsFusionIn` の定義 = `Ch05_Transfer/Basic.lean:872`)。そこから:

1. **`x² ≠ 1` が従う** — `x = 1` なら `y = 1` で `u = 1` が効く; `x` が対合なら `Q₈` の対合の
   一意性 (`eq_of_sq_eq_one_of_quaternionTwo`) で `y = x` となりやはり `u = 1`。⟹ 位数 4。
2. **`{y, y⁻¹} ≠ {x, x⁻¹}`** — `T`-共役類がちょうど `{x, x⁻¹}` (`conj_eq_iff_of_quaternionTwo`)
   なので、`y` がそこに入れば `T`-共役になってしまう。
3. **動く `u`** — `exists_mem_normalizer_conj_mem_zpowers` で `u ∈ N_G(T)`、`u x u⁻¹ ∈ ⟨y⟩`。
   `u x u⁻¹` は位数 4 で `⟨y⟩` は位数 4 の巡回群なので `u x u⁻¹ ∈ {y, y⁻¹}` ⟹
   `u • {x,x⁻¹} = {y,y⁻¹} ≠ {x,x⁻¹}`。
   ⚠ **`⟨y⟩` の位数 4 の元は `y, y⁻¹` だけ**の部分は `quaternionTwo_eq_or_eq_inv_of_mem_powers`
   (`decide`、冪を `1, y, y², y³` と列挙した形) が済んでいる。残るのは
   `x ∈ Subgroup.zpowers y` からこの列挙形へ落とす橋渡しだけで、
   `mem_powers_iff_mem_zpowers` (有限群) + `pow_mod_orderOf` + `orderOf y = 4` で出る
   (⚠ `zpow` のまま `%` を扱おうとすると煩雑になる — **ℕ 冪に移してから** `% 4` する)。
4. **`exists_smul_eq_of_mem_inversePairs`** で全対が融合 ⟹
   **「位数 4 の元は全て `G`-共役」**(原文の "the claim has been proven")。

✅ **(1)-(4) は 2026-08-06 に完了** (`isConj_of_orderFour`)。⟹ p.139 は
`q8_exists_proper_normal` の sorry を除いて**全部形式化済**。

**次の段 = p.140 以降** (2026-08-06 実測: 部品はすべて `Modular/PrincipalBlock*` に在る):

| 原文 | 供給する既存定理 | 場所 |
|---|---|---|
| (7.2) `|Irr(B₀)| = 4`, `χ(t) = ±1` | `card_blockOfIrr_principal_eq_four_and_character_involution` | `PrincipalBlockInvolution:320` |
| 弱ブロック直交 `Σ χ(1)χ(t) = 0` | `sum_character_mul_character_involution_eq_zero` | 同 `:492` |
| `ε_j² = 1` | `character_involution_mul_self` | `PrincipalBlockBasicSet:245` |
| (7.4) basic set + `UᵗCU = 1+δ` | `sum_basicSetMatrixOf_mul_cartanMatrix` ほか 4 定理 | 同 |
| `U` の整数性 | `intBasicSetMatrix` / `sum_intBasicSetMatrix_mul_cartanMatrix` | `IntegralBasicSetMatrix` (issue 9508) |

⚠ **(7.2) の機械は `t` を「唯一の対合類の代表」として受け取る形** (`hconjall` と
`hcart : cartanMatrix … = 4` が仮説)。"Analysis at y" は同じ機械を**位数 4 の元 `y`** で回すので、
`hconjall` に相当する仮説を `isConj_of_orderFour` (2026-08-06 完成) が供給する
— ここが p.139 の成果と p.140 の接続点。

⚠⚠ **ただし包装済の `card_blockOfIrr_principal_eq_four_and_character_involution` は
そのままでは `y` に使えない (2026-08-06 実測)**: section 変数 `ht : t * t = 1` を
`include` しているので**対合専用**。中身の部品のうち平方和だけが `t*t=1` を使っていて、
それは既に一般化されている:
**`sum_sq_character_eq_cartanMatrix_of_isConj_inv (hinv : ∃ c, c * t * c⁻¹ = t⁻¹)`**
(`PrincipalBlockInvolution:206`、段 197-198)。`Q₈` の位数 4 の元は `T` 内で反転されるので
(`exists_conj_eq_inv_of_quaternionTwo`) この仮説は満たせる。
⟹ **次の実装単位** = `card_blockOfIrr_principal_eq_four_and_character_involution` の
`y`-版を、`ht` を `hinv` に差し替えて組み直すこと。**証明本体で `ht` を使うのは 2 箇所だけ**
(2026-08-06 に proof を読んで確定):

| `t`-版 (対合) | `y`-版 (位数 4) で使う置換先 |
|---|---|
| `exists_intCast_character_of_mul_self_eq_one σ h2 ht` (`χ(t) ∈ ℤ`) | **`exists_intCast_character_of_pow_four_eq_one σ h2 (hy : y^4 = 1) (hreal : σ.character y⁻¹ = σ.character y)`** (`RepresentationTheory/CharacterOrderFour:162`、段 199) |
| `sum_sq_character_involution_eq_cartanMatrix … ht` (平方和 = 4) | **`sum_sq_character_eq_cartanMatrix_of_isConj_inv (hinv : ∃ c, c * t * c⁻¹ = t⁻¹)`** (`PrincipalBlockInvolution:206`、段 197-198) |

`hreal` (`χ(y⁻¹) = χ(y)`) と `hinv` はどちらも「`y` が `y⁻¹` と共役」から出て、それは
`Q₈` の Hamiltonian 性 (`exists_conj_eq_inv_of_quaternionTwo`、2026-08-06) が供給する。
`hy : y^4 = 1` は `quaternionTwo_pow_four` から。
残り (`hane` 以降の非零性・`Nontrivial`・`SumSquaresFour`) は `t` に依らない。

⚠ 当該ファイルは仮説鎖が長く `maxHeartbeats 1000000` 級なので、
`include` 行の差し替えを 1 つずつ leaf build で回すこと (段 I の refactor と同じ要領)。

**実装方針 = その場で一般化 (複製しない)**。呼び出し側は **2 箇所だけ** (実測):
`PrincipalBlockInvolution:632` と `PrincipalBlockBasicSet:252`。
`ht : t * t = 1` を `(hy4 : t ^ 4 = 1) (hinv : ∃ c, c * t * c⁻¹ = t⁻¹)` に差し替え、
`include` から `ht` を外す。対合での instance 化は
`hy4 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, sq, ht, one_pow]`、
`hinv := ⟨1, by simpa using (inv_eq_of_mul_eq_one_right ht).symm⟩`。
⚠ `exists_intCast_character_of_pow_four_eq_one` が要求する `hreal : χ(t⁻¹) = χ(t)` は
`hinv` + 指標の類関数性から出る (`χ(c t c⁻¹) = χ(t)`) — **この橋渡し補題の所在を
先に grep すること** (`Representation.character` の共役不変性)。


- "Analysis at y" (p.139 末-140): `⟨y⟩` が `C_G(y)` の Sylow-2 ⟹ 正規 2-補群 ⟹
  `IBr(b₀) = {1}` ⟹ `χ_i(y) = d^y_{χ_i 1}` … 部品は段 185-200 で既出。
  **2026-08-06 実測の所在**: 正規 2-補群は
  `GroupTheory/CentralSylowComplement.hasNormalPComplement_of_sylow_le_center` (段 200;
  `y` は自分の中心化群で中心的なので仮説が自動)、Cartan 値は
  `Modular/PrincipalBlockCartan.card_mul_sum_sq_principalBlock` (`:157`)。
  「四元数群は位数 4 の中心元を持たない」は **段 278 で完了**
  (`sq_eq_one_of_mem_center_of_quaternionTwo`)。

  ✅ **「`⟨y⟩` が `C_G(y)` の Sylow-2」= 段 281 で完了**
  (`sylow_centralizer_eq_zpowers`、`BrauerSuzukiQ8.lean`)。証明は予定どおり:
  `y` は `C_G(y)` の中心 ⟹ `⟨y⟩` は正規 2-部分群 ⟹ `IsPGroup.le_sylow_of_normal` で
  `⟨y⟩ ≤ S` ゆえ `4 ∣ |S|`; `S` の `G` への像は 2-部分群ゆえ `|S| ∣ |Q| = 8`;
  `|S| = 8` なら濃度一致で像 `= Q` で `Q ≅ Q₈` (段 279) だが `Q ⊆ C_G(y)` の元は
  `y` と可換ゆえ `y ∈ Z(Q)` で段 278 に矛盾 ⟹ `|S| = 4 = |⟨y⟩|`。
  ⚠ 「位数 8 の 2-部分群は Sylow」という補題は**要らなかった** —
  `IsPGroup.exists_le_sylow` で包む Sylow `Q` を取り、濃度一致で `= Q` を出す方が短い。
  正規 2-補群への接続も同段で完了 (`hasNormalPComplement_centralizer_orderFour`)。

  ✅ **`hcart` の供給ルート = 段 282 で完了**
  (`cartanMatrix_principalBlock_eq_card_sylow`、`Modular/PrincipalBlockCartanEntry.lean`)。
  ⚠ **上の「所在」記述は不正確だった**: `card_mul_sum_sq_principalBlock` は degree 版で、
  Cartan 版 `card_mul_cartanMatrix_principalBlock` (`|N| · c_{φ₀φ₀} = |G|`、`K` の中の等式)
  が既に `PrincipalBlockCartanEntry.lean` に在った (ただし **consumer ゼロ**)。
  足りなかったのは「`K` は標数 0 ゆえ ℕ で読み直し、`|N| · [G:N] = |G|` と約して
  `c = [G:N] = |S|`」の一段だけ。支持補題
  `index_eq_card_sylow_of_isPGroup_quotient` (`GroupTheory/ThreeStepGroup.lean`) も新設
  (`S ⊔ N = ⊤` + `S ⊓ N = ⊥` ⟹ `|G| = |S|·|N|`)。

  ⚠⚠ **「(7.2) の機械を `y` でそのまま回す」は誤りだった (段 283 で p.140 を画像実読して訂正)**。
  (7.2) の `hconjall` (全ての `p`-元が `t` に共役) は **`y` には成り立たない** — 位数 4 の元は
  2 つある `2`-元の類の片方でしかないので、「どの `χ(y)` も 0 でない」が言えず
  `|Irr(B₀)| = 4` は出ない。原文が実際に書いているのは
  「the nonzero entries of the integer column `χ(y)` are necessarily **four ±1**」で、
  `±2` の排除には `hconjall` でなく**列の先頭成分が 1 (自明指標)** を使う。

  ✅ **"Analysis at y" の指標側 = 段 283-285 で完了**:
  - 段 283 `card_character_ne_zero_eq_four_of_isConj_inv` (`PrincipalBlockInvolution`) =
    `∑_{Irr(B₀)} χ(y)² = 4` (段 197-198 + `hcart`) + `χ(y) ∈ ℤ` (段 199) を
    **0 を許す算術版** (`Algebra/SumSquaresFour` に新設:
    `eq_zero_or_one_or_neg_one_of_sum_sq_eq_four` /
    `card_filter_ne_zero_eq_four_of_sum_sq_eq_four`) に噛ませる。
  - 段 284 `exists_trivial_wedderburn_index` (`PrincipalBlockNonvanishing`) =
    自明表現は任意の Wedderburn 分解に 1×1 ブロックとして現れる
    (`Ĝ` の非零成分の列が不変ベクトル ⟹ 既存 `forall_apply_eq_of_invariants_ne_bot`)。
  - 段 285 `blockOfIrr_eq_principalBlock_of_trivial` (新 leaf
    `Modular/PrincipalBlockTrivial.lean`) = その成分のブロックは `B₀`
    (中心指標を類和基底 `centerBasis` 上で比較: `ω(K̂) = |K|` → 格子側も `|K| ∈ 𝒪` →
    剰余 `|K|*` = `aug(K̂)`)。⟹ 段 283 の signature から `{j₁}` 系の仮説が消えた。

✅ **`BrauerSuzukiQ8.lean` の prefix-split = 段 280 で完了**:
`Q₈` 固有の事実 24 宣言を `GroupTheory/QuaternionTwoFacts.lean` (388 行) へ分離、
本体は 811 行に (段 281 追加後 933 行)。`OddOrder.lean` 配線済。

⟹ **次の実装単位 = p.141 "Analysis at t" の群論的入力** (2026-08-06 に p.141 を画像実読):
  1. `T` (≅ `Q₈`) は `C_G(t)` の Sylow-2 (`t ∈ Z(T)` ゆえ `T ≤ C_G(t)`、`[G:T]` 奇)
  2. ⟹ `C_G(t)/⟨t⟩` の Sylow-2 は `Q₈/Z(Q₈) ≅ Z₂ × Z₂` (Klein four)
  3. `C_G(t)/⟨t⟩` の対合は全て共役 (`T` の位数 4 の元が `C_G(t)`-共役だから;
     対合は Sylow へ共役で送れる + `T̄` の 3 つの対合は位数 4 の元の像)
  ✅ **1-3 は段 286-288 で完了** (`sylowQ8_le_centralizer_involution` /
  `card_quotient_zpowers_of_quaternionTwo` + `sq_eq_one_quotient_zpowers_of_quaternionTwo` /
  `isConj_of_sq_eq_one_quotient_centralizer`)。3 の途中で
  **`isConj_of_orderFour` の結論を `∃ g ∈ N_G(T)` に強化**し (証明中の融合元は元々
  `N_G(T)` の中で作られていた)、`isConj_centralizer_of_orderFour` を得た (段 287)。
  汎用配管 `exists_conj_mem_sylow` (p-元は指定 Sylow に共役で入る) も新設 —
  ⚠ 着手後に対合専用の特殊化 `exists_conj_mem_sylow_of_mul_self_eq_one` が
  `KleinFourSylowFusion` に既存と判明したので、その場で一般化して特殊版を置換した。

  ✅ **`τ(t) ≡ τ(y) mod 2` = 段 289 で完了、しかも `Q₈` の指標表は不要だった**。
  原文は「from the character table of `P`」と読むが、`t` も `y` も `2`-元なので
  どちらの値も次数と `mod 2` で合同 (Gorenstein Lemma 7.5 = 既存
  `intModEq_of_mem_adjoinSpan`) ⟹ 互いに合同。
  新設 = `pRegularPart_eq_one_of_isPElement` / `intModEq_one_of_isPElement` /
  `intModEq_of_isPElement_of_isPElement`。

  ⟹ **残り** = Cor (7.4) (段 207-209) を `C_G(t)/⟨t⟩` に適用して basic set
  `{1=ψ₀,ψ₁,ψ₂}` と Cartan `c_ij = 1 + δ_ij` を得る → (7.6) (段 214-215) で
  `C_G(t)` へ持ち上げ (Cartan は 2 倍) → (7.5.a) で
  `χ_i(tu) = ∑_j d^t_{χ_i ψ_j} ψ_j(u)` → (7.5.b,c,d) で
  (3) `(D^t_i, D^t_j) = 2(1+δ_ij)` / (4) `(D^y_0, D^t_j) = 0` / (5) `(χ(1), D^t_j) = 0`。
  ⚠ ここから先は「`C_G(t)/⟨t⟩` の modular datum を組む」段になるので、
  着手前に (7.4)/(7.6) の実際の signature を実測すること。

### 🎯 未供給仮説の棚卸し (段 290-293、2026-08-06)

BS の鎖が長らく**仮説として持ち回っていた**もののうち、supplier がゼロだった 3 件を閉じた。
(7.6) は `quotientPi` で商側の datum を**元の datum から導出**する設計なので、
`C_G(t)/⟨t⟩` 用に別の datum を組む必要は無い — 要るのは `C_G(t)` の datum だけ。

| 仮説 | 供給源 | 段 |
|---|---|---|
| `hcart : cartanMatrix … = 4` | Klein four Sylow + 中心的対合 ⟹ 正規 2-補群 ⟹ `c = \|Sylow\|` | 290-291 |
| `hζ`/`hζk`/`hζK` | `exists_pow_eq_one_residue_eq_one_padicComplexInt` (ℂ_[p] の原始 p 乗根) | 292 |
| `hlin`/`hnil` | `exists_splitting_datum` (旧 `exists_surjective_blocks_card_eq` は両方落としていた) | 293 |

⟹ **残るは `hconv` と、datum 一式を実際に `obtain` して組む assembly**。
`hp`/`hx`/`hω`/`hω'`/`e`/`eG`/`Invertible` は既に supplier がある
(`exists_isPrimitiveRoot_padicComplexInt` / `exists_algEquiv_pi_matrix_padicComplex` / 標数 0)。

### `hconv` は gap ではなく assembly (2026-08-06 実測)

`hconv` (= Brauer 第 3 主定理の逆向き) の**本体は既に在る**:
`SecondMainPrincipalBlock.eq_principalBlock_of_inducedBlockOfCentralizer_eq`
(Külshammer route の `eq_principalBlock_of_inducedBlockOfNormalizer_eq_intermediate` を
`Q = ⟨x⟩` / `H = C_G(x)` に特殊化したもの)。⟹ **新しい数学は要らない**。

ただし `∀ b, … → b = principalBlock` の形 (= `hconv` そのもの) にするには 3 つ供給が要る:
1. `hB` / `hBH` — ブロック冪等元の族 `F'` with `blockCharacterPi (F' B) = Pi.single B 1`。
   `MatrixModule.exists_completeOrthogonalIdempotents_block` (`Algebra/BlockIdempotent:183`)
   が出す。**ほぼ機械的**。
2. `hcoeff` — `e_{B₀}^G(g) = e_{b₀}^{C_G(x)}(g)`。本体は
   `KulshammerThirdMain.coeff_principalBlock_eq_centralizer_intermediate` だが、
   ⚠ **こちらが仮説を大量に持つ** (`hidemH`/`hfH`/`hBH`/`hweakH`/`hvanishH` +
   両側の Sylow + 𝒪 側への持ち上げ)。⟹ **ここが本当の assembly コスト**。
3. `C_G(⟨x⟩)` と `centralizerOf x` の項の同一視 (同じ部分群だが syntactic に別)。

#### 供給源の実測 (2026-08-06) — **4 つとも既に在る。残りは純粋な配管**

| 仮説 | supplier | 状態 |
|---|---|---|
| `hidemH` / `hfH` | `BlockIdempotentLift.exists_isIdempotentElem_blockCharacterPi_eq_single` | 証明済 |
| `hBH` | `MatrixModule.exists_completeOrthogonalIdempotents_block` | 証明済 |
| `hweakH` | **Navarro (5.11)** `BlockPartVanishing.sum_character_blockOfIrr_eq_zero` | 証明済 |
| `hvanishH` | `PRegularSumVanishing.blockCharacter_blockOfIrr_pRegularSum_eq_zero` | ⚠ **形が違う** |

⚠ **循環は無い**: (5.11) の仮説は「`G` と `C_G(g_p)` の modular datum + 原始根 + `ζ` 三点」だけで、
`hconv` を要求しない。`ζ` 三点は段 292、datum は段 293 で supplier が揃ったので、
(5.11) は無条件に使える。

⚠⚠ **上の表の `hvanishH` は訂正 (2026-08-06、実読)**。
`blockCharacter_blockOfIrr_pRegularSum_eq_zero` は
(a) ブロックが `blockOfIrr e … i` の形であること、(b) 追加の分離仮説 `hne`
(`i` の分解行列の台と `σ` の分解数の台で中心指標が異なる) を要求する。
`hvanishH` が要るのは**任意の `B ≠ B₀`** についてなので、そのままでは使えない。
⟹ 埋めるべきもの: (a) **`blockOfIrr` の全射性** (「どのブロックもある `χ` のブロック」;
repo に補題が見当たらない) と (b) `hne` の discharge。**ここだけは新しい補題が要る**。

✅ **段 294 完了**: `hidemH`/`hf`/`hBH` の束
`BlockIdempotentLift.exists_blockIdempotentFamily` を新設 (1 ブロック版から `choose`;
`hf` は `centerReduce` の定義から `rfl`)。

✅ **段 295 完了**: `blockOfIrr` の全射性 `CentralScalarBridge.exists_blockOfIrr_eq`
(+ 支持補題 `mapRingHom_injective`)。

#### `hvanishH` を任意の `B` に降ろす残り (2026-08-06 に段取り確定)

`blockCharacter_blockOfIrr_pRegularSum_eq_zero` を `B ≠ B₀` で使うには、段 295 で `i` を取った後
その追加仮説 `hne` を潰す必要がある。`hne` の中身は実は「`B ≠ B₀`」そのもの:

- `decompositionMatrix e i φ ≠ 0` ⟹ `blockOfIrr e … i = Quotient.mk (blockSetoid) φ`
  (`DecompositionBlockDiagonal.blockOfIrr_eq_of_decompositionMatrix_ne_zero`, 証明済)
- `decompositionNumber σ μ ≠ 0` ⟹ `centralCharacterAlg π μ` は `σ` のブロック
  (`DecompositionNumber.centralCharacterAlg_eq_of_decompositionNumber_ne_zero`, 証明済)
- `centralCharacterAlg π φ ≠ centralCharacterAlg π μ` ⟺ `Quotient.mk φ ≠ Quotient.mk μ`
  (`blockSetoid` の定義)

⟹ **残る 1 点 = 「自明な `𝒪`-格子表現 `σ` (trace ≡ 1) のブロックは主ブロック」**。
これは段 285 (`blockOfIrr_eq_principalBlock_of_trivial`) の **`𝒪`-格子側の対応物**で、
証明も同じ (中心指標を類和基底上で比較)。これが出れば `hvanishH` → `hcoeff` → `hconv` が
最後まで通る。

- "Analysis at t" (p.141-142): `C_G(t)/⟨t⟩` が Klein four Sylow-2 ⟹ (7.4) の basic set、
  (7.6) で `C_G(t)` へ持ち上げ、(7.5) で `d^t` の列。**整数性は issue 9508 で完済**
  (`intBasicSetMatrix` / `sum_intBasicSetMatrix_mul_cartanMatrix`)。
- `Z(T) = {1,t} ⊴ N_G(T)` から `u ∈ C_G(t)` (原文 p.139 末の注意) は必要になった時点で足す。

必要な群論的事実 (原文 p.138 が列挙):
~~`Aut(Q₈) = Sym(4)`~~ (上記で不要) / 巡回 Sylow 2 なら正規 2-補群 /
対合 2 つが生成する群は二面体 /
`P` が `G`-fusion を制御 ⟺ 正規 p-補群 (✅ 段 217 で使用済) / `Q₈` の指標表 (p.138 に掲載)。
さらに p.141 末: `τ(t) ≡ τ(y) mod 2` (`Q₈` の指標表から)。
⚠ 着手前に repo 実測で再確認する (上の (B) 節の実測は 2026-08-05 時点)。

⚠ 上記の番号は Navarro の結果番号であって段番号ではない (段番号は連番で振り直す)。
⚠ 数式は OCR 崩れが重いので、各段の statement は `references/navarro/pages/*.png` で確定する
(BS 証明の pp.139–146 は取得済)。

## 完了条件

上記チェックボックスが全て埋まり、**具体構成による instance が存在**し、
build green + AxiomsCheck 登録 + sorry 非退行。

## 参照

- 親: [0147](0147-q8-modular-char-theory-frozen.md)
- spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
- 前提調査: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`
