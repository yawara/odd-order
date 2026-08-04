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
- [ ] **97: 🎯 第二主定理 `(5.2)`** — `x` が `p`-元、`b ∈ Bl(C_G(x))`、`χ ∈ Irr(G)` が
      `Irr(b^G)` に属さないなら、全ての `φ ∈ IBr(b)` について `d^x_{χφ} = 0`。

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
  - [ ] **次: (5.5) の組み立て**。標数 `p` 側の corner 逆元 `ȳ` を `centerLift` で
        `Z(𝒪G)` へ持ち上げて `w` とし、`f_B - (f_B x) w` が核に入ることを
        `mem_centerIdeal_iff_centerReduce_eq_zero` で見て
        `exists_corner_inverse_of_approx` を当てる。部品は全て揃っており配線のみ。
        必要な instance = `Module.Finite 𝒪 Z(𝒪G)` (類和基底) と `Nontrivial Z(𝒪G)`。
  - [ ] その後 (5.6) → (5.7) → 🎯 (5.2)。
        併せて (3.13) `χ ∉ B ⟹ M f_B = 0` / (3.31) `ψ(f_b z)` も必要。
  - [ ] **(5.5)** / **(5.6)** / **(5.7)**。
        (5.7) は `⟨h⟩` の `supp(w)` への軌道が長さ `p` の倍数であること + 固有空間の
        次元比較 (乗算 `s` が単射) という組み合わせ論 + 線型代数。
  - [ ] 併せて必要: **(3.13)** `χ ∉ B ⟹ M f_B = 0` / **(3.31)** `ψ(f_b z) = ψ(z)`
        (`ψ ∈ Irr(b)`), `= 0` (otherwise)。どちらも `Irr(B)` の帰属を `𝒪G` の冪等元で
        言い換えるもので、(5.4) と同じ前提に乗る。
- [ ] **98: `(5.8)` + `(5.13.b,c,d)` (一般化分解数の直交関係) + block orthogonality**
- [ ] **99: 🎯 第三主定理 `(6.7)`** — Okuyama の証明 ((6.1)–(6.6) 経由、非常に一般な形)
- [ ] **100: `(6.10)` `ker(B) = O_{p'}(ker χ)` → `(6.12)` → 🎯 `(6.13)`**
      (normal `p`-complement ⟺ `IBr(B₀)` 単元、Cartan 行列 `(|G|_p)`)
- [ ] **101: `(7.2)` Klein four Sylow-2 / `(7.3)` basic set / `(7.4)` / `(7.5)` / `(7.6)`**
- [ ] **102: 🎯🎯🎯 BS 本証明 (pp.139–146)** → `brauerSuzuki_quaternionSylow_q8` の `sorry` 置換

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
