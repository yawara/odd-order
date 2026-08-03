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

- [ ] **`IBr(G)` の定義** (Navarro 2.x)。段 50 でブロック ↔ 既約加群が閉じたので、
      `IBr(G)` = ブロック `V_i` の Brauer 指標の族、として定義できる。
      ⚠ 配線の要: 本リポの `brauerCharacter` (段 27) は **`Representation k G V`** に対して
      定義されているのに対し、段 45-50 は **`Module (kG) M`** で書かれている。
      mathlib の `Representation.asModule` / `Representation.ofModule` で往復させる。
- [ ] **Brauer 指標の一次独立性** (Navarro 2.7)。単純加群の Brauer 指標が
      `p`-正則類上の類関数として独立。
- [ ] **分解行列 `D` の表現論的包装**: `G`-不変 `𝒪`-束の存在 (段 30 `exists_invariant_lattice`)
      → `χ|_{p-reg} = ∑_φ d_{χφ} φ`。加法性 (段 29) は済んでいるので組成因子への分解は取れる。

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
