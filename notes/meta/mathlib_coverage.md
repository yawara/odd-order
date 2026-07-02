# mathlib カバレッジ (Feit-Thompson 形式化向け)

> **⚠ 2026-07-02 注記**: mathlib 欠落判定 (2026-05 snapshot) は有効だが、✗/△ 項目の大半は `OddOrder/**` に
> 実装済 (Frobenius 群 = Isaacs Ch06、J(P)/ZJ = `GroupTheory/ThompsonSubgroup`+Ch07、TI = `GroupTheory/TISubset`、
> Dade = Pf S04/S06、coherence = S07/S08 sorry-free 等)。**本 doc は mathlib coverage の記録であり残作業リストではない**。

mathlib (調査時 `v4.29.1`; **2026-05-27 に `v4.30.0-rc2` へ bump 済** — 本調査自体は v4.29.1 時点のスナップショット, ローカルパス `.lake/packages/mathlib/Mathlib/`) における Feit-Thompson 関連項目の網羅調査結果。**2026-05-21** 実施。mathlib は更新が速いので 3 ヶ月以上経ったら再監査推奨。

## ✓ 完全に揃っているもの (そのまま使える)

**群論基礎:** 部分群・正規化群・中心化群 (`Subgroup.normalizer/centralizer/center`)、剰余群、同型定理、群作用 (orbit/stabilizer)、`Subgroup.index`。

**有限群論:**
- Sylow の定理 (存在・共役・個数): `Mathlib/GroupTheory/Sylow.lean`
- `IsPGroup`: `Mathlib/GroupTheory/PGroup.lean`
- `IsSolvable`, `derivedSeries`: `Mathlib/GroupTheory/Solvable.lean`
- `IsNilpotent`, `upperCentralSeries`, `lowerCentralSeries`, `nilpotencyClass`: `Mathlib/GroupTheory/Nilpotent.lean`
- `frattini`, Frattini argument: `Mathlib/GroupTheory/Frattini.lean`
- Transfer map, Burnside normal p-complement: `Mathlib/GroupTheory/Transfer.lean` (`transfer`, `ker_transferSylow_isComplement'`)
- Focal subgroup theorem: `Mathlib/GroupTheory/Focal.lean`
- Schur-Zassenhaus: `Mathlib/GroupTheory/SchurZassenhaus.lean`
- Complement, semidirect product: `Mathlib/GroupTheory/Complement.lean`, `SemidirectProduct.lean`
- `IsPerfect`: `Mathlib/GroupTheory/IsPerfect.lean`

**表現論/指標理論:**
- `Representation`, `FDRep k G`: `Mathlib/RepresentationTheory/Basic.lean`, `FDRep.lean`
- `character`: `Mathlib/RepresentationTheory/Character.lean` (直交関係込み)
- `IsIrreducible`: `Mathlib/RepresentationTheory/Irreducible.lean`
- Maschke の定理: `Mathlib/RepresentationTheory/Maschke.lean`
- 誘導表現 (adjunction 形): `Mathlib/RepresentationTheory/Induced.lean`
- 半単純性, Schur の補題: `Mathlib/RepresentationTheory/Semisimple.lean`, `FDRep.lean`
- **群環の代数射** `Representation.asAlgebraHom : ℂ[G] →ₐ[ℂ] End ℂ V`, `Subalgebra.center ℂ ℂ[G]` (中心)

**本リポ実装済 (mathlib 不在分):**
- **class-sum 代数 / 中心指標** `ω : Z(ℂ[G]) →ₐ[ℂ] ℂ`: `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean` (`classSum`, `classSum_mem_center`, `classSumCoeff`, `classSum_mul_apply`, `centralCharacterOfRep`, `centralCharacterOfRep_classSum`). Isaacs §3 (p.35) / Peterfalvi (6.7.2) の `ClassSumAlgebraHom`。代数的整数性 (ω(C) が整数; (6.7.3) で使用) は未実装 (構造係数行列論法; 別 issue)。

## △ 部分的にあるもの (拡張/整備が必要)

- **Hall 部分群**: 一般 π-Hall の定理 (可解群版) は未実装。Sylow がコメントで Hall と呼ばれている程度。
- **Thompson subgroup J(P)**: 焦点定理は OK だが J(P) 自身の定義は無い。
- **Glauberman Z\***: 焦点定理止まり、Z\* explicit API なし。
- **互素作用 (coprime action)**: 基本だけ。Hall–Higman 系の補題群は未整備。
- **Frobenius 相互律**: adjunction 形では存在、古典形 explicit theorem は弱い。
- **類関数**: character 経由でしか扱えず、汎用 `ClassFunction` API は薄い。
- **群コホモロジー**: H¹ 基本と Shapiro の補題はあるが Feit-Thompson で要る範囲は要確認。
- **単純群**: `Subgroup.Simple.lean` に定義はあるが極小反例系の補題は無し。

## ✗ まったく無いもの (新規実装 = Phase 1 以降のロードマップ)

順序は Bender → Peterfalvi の依存関係に沿っておおむね下に行くほど後半:

1. **Fitting 部分群 `Fit(G)`** (最大冪零正規部分群)
2. **一般化 Fitting `F*(G)`**
3. **Frobenius 群** (kernel/complement の特性化、Frobenius の定理)
4. **CN 群, CA 群** (Suzuki の構造定理の準備)
5. **TI (trivially intersecting) 部分群/部分集合**
6. **仮想指標 (virtual character)、`ℤ[Irr G]` の環構造**
7. **Brauer 誘導定理**
8. **Artin 誘導定理**
9. **Brauer 指標 (modular character)、block theory、defect group**
10. **Dade isometry**
11. **Peterfalvi の coherence、例外指標 (exceptional characters)**
12. (周辺) 極小反例 (minimal counterexample) の構造補題群

優先順序は [ROADMAP.md](../../ROADMAP.md) Phase 1 (Isaacs Ch.1-10) でカバー。並行作業の単位として「Fitting」「Frobenius 群」など独立性が高い項目から着手するのが効率的。
