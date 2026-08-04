# mathlib v4.32.0-rc1 → v4.32.2 移行記録

2026-08-04 実施 (branch `mathlib-v4322`)。`lake build OddOrder` フル green (5m47s 初回 / 5168 jobs)、
`bin/check-warnings --strict` OK、AxiomsCheck OK、sorry 1 = 1 (非退行)。被弾 18 files。

## pin

| | 旧 | 新 |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.32.0-rc1` | `leanprover/lean4:v4.32.2` |
| mathlib `rev` | `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` | `905b95818eb32af7874a58b427f50c1711a5e96c` (tag `v4.32.2` = `stable`) |

drift = 600 commits。ただし内容差は `v4.32.0-rc1 → v4.32.0` の **598 commits** に集中し、
`v4.32.0 → v4.32.1 → v4.32.2` は toolchain bump 2 commit のみ (mathlib のコード変更ゼロ)。

**v4.33.0-rc2 に直行しなかった理由**: 実測で v4.33 は commit 数が 6 割なのに repo の import 面
379 module 中 **239 (63%)** を触り (v4.32 系は 114 = 30%)、deprecated alias を 788 件削除する。
v4.33.0-rc2 は 2026-08-03 リリースの新しい rc なので、重い方を動いている的に当てない判断。
2 段階でも実測で二重 churn ゼロ (v4.32 で改名され v4.33 で再度動く名前 = 0 件) ゆえ加算で損しない。

## 最大の破壊的変更 — `MonoidAlgebra` の structure 化

`MonoidAlgebra R M` が `def := M →₀ R` から **`structure`** (フィールド `coeff : M →₀ R`、
コンストラクタ `ofCoeff`) になった。影響:

- 係数アクセス `x g` → **`x.coeff g`** (`Function expected at x but this term has type k[G]`)
- `Finsupp.ext` → `MonoidAlgebra.ext` / `ext` タクティク (2 段: `MonoidAlgebra.ext` + `Finsupp.ext`)
- `x.support` → `x.coeff.support` (`MonoidAlgebra.support` は存在しない)
- `Finsupp.filter/mapDomain/applyAddHom` を直接適用していた箇所は `.coeff` / `.ofCoeff` で包む
- `inferInstanceAs (Module.Finite ℤ (G →₀ ℤ))` が defeq でなくなる →
  `Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ..).symm` で移送
- `*_apply` 系が **`coeff_*`** へ一括改名 (`smul_apply` → `coeff_smul_apply` 等、
  deprecated alias 75 件の対応表あり)

## その他の API 変更

- `card_rootsOfUnity` / `HasEnoughRootsOfUnity.of_card_le`: `Fintype.card` → **`Nat.card`**
- `MonoidAlgebra.algHom_ext`: `A[M] →ₐ[R] B` へ一般化され**仮説が 2 本**に
  (係数側は `R = A` なら `Subsingleton.elim _ _`)
- `MulAction.selfEquivOrbitsQuotientProd` / `orbitEquivQuotientStabilizer`: 変数名 `α`/`β` → `G`/`X`
- `Pi.algHom R A g` → `AlgHom.pi g` / `AlgEquiv.coe_algHom` → `AlgEquiv.coe_toAlgHom`

## 同時に入れたリファクタ

1. **[`OddOrder/Mathlib/MonoidAlgebra.lean`](../../OddOrder/Mathlib/MonoidAlgebra.lean) 新設** —
   mathlib に無い穴 3 本。structure 化で `Finsupp` 版を流用できなくなった分。
   - `MonoidAlgebra.coeff_finsetSum` — `(∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m`
     (mathlib は `coeff_sum` (Finsupp の等式) と `Finsupp.finsetSum_apply` を別々に持つだけで
     合成版が無い。repo 内で同じ 2 行イディオムが 8 箇所以上繰り返されていた)
   - `MonoidAlgebra.mapDomain_surjective` — mathlib は `mapDomain_injective` しか持たない
   - `MonoidAlgebra.mapDomain_comp` — mathlib は束ねた準同型版のみ
2. **`_apply` → `coeff_*` 改名** — `_apply` サフィックスは「関数適用 `x n`」を指しており、
   migration 後は名前が実態と食い違う。`coeff_conj_smul` / `coeff_classSum` / `coeff_brauerProj` /
   `coeff_relTrace_single` / `coeff_center_conj` / `coeff_mul_sum` 等。新 mathlib 規約と一致。
3. **mathlib 変数名への結合を解消** — `selfEquivOrbitsQuotientProd (α := Γ)` は純粋なリネームで
   壊れた。`h` から推論させる形へ (名前非依存)。
4. **lint 純ゼロの維持** — `Pi.algHom` / `AlgEquiv.coe_algHom` の非推奨、unusedSimpArgs 3 件、
   `simpa`→`simp` 1 件、長すぎる行 7 件を解消。

## 後続で解消した重複 (2026-08-04、同日)

`ClassSumSections.classSum` (ℂ 版) と `CenterClassSumBasis.classSum` (一般体版) が
**定義も証明もほぼ同一の重複**だった。重複していたのは正確に 3 宣言
(`classSum` / `coeff_classSum` / `classSum_mem_center`) で、残りは各ファイル固有。

[`OddOrder/GroupTheory/RepresentationTheory/ClassSumCore.lean`](../../OddOrder/GroupTheory/RepresentationTheory/ClassSumCore.lean)
に 1 本化し、両ファイルが import する形にした。副産物:

- **一般化**: 中核は `Field k` を必要とせず `CommSemiring k` で足りる。類和が任意の可換係数
  半環上で使えるようになった (特殊化債務の解消)。
- **過剰 instance の露出と解消**: `CenterClassSumBasis` の
  `linter.unusedSectionVars` / `unusedFintypeInType` / `unusedDecidableInType` 抑制 3 本は
  「共有 `variable` ブロックの instance は全部 `classSum` が要る」ことを根拠にしていた。
  中核を外に出したら根拠が消え、抑制を外すと `DecidableEq G` が**全宣言で未使用**、
  `Fintype (ConjClasses G)` も大半で未使用だと判明。variable ブロックを段階導入に再構成して
  **抑制 3 本すべて除去**。`CenterOrbitCount` にも波及した 2 件は `omit` で対応。
- 差し引き **−71 行** (新 leaf の docstring を含む正味)。

⚠ 注意点: 中核が `k` について多相になったため、ℂ 固定を当てにしていた
`(classSum Ci * classSum Cj).coeff w` 形が `k` 不定になる (`CommSemiring ?m` が stuck)。
消費側 7 ファイルで `(… : ℂ[G]).coeff` の型注釈により固定した — ただし
`open scoped MonoidAlgebra` していないファイルでは `ℂ[G]` が配列添字と解釈されるので
`(… : MonoidAlgebra ℂ G).coeff` と綴る必要がある。

## 未着手 (別 issue 候補)

- `OddOrder.GroupAlgebra.classSum` (`OddOrder/Algebra/ClassSum.lean`) は**群の元**で添字づけた
  3 つ目の類和で、`classSum (ConjClasses.mk g)` と一致するはずだが添字型が違うため未統合。
  相対トレース機構と一体で発展しているので、統合するなら別途設計判断が要る。
