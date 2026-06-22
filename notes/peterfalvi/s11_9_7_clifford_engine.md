# Pf §11 (9.7) Clifford decomposition engine — design (lane-c, 2026-06-22)

> Goal: prove `clifford_dichotomy` (Pf 9.7) `Nonempty (CliffordCaseAData chars) ∨ Nonempty
> (CliffordCaseBData chars)` by building the Clifford decomposition of the chief factor `H̄ = H/H₀`
> as an `F_p[U]`-module.  Deep, multi-session.  User-chosen (2026-06-22) over de-opacify-only /
> wait-for-hub.  正本 = this note.  Owner = lane-c (`S11_MaximalII_III_IV.lean`).

## 教科書 (9.7) 証明 (mmd 04.11 L53-69)

`H̄` は (9.6) で `UW₁`-既約 `F_p`-加群 (dim `q`、`|H̄|=p^q`)。`U` に制限し Clifford:
`H̄ = H₁ ⊕ ⋯ ⊕ H_k`、`H_i` は既約 `F_p[U]`-加群で `W₁` 共役。`q = dim H̄ = k·dim H₁`。`q` 素数ゆえ
**k=q (CaseA, dim H₁=1)** か **k=1 (CaseB, U 既約)**。

- **CaseA (k=q)**: `H_i` 位数 `p`、`a=|U:C_U(H₁)| ∣ p-1`、`U/C_U(H_i)` 巡回位数 `a`、
  `Ū ↪ (位数 a の巡回群)^{q-1}`。
- **CaseB (k=1)**: (8.5.b) で `U'` が `H` を中心化 ⟹ `Ū` abelian。`F=End_{F_p[U]}(H̄)` は体
  (Schur+有限可除環=体 Wedderburn)。`Ū≅U*⊆F*`、`H̄` は `F` 上 1 次元、`Ū` 巡回、`W₁` が `Ū` 上 FPF
  ⟹ `U*∩F_p=1` ⟹ `u` は `p-1` と互いに素・`(p^q-1)/(p-1)` を割る。

## 前提: ChiefFactorData の de-opacify (step 0、ungated)

`ChiefFactorData` の `quotient_elementaryAbelian` / `quotient_chiefFactor` /
`U_noncentral_on_quotient` は現状 **opaque `True`** (`exists_chiefFactorData` が捨てている)。engine は
`H̄` の**実**構造 (el-ab + 既約 + 非中心) を要する。`exists_chiefFactor_seed` (S11:1091) /
`exists_chiefFactor_kernel` (897) が**実証明を保持**しているので、それを field に通す:
- `quotient_elementaryAbelian` → `IsElementaryAbelian p (↥data.H ⧸ (H0.subgroupOf data.H))`
- `quotient_chiefFactor` → 既約性 (∀ A-inv 部分群 = ⊥ or ⊤、`coprimeFrobeniusChiefFactor_card` の `hirr` 形)
- `U_noncentral_on_quotient` → `C_H̄(U) ≠ ⊤` (action form)
chiefFactor_basic (済) は `_holds` / `quotient_order` 経由ゆえ互換 (field 値を返すだけ)。

## アーキテクチャ (steps)

0. **de-opacify ChiefFactorData** (上記)。実 H̄ 構造を露出。
1. **bridge**: `H̄ = Additive (↥data.H ⧸ H0')` を `ZMod p`-module 化 (`IsElementaryAbelian.zmodModule`,
   PRank.lean)、`dim = q` (`IsElementaryAbelian.card_eq_pow_finrank` + `|H̄|=p^q`)。`U`-conjugation を
   `F_p`-線形作用 (`typeP_quotientCoprimeAction` 既存; mathlib `Representation` へ橋渡し or 加群直接)。
2. **Maschke/半単純**: `p ∤ |U|` (coprime) ⟹ `F_p[U]` 半単純、`H̄|_U = ⊕ 既約` (mathlib
   `RepresentationTheory/Maschke`, `Semisimple`, `RingTheory/SimpleModule/Isotypic`)。
3. **Clifford permutation (新規, mathlib 不在)**: `W₁` が `U`-isotypic 成分を置換、`UW₁`-既約 ⟹ 推移的。
   **ここが build の核心 (mathlib に無い)**。
4. **dichotomy**: `q = dim = k·dim(成分)`、`q` 素数 ⟹ `k∈{1,q}`。
5. **CaseA 構成 (k=q)**: `q` 成分を G-部分群 (`Hpart`, H̄→H→G 対応) に、位数 `p`、`a ∣ p-1`。
6. **CaseB 構成 (k=1)**: Schur (End 体, mathlib `Irreducible.lean`?) + Wedderburn
   (`RingTheory/SimpleModule/WedderburnArtin` 有限可除環=体)、`Ū` 巡回、整除性。

## 再利用する infra

- **repo**: `IsElementaryAbelian.zmodModule`/`card_eq_pow_finrank`/`mulAutEquivGeneralLinearGroup`
  (PRank.lean); `coprimeFrobeniusChiefFactor_card` (S11:722, Wielandt on H̄); `S03c_Thm37` /
  `S03g_Thm310Module` / `WielandtElabBridge` (coprime FPF action on el-ab を module 形で扱う**前例**、
  mirror 推奨); `typeP_quotientCoprimeAction` (S11:683, H̄ の action)。
- **mathlib**: `RepresentationTheory/{Maschke,Semisimple,Irreducible,Subrepresentation,Submodule}`;
  `RingTheory/SimpleModule/{Isotypic,WedderburnArtin,Basic}`。

## 新規に書く部分 (mathlib/repo 不在)

- **step 3 Clifford permutation** (W₁ が isotypic 成分を推移的に置換) ← 最重要・最難。
- **step 6 field model assembly** (CaseB の End 体 + 巡回 + 整除)。

## 進め方 (上流順)

step 0 (de-opacify) → 1 (bridge+dim) → 2 (Maschke 分解) → 3 (Clifford perm) → 4 (dichotomy) →
5/6 (CaseA/CaseB)。各 step を build-green で commit。step 3 が crux、難航時は ChatGPT 相談可
([[feedback-ask-chatgpt-for-elided-gaps]])。CaseA/CaseB carrier の opaque Prop field は
`True`+`trivial` で可、**実 field** (Hpart/a/u-整除) が本体。

## 注意

- `H̄ ⧸ N` の dependent quotient は `[N.Normal]` 依存 ⟹ `quotientMulEquivOfEq` で iso bridge
  (S11 既存知見、design note s11_wielandt_91)。`zmodModule` の `IsMulCommutative` diamond 注意
  (`WielandtPerFactorDischarge` の `subgroupZmodModule` 参照)。
- これは深い build。完了で (9.7) のみ解禁、(9.8)-(9.11) は別途指標論を要する。
