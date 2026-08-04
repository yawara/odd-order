---
id: 9507
slug: splitting-p-modular-system
title: "分裂 p-modular system の構成 (段 94 以降の gate)"
created: 2026-08-04
---

# 分裂 `p`-modular system の構成

**claim**: hub / main session (9500 band) / **状態**: ✅ 完了 (2026-08-04)

## なぜ要るか

[issue 9506](9506-modular-p-modular-system.md) の段 94 (Cartan 行列 `C = DᵀD`) 以降は
**`Irr(G)` を添字集合として持つ**必要がある。`D` の行添字が `Irr(G)` だからで、さらに
Navarro (6.13) の `Irr(B₀) = Irr(G/O_{p'}(G))` と BS 本証明の
`Irr(B₀) = {1_G = χ₀, …, χ_r}` の枚挙も同じものを要求する。

`Irr(G)` を `k`-側と同じ設計 (Wedderburn 分解の添字) で持つには、
**`K = Frac(𝒪)` が `K[G]` を分裂させる**必要がある。

## ⚠ 現行の `StandardSystem` では足りない (2026-08-04 実測)

`StandardSystem p = 𝕎(𝔽̄_p)` の商体 `K = Frac(𝕎(𝔽̄_p))` は **`ℚ_p` の最大不分岐拡大の完備化**。

* `p'`-乗根はすべて含む (だから Brauer 指標側は足りている)。
* **`ζ_p` を含まない** — `ℚ_p(ζ_p)/ℚ_p` は次数 `p−1` の**完全分岐**拡大。`p = 2` なら `i ∉ K`。
* `exp G` の `p`-部分に対応する乗根が指標値に出るので、**一般に分裂体でない**。

`StandardSystem.lean` の docstring が主張しているのは**剰余体側**の 2 条件だけ
(`k` が群環を分裂させる = 代数閉、`k` が `|G|_{p'}` 乗根を持つ) で、`K` の分裂には触れていない。
段 93 までは剰余体側しか使っていなかったので表面化しなかった。

## 数学的には何が要るか

* **Schur 指数は障害にならない**: `K` は完備離散付値体で剰余体が代数閉 ⟹ Lang の定理により
  **quasi-algebraically closed (C₁)** ⟹ Brauer 群が自明 ⟹ Schur 指数はすべて 1。
  したがって**指標値を含めれば分裂する**。
* ⟹ 必要なのは **`ζ_{exp G}` を添加するだけ**。標準構成は
  **`𝒪' = 𝕎(𝔽̄_p)[ζ_{p^a}]`** (`p^a = |G|_p`)。完備 DVR の**完全分岐**有限拡大で、
  剰余体は `𝔽̄_p` のまま ⟹ 同じ `p`-modular system の枠に収まる。

## ⚠⚠ Lean 側の障害 (2026-08-04 実測、これが本 issue の実質)

mathlib に**必要な拡大論が無い**:

* `Mathlib/RingTheory/DiscreteValuationRing/` は `Basic.lean` と `TFAE.lean` のみ。
  **DVR の有限拡大が DVR である**という定理は無い (grep 0 件)。
* `HenselianLocalRing` の instance は **(i) 体、(ii) `IsAdicComplete` から**の 2 つだけ。
  **「Henselian の有限拡大は Henselian」は無い**。
* **C₁ 体 / Lang の定理 / Brauer 群の自明性**も無い (grep 0 件)。

⟹ `𝕎(𝔽̄_p)[ζ_{p^a}]` を作って「完備 DVR で剰余体 `𝔽̄_p`」を示すには、
**mathlib レベルの拡大論を自前で建てる**ことになる。

## 選択肢 (未決定)

1. **完備 DVR の有限拡大論を建てる** — `𝕎(𝔽̄_p)[ζ_{p^a}]` が Henselian 局所 Noetherian
   であることまで。正攻法だが mathlib 規模。
   ⚠ `IsPModularSystem` は DVR を要求していない (Henselian 局所 + charZero + 剰余体 char p)。
   DVR が要るのは `BrauerLinearIndependence` の Nakayama で、そこは
   **Noetherian + `jacobson_eq_maximalIdeal`** があれば足りるはず — 要求を弱められる可能性あり
   (未検証、着手時に確認する)。
2. **古典的な設定に寄せる** — `R = ℤ[ζ_{|G|}]` の `p` 上の極大イデアルでの局所化 `R_M`。
   DVR (Dedekind の局所化) で `K = ℚ(ζ_{|G|})` は分裂体。
   ⚠ ただし **Henselian でない**ので `RootsOfUnityLift.lean` の
   `rootsOfUnityEquivResidue` (Hensel を使う) が効かない。`p'`-乗根の還元が単射・全射で
   あることを別途示す必要がある (可能なはずだが別ルート)。
3. **大域的な分裂を要求しない設計を続ける** — 段 93 では絶対既約性を**加群ごと**の仮説に
   することで回避した。段 94 で同じ手が使えるかは未検討 (`C = DᵀD` は `Irr(G)` 全体を
   要求するので、そのままでは苦しい)。

## 着手前にやること

- [ ] 選択肢 1 の「DVR でなく Noetherian で足りる」を実測で確認
      (`BrauerLinearIndependence` と `DecompositionNumber` の
      `IsDiscreteValuationRing` 使用箇所を trace)
- [ ] 選択肢 2 の Hensel 迂回が本当に書けるか、`RootsOfUnityLift.lean` の依存を見て判断
- [ ] そのうえで route を確定して着手

## 完了条件

`K = Frac(𝒪)` が `K[G]` を分裂させる `p`-modular system の **instance が具体構成で存在**し
(CLAUDE.md「carrier の構成可能性」)、段 94 の `Irr(G)` 添字化が乗る。

## 参照

- 親: [9506](9506-modular-p-modular-system.md) (段 94 の gate)
- 祖父: [0147](0147-q8-modular-char-theory-frozen.md) (Q₈ Brauer–Suzuki)
- 現行 system: `OddOrder/GroupTheory/RepresentationTheory/Modular/StandardSystem.lean`


---

## ✅ 解決 (2026-08-04) — 上の 3 案のどれでもない route

**採ったのは `𝓞_ℂ_[p]` = `ℂ_[p]` の付値環**。mathlib の
`Mathlib/NumberTheory/Padics/Complex.lean` に `ℂ_[p] = PadicComplex p` と
その付値環 `PadicComplexInt p` が既にある (2025 年追加, María Inés de Frutos-Fernández)。

### なぜこれで全部片付くのか

**`Frac(𝓞_ℂ_[p]) = ℂ_[p]` は代数閉**。したがって

* `K[G]` の分裂 = Maschke (char 0) + mathlib の
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` で**即座に**出る。
* **剰余体も代数閉** (monic を持ち上げ→根 (整閉性で `A` 内)→還元)。
  ⟹ `k[G]` 側も既存の `exists_algHom_pi_matrix_of_isAlgClosed` で無条件。

**⟹ Brauer の分裂体定理も Lang の定理 (C₁) も一切要らない。**
選択肢 1・2 が重かったのは、離散付値を保とうとすると分裂性を別途証明する必要が
あったから。**離散性のほうを捨てる**と分裂性がタダになる。

さらに **Henselian も完備性なしで出る**: 代数閉な商体の上では monic の根は
初めから `A` に在るので、`f(a₀) ∈ 𝔪` から線型因子を 1 本ずつ剥がして
`𝔪` が素であることを使えば `a₀` と同じ剰余類の根が取れる (Newton 反復不要)。
⟹ `IsPModularSystem` の class 定義は**無変更**のまま instance が付く。

### 代償と、それに対して行った一般化

`𝓞_ℂ_[p]` は Noether でも DVR でもない (値群が可除で `𝔪 = 𝔪²`)。既存の
Brauer 機構は DVR / PID を仮定していたので、次の 2 箇所を**本質的に一般化**した
(どちらも DVR 側は無変更で通る — DVR は局所 + Bézout ゆえ `ValuationRing` の instance を持つ)。

1. **`BrauerLinearIndependence`** — 一様化元 + Nakayama を捨て、
   「割り切りが全順序」だけを使う: 非零係数のうち他を全部割るもの `c_j` を取り、
   `c_j` で割った関係式の第 `j` 係数は `1`。one-step 補題がそれを `𝔪` に入れるので矛盾。
   Noether 性不要。補助 = `exists_dvd_forall_of_valuationRing`。
2. **`EigenspaceDecomposition`** — PID の「自由加群の部分加群は自由」を、
   `finite_eigenspace_of_separated` (内部直和のレトラクト ⟹ 有限生成) +
   `free_eigenspace_of_separated` (捩れ無し ⟹ Bézout で平坦 ⟹ 局所で自由) に置換。
   `LatticeEigenspaces` / `Reduction` / `DecompositionMatrix` / `DecompositionNumber`
   も `IsPrincipalIdealRing` → `ValuationRing` へ。

⚠ 「着手前にやること」に挙げた 3 項目は**この route では不要になった**ので未実施
(選択肢 1 の Noether 弱化・選択肢 2 の Hensel 迂回はいずれも採らなかった)。
ただし調査で得た事実 —
`BrauerLinearIndependence` の DVR 使用は「一様化元による割り算 + Nakayama」だけ、
`HenselianLocalRing` の使用は `RootsOfUnityLift` の全射性 1 箇所だけ —
は上の一般化の設計に直接効いた。

### 成果物

| ファイル | 内容 |
|---|---|
| `OddOrder/Algebra/AlgClosedFractionField.lean` | 整閉整域 + 代数閉な商体: 根の存在 / 剰余類指定の根 / 剰余体の代数閉性 / Henselian |
| `OddOrder/GroupTheory/RepresentationTheory/Modular/PadicComplexSystem.lean` | `IsPModularSystem p 𝓞_ℂ_[p]`、剰余体代数閉、`p'`-乗根 (上下)、`ℂ_[p]` の分裂 |

build green / `bin/check-warnings --strict` clean / AxiomsCheck 新規 11 件すべて
allowlist 内 (`propext`/`Classical.choice`/`Quot.sound` のみ)。

**⟹ 段 94 の gate は外れた。** `Irr(G)` の添字化は
`exists_algEquiv_pi_matrix_padicComplex` の `Fin n` を使う。
