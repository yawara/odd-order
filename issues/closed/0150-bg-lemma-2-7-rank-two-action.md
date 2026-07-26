---
id: 150
slug: bg-lemma-2-7-rank-two-action
title: "BG Lemma 2.7: (Z/q)² が (Z/p)² に忠実作用 ⟹ q ∣ p−1 かつ冪写像 α が在る"
created: 2026-07-26
---

# BG Lemma 2.7 — rank-2 elementary abelian が rank-2 elementary abelian に忠実作用

## 位置づけ

**3 冊スコープで残る「真に未形式化の数学」のうち、文書順で最も上流の項目** (2026-07-26 の
全数再実測の結論; 正本 = `notes/meta/three_books_full_survey_2026_07_16.md` の
「BG の突き合わせ」「Pf 特殊化債務リストの再実測」節)。Isaacs は完済、BG の残りは本項 +
§16 tame-embedding (issue 8005 で意図的 defer) + App.C Rem (II)/(V)、Pf の残りは
(6.2)-(6.6) の h56 oracle + packaging のみ。

## 主張 (BG p.31, Lemma 2.7)

`p ≠ q` を素数、`P ≅ (ℤ/p)²`、`Q ≅ (ℤ/q)²` とし、`Q ≤ Aut(P)` (忠実作用) とする。このとき

- **(a)** `q ∣ p − 1`;
- **(b)** ある `α ∈ Q^#` が冪写像として作用する: `∀ x ∈ P, α x = x^r` で
  `r^q ≡ 1 (mod p)` かつ `r ≢ 1 (mod p)`。

## 実測状況 (2026-07-26)

**未形式化** (07-16 調査の "VERIFIED missing (refutation attempted and failed)" を再確認)。
repo 内の `2.7` ラベルは全て Isaacs Lem 2.7 / Peterfalvi (2.7) / BG Thm 12.7 / 表示式 (12.7)。

Coq 対応物 `regular_abelem2_on_abelem2` (`BGsection2.v:1048`) は Coq 側でも FT 証明本体から
未使用 — **純粋な書籍完備性項目**で、下流を unblock しない (だが CLAUDE.md の方針どおり
「payoff の遠さ」は着手判断の基準にしない)。

## 証明ルート (BG 原文 + 既存インフラ)

`P` を 2 次元 `𝔽_p`-ベクトル空間と見る。

1. **既約でない**: `Q` は可換だが非巡回。`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`
   (`OddOrder/GroupTheory/RepresentationTheory/SingerField.lean:494`) の対偶 —
   忠実かつ既約なら `Q` は巡回。⟹ `Q`-部分加群として真の直線 `L₁` が在る。
2. **完全可約**: `|Q| = q²` と `|P| = p²` は互いに素なので Maschke で補空間 `L₂` が取れる
   (`P = L₁ ⊕ L₂`、両方 1 次元)。
3. **スカラー指標**: `Q` は各直線に `𝔽_p^×` のスカラーで作用 ⟹ 指標
   `χ₁, χ₂ : Q →* 𝔽_p^×`。`Q` の指数は `q` なので `χ_i^q = 1`。
4. **忠実性**: `(χ₁, χ₂) : Q ↪ μ_q × μ_q` が単射。`|Q| = q²` ゆえ全単射で、特に
   `μ_q ⊆ 𝔽_p^×` は位数 `q` ⟹ **`q ∣ p − 1`** = (a)。
5. **(b)**: 4 の全射性から `χ₁(α) = χ₂(α) = ζ` (原始 `q` 乗根) となる `α` が取れる。
   この `α` は `P` 全体で `x ↦ x^r` (`r = ζ` の代表) として作用し、`r^q ≡ 1`、`r ≢ 1`。

## 既存インフラ

| 部品 | 所在 |
|---|---|
| Singer 順序限界 (忠実+既約+可換 ⟹ 巡回・位数 ∣ `|M|−1`) | `RepresentationTheory/SingerField.lean:494` |
| `q ∣ p²−1` (rank ≤ 2 への素数位数自己同型) — **本項より弱い** | `GroupTheory/PRank.lean` `prime_dvd_prime_sq_sub_one_of_orderOf_mulAut` |
| Singer field data / `μ : C →* Kˣ` | 同 `SingerField.lean` (`nonempty_singerFieldData`) |

### 2026-07-26 追調査 — Lean 側の橋渡し経路

- **モジュール構造**: `SingerField` 系の定理は `[Module (MonoidAlgebra (ZMod p) C) M]` を
  **instance 仮説として取る**(自分では作らない)。よって `φ : Q →* MulAut P` から作る必要がある。
  経路は mathlib 標準の **`Representation.asModule`** で、本 repo 内に使用実績あり:
  - `BG/Ch1_Preliminary/S02_RepresentationsBasic.lean:776` (Maschke + `Representation.asModule` 橋)
  - `BG/Ch1_Preliminary/S03d_Thm34.lean:339,353` (`Representation.asModuleEquiv_map_smul` /
    `asAlgebraHom_single_one` の実使用)
- **elementary abelian → ZMod p 加群**: `IsElementaryAbelian.zmodModule`
  (`GroupTheory/PRank.lean:87`) が `Module (ZMod p) (Additive E)` を与える。次元は
  `hE.card_eq_pow_finrank` で `|E| = p^n`。**setup の書き方の手本は
  `PRank.prime_dvd_prime_sq_sub_one_of_orderOf_mulAut` (:354)** — 同じ「rank ≤ 2 の
  elementary abelian に素数位数自己同型」設定を `letI := hE.zmodModule` で回している。
- **(a) は 1 本の非自明指標だけで出る**: `χ₁, χ₂` の像は `𝔽_p^×` の `q`-捩れなので位数 1 か `q`。
  両方自明なら `Q` が自明作用 ⟹ 忠実性に反する。よって少なくとも一方が位数 `q` ⟹ `q ∣ p − 1`。
- **(b) の核勘定**: `χ₂` が自明なら `ker χ₁ ∩ ker χ₂ = ker χ₁ = 1` ⟹ `χ₁` 単射 ⟹ `Q ↪ μ_q` 巡回で
  `Q ≅ (ℤ/q)²` に矛盾。よって**両方非自明**で `|ker χᵢ| = q`、かつ `(χ₁,χ₂) : Q → μ_q × μ_q` は
  位数 `q²` 同士の単射 ⟹ 同型。よって `(ζ, ζ)` の逆像 `α` が両直線に同一スカラー `ζ` で作用 =
  `x ↦ x^r`。

⚠ **Maschke の適用形** (`|Q| = q²` と `p` が互いに素 ⟹ 完全可約) が repo のどの補題で出るかは
未確定。`S02_RepresentationsBasic.lean` の Maschke 節をまず読むこと。

## 完了条件

- (a)(b) を書籍強度の単一定理 (または 2 定理) として sorry-free で landing。
- `AxiomsCheck.lean` に登録して axiom-clean を確認。
- ⚠ **sorried statement を先に置かない** (現在 repo の実 sorry は Q₈ Brauer-Suzuki の 1 件のみ。
  非退行を守る)。

## 目標シグネチャ (2026-07-26 確定 — 加群言語で述べる)

群言語 (`P`, `Q : Type`, `φ : Q →* MulAut P`) で直接述べると `hP.zmodModule` の `letI` 束縛が
statement に露出して instance 合成が詰まる (PRank の docstring が明記している既知の罠;
[[lean-instance-defeq-traps]])。よって**本体は加群言語で述べ、群言語版は PRank の
`mulAutEquivGeneralLinearGroup` / `addAutEquivGL` 経由の packaging 系として別に置く**。

```lean
theorem <name> {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p)
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    (hrank : Module.finrank (ZMod p) M = 2)
    {Q : Type*} [CommGroup Q] [Finite Q]
    (hQexp : ∀ x : Q, x ^ q = 1) (hQcard : Nat.card Q = q ^ 2)
    (ρ : Representation (ZMod p) Q M) (hfaith : Function.Injective ρ) :
    q ∣ p - 1 ∧ ∃ α : Q, α ≠ 1 ∧ ∃ r : ZMod p, ∀ x : M, ρ α x = r • x
```

### Singer の正確なシグネチャ (実測)

```
isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible :
  ∀ {p : ℕ} [Fact p.Prime] {C M : Type u}
    [CommGroup C] [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) C) M] [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M],
    (∀ c : C, (∀ x : M, (MonoidAlgebra.of (ZMod p) C) c • x = x) → c = 1) →
    IsCyclic C ∧ Nat.card C ∣ Nat.card M - 1
```

⚠ `[IsCyclic C]` も `[Finite C]` も**不要** (どちらも導出される)。`Module (MonoidAlgebra …) M` は
`Representation.asModule` で作る (`Representation.instModuleMonoidAlgebraAsModule`)。

### ステップ対応表

| 段 | 内容 | 使う物 |
|---|---|---|
| 1 | `¬ IsCyclic Q` | 指数 `q` かつ `|Q| = q²` |
| 2 | 既約でない | 上記 Singer の**対偶** |
| 3 | 半単純 (Maschke) | `NeZero (Nat.card Q : ZMod p)` (`q ≠ p`) → `IsSemisimpleModule`。手本は `BG/Ch1_Preliminary/S02_RepresentationsBasic.lean` の `exists_simple_submodule_of_neZero_card` (⚠ `private`、公開版が要る) |
| 4 | 2 直線への分解 | 非既約 + 半単純 + `finrank = 2` |
| 5 | 各直線のスカラー指標 `χᵢ : Q →* (ZMod p)ˣ` | 1 次元表現 |
| 6 | (a) `q ∣ p−1` | 少なくとも一方の `χᵢ` が非自明 (両方自明なら忠実性に反する) |
| 7 | (b) `α` | 両方非自明 (片方自明 ⟹ `Q ↪ μ_q` 巡回で矛盾) ⟹ `(χ₁,χ₂)` は位数 `q²` 同士の単射 = 同型 ⟹ `(ζ,ζ)` の逆像 |

## 2026-07-26 probe 結果 — 段 3 の障害は消えた

`lake env lean` で直接確認した (scratch probe):

1. **Maschke の private 版は不要**。`NeZero (Nat.card Q : ZMod p)` と
   `[Module.Finite (ZMod p) M]` があれば
   ```lean
   example (ρ : Representation (ZMod p) Q M) [NeZero (Nat.card Q : ZMod p)]
       [Module.Finite (ZMod p) M] :
       IsSemisimpleModule (MonoidAlgebra (ZMod p) Q) ρ.asModule := by infer_instance
   ```
   が**そのまま通る** (mathlib の Maschke instance が効く)。よって
   `S02_RepresentationsBasic` の `private exists_simple_submodule_of_neZero_card` を
   公開化する必要は**ない**。
2. **補空間の取り出し**は `exists_isCompl` で足りる (`IsSemisimpleModule R M` は
   `ComplementedLattice (Submodule R M)` そのものなので):
   ```lean
   example (R M : Type) [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
       (N : Submodule R M) : ∃ N' : Submodule R M, IsCompl N N' := exists_isCompl N
   ```
   ⚠ `IsSemisimpleModule.exists_isCompl` / `IsSemisimpleModule.complementedLattice` /
   `Submodule.finrank_add_finrank_le_of_isCompl` は**存在しない名前**。
3. `NeZero (Nat.card Q : ZMod p)` を作る補題 `neZero_nat_card_cast_of_isPGroup_ne_char` は
   `S02_RepresentationsBasic.lean:687` にあるが **`private`** — ここだけは公開版 (または
   その場での再証明) が要る。`|Q| = q²` と `q ≠ p` からの直接証明でもよい
   (`ZMod.natCast_self_eq_zero` 系 + `Nat.Coprime`)。

### 残る実装の重さ

`ρ.asModule` (型シノニム) 上の `MonoidAlgebra`-部分加群と `M` 上の `ZMod p`-部分加群の
往復 (`Representation.asModuleEquiv : ρ.asModule ≃ₗ[ZMod p] M`) と finrank の突き合わせが
最も fiddly。段 5-7 の指標解析は素直だが行数が出る。**複数 session 規模**の項目。

## ✅ 完了 (2026-07-26)

(a) `prime_dvd_sub_one_of_faithful_rank_two` / (b) `exists_powerMap_of_faithful_rank_two`
がともに sorry-free で landing (`51f977137` / `86be397b5`)。実体は新 leaf
`OddOrder/GroupTheory/RepresentationTheory/SingerReducibility.lean` (約 430 行、11 定理)。
AxiomsCheck 登録済み・axiom-clean。

**採った経路 (計画からの変更点)**

- 段 3 の Maschke: `private` の公開化は**不要**だった。`NeZero (Nat.card Q : ZMod p)` +
  `Module.Finite` があれば `IsSemisimpleModule … ρ.asModule` が `infer_instance` で通る。
- (b): `Q ≅ μ_q × μ_q` の同型を作って対角元を取る計画だったが、**商指標
  `ψ = χ₁ / χ₂ : Q →* 𝔽_p^×` の核**を見るほうが遥かに短い。像は `q` 乗根からなる巡回群の
  部分群なので位数が `q` を割り、`|Q| = q²` から核が位数 `q ≥ 2` 以上。μ_q の位数計算も
  全射性も不要になった。

**副産物 (汎用に切り出した補題)**

`Representation.not_isSimpleModule_asModule_of_not_isCyclic` (Singer の対偶) /
`exists_isCompl_finrank_one_of_not_isSimpleModule` (階数 2 半単純 → 2 直線、任意の体・環) /
`exists_scalar_of_finrank_eq_one_of_mapsTo` / `exists_monoidHom_scalar_of_finrank_eq_one` /
`exists_invariant_lines_of_not_isSimpleModule` (`ρ.asModule` ↔ `M` 輸送) /
`prime_dvd_sub_one_of_pow_eq_one`。

**踏んだ罠**: Singer 定理は `C, M` が同一 universe / `Representation` は `MonoidHom` の def
なのでドット記法が `MonoidHom.*` へ流れる / `omit … in` と `open … in` は docstring の**前** /
`Module.finrank_top` は存在せず root の `finrank_top` / mathlib に別命題の同名
`exists_smul_eq_of_finrank_eq_one` がある / **AxiomsCheck は新 leaf を import しないと
"constant not found"** (orphan leaf と同種)。
