---
id: 41
slug: bg-appa-a2-dim-reduction
title: "BG App.A A.2 / Gorenstein 3.8.1 次元縮約 (char-p 二次既約 ⇒ dim V = 2)"
created: 2026-05-28
---

# BG App.A A.2 / Gorenstein 3.8.1 次元縮約 (char-p 二次既約 ⇒ dim V = 2)

> **この issue は単独で読めるように書いてある**(別セッション引き継ぎ用)。前提知識ゼロから着手できる。
> **2026-05-28 (late PM) 更新**: `references/gorenstein/` 追加で Gorenstein 3.8.1 の証明本体
> (mmd L2204+) が読めるようになった。本 issue は**証明の再構成ではなく、Gorenstein 原文の
> Lean への翻訳**になった。内容は初等線形代数(rank-nullity / Jordan / ブロック行列 / 置換共役)
> で、当初想定の「char-p 加群表現論(primitivity / module-Clifford / tensor 分解)」は不要だった。
>
> **★ 2026-05-28 (late PM) 再更新**: Gorenstein 8.1 Step 4-5 を精読、**Jordan canonical form は不要**と判明。
> 実際に proof が使うのは `R: V₁ ≅ V₂` 同型(より正確には `T := (x₂-1)∘(x₁-1): V₂ → V₂` 同型)の
> **eigenvector 1 個**だけで、Jordan form 全体は不要。mathlib `Module.End.exists_eigenvalue`
> (alg-closed + finite-dim + nontrivial)で直接。Step 4 自前実装見積もり ~200 行 → **~30-50 行**。
> 詳細: 下記「★ Step 4 の精密化」節 + [`notes/bg/appA_pstability.md`](../../notes/bg/appA_pstability.md)
> 「★ 2026-05-28 (late PM) 追補」節。

## 背景 — なぜこれが要るか

Feit–Thompson(奇数位数定理)の Lean 形式化プロジェクト。BG (Bender–Glauberman,
_Local Analysis for the Odd Order Theorem_) の局所解析パートを形式化中。その核心に
**BG Thm 6.2 (Glauberman の normal-J / Z(J) 定理)** = `Z(J(S))·O_{p'}(G) ⊴ G` があり、
§7–§9 (Uniqueness) で 7+ 箇所引用される。

問題: **Isaacs FGT は Glauberman Z(J)-定理を明示的に省く**(Isaacs p.217)。⇒ Thm 6.2 は
Isaacs へ「読み替え」不能。解決ルートとして **BG App.A (p-Stability) + App.B (Puig L(S))** を採る
(設計決定: [`notes/meta/log/bg_s6_appAB_route_2026_05_28.md`](../../notes/meta/log/bg_s6_appAB_route_2026_05_28.md))。

2026-05-28 の kernel-connection spike で、そのルートの **唯一の実質的な数学的欠落** が
本 issue の対象だと判明した(同ノート **§0**)。依存連鎖:

```
Thm 6.2 ⟸ App.B Thm B.4 ⟸ Thm A.5 ⟸ Thm A.4(c) ⟸ Thm A.3 ⟸ Thm A.2 ⟸ Thm A.1
                                                                    ↑
                                              ★ 本 issue = A.2 の「次元縮約パート」
```

- A.5, A.4, A.3 は A.2 の上に積む(reduction glue、別途)。
- **A.1**(dim-2 base)は部品が揃っている(下記「使える部品」)。
- **A.2 の証明本体 = Gorenstein 3.8.1 の「次元 2 への縮約」**。BG App.A は *"follow the proof
  of Theorem 3.8.1 of **G** up to page 105, where V is shown to have dimension 2"* と書くだけ。
  **Gorenstein 原文は repo に追加済**(`references/gorenstein/finite-groups.{pdf,mmd}`、
  Ch.3 §8 Thm 8.1 = G's 3.8.1, mmd **L2204 statement / L2210–L2240 proof**)。

⚠️ よくある誤解(spike で訂正済 — §0): repo の `gl2_pSubgroup_centralizes_of_normalizes`
(Isaacs Lem 7.3)や `sylow_normal_of_elementary_normal_P_theorem`(Thm 7.5)は **この
次元縮約ではない**。7.3 は GL(2,p) の補題で reduced J(P) 経路 (7.5/7.6) 専用。7.5 の次元縮約は
`|V:C_V(P)| ≤ p` を**仮説に取る**(二次作用はそれを dim≤2 でしか満たさない、rank-nullity)。
**本 issue は別物の新規証明 = Gorenstein 8.1 の翻訳**。

## ターゲット(正確な statement)

### 主目標 = 次元縮約補題

BG Thm A.2 の証明本体(= Gorenstein Ch.3 §8 Thm 8.1 の弱化形)。informal:

> `p` を奇素数、`F` を `F_p` の代数閉包、`V` を有限次元 `F`-ベクトル空間とする。
> `G ≤ GL(V)` が `V` 上 **忠実かつ既約** に作用し、`G` が **2 つの**「二次最小多項式を持つ
> `p`-元」で生成されているとする。ならば `dim_F V = 2`。

補足: 「二次最小多項式を持つ `p`-元」= `(ρ x - 1)² = 0` かつ `ρ x ≠ 1` な `x`。char `p` では
`(x-1)²=0 ⇒ x^p = 1`(`n := x-1`, `n²=0` ⇒ `x^p = (1+n)^p = 1 + p·n = 1`)なので自動的に
位数 `p` の元。⇒ 仮説は実質「`(ρx−1)²=0, ρx≠1`(`y` も)、`p` 奇、忠実既約、`G=⟨x,y⟩`」。

Lean signature 案(細部は実装者調整 — 既約の符号化と表現の型は要検討):

```lean
-- F = AlgebraicClosure (ZMod p) のような alg-closed char-p 体
theorem quadratic_two_generated_irreducible_finrank_eq_two
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    {G : Type*} [Group G] [Finite G] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hirr : IsSimpleModule (MonoidAlgebra F G) ρ.asModule)   -- ← 既約 (要確認: asModule の正確な綴り)
    (x y : G) (hgen : (⊤ : Subgroup G) = Subgroup.closure {x, y})
    (hx : (ρ x - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : (ρ y - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    Module.finrank F V = 2 := by
  sorry
```

(`ρ x` は `Module.End F V` の元として扱う。`ρ x - 1` の `1` は `LinearMap.id`。`IsSimpleModule`
での既約符号化が扱いにくければ「`G`-不変部分空間は `⊥` か `⊤` のみ」で直書きしてよい。)

### A.2 本体(縮約 + A.1、follow-on)

`dim V = 2` が出たら A.2 は A.1 で閉じる:

> **A.2**: 上記仮説(忠実既約・二次 `p`-元 2 生成・`p` 奇)⇒ `|G|` は偶数。
> 証明: 縮約補題で `dim V = 2`。`G` は非自明 `p`-元を含むので `p ∣ |G|`。もし `|G|` 奇なら
> A.1 が `p ∤ |G|` を与え矛盾。∴ `|G|` 偶。

A.2 まで仕上げてくれてよいが、**最小の deliverable は次元縮約補題**(`= 2`)。A.1/A.2 の
assemble は短い follow-on。

> Gorenstein 8.1 の full conclusion は `G ⊇ SL(2,p)`(dim=2 + Dickson Ch.2 §8 Thm 8.4)で
> BG A.2 より強い。**BG A.2 weakening(`|G|` 偶のみ)なら Dickson は不要**で、上記 dim=2 +
> repo A.1 で閉じる。Dickson 形式化を回避できる利点があるので、BG の weakening を採るのが推奨。

## 証明戦略 = Gorenstein 8.1 (mmd L2210–L2240) の Lean 翻訳

Gorenstein Ch.3 §8 Theorem 8.1 の証明は **完全に初等線形代数**で、次の 5 ステップ:

1. **rank-nullity**: `xᵢ` は char `p` 上の `p`-element で min poly `(X-1)²` ⇒ `(xᵢ-1)² = 0`。
   `Wᵢ := im(xᵢ-1) ⊆ ker(xᵢ-1) = C_V(xᵢ) =: Vᵢ`。rank-nullity ⇒ `d ≤ 2dᵢ`(`d = dim V`,
   `dᵢ = dim Vᵢ`)。

2. **既約性で `V₁ ∩ V₂ = 0` 強制**: `dᵢ > d/2`(つまり等号 `d = 2dᵢ` でない)を仮定 ⇒
   `W := V₁ ∩ V₂ ≠ 0`(次元数え)。両 `x₁, x₂` は `W` 上自明、`G = ⟨x₁, x₂⟩` も `W` 上自明 ⇒
   既約より `V = W` ⇒ `G` 自明 ⇒ `G` 忠実だが `G = 1` で contradiction(`xᵢ ≠ 1` 仮定と矛盾)。
   よって `d₁ = d₂ = d/2 =: m`、`V = V₁ ⊕ V₂`。

3. **ブロック行列形**: `V₁` の基底 `{v_i}_{1≤i≤m}` を取り、`v_{m+i} := vᵢ(x₁-1)` で `V₂` の基底
   を生成(`x₁-1: V₂ → V₁` 同型)。この `(v_i)_{1≤i≤2m}` 基底で:

   ```
   x₁ = (I 0)    x₂ = (I R)         (R は x₂-1: V₁→V₂ の同型行列、非特異)
        (I I)         (0 I)
   ```

4. **Jordan canonical form + 置換共役**(Gorenstein 原文): `R` を `F` 代数閉なので Jordan canonical form
   `S = Q⁻¹RQ` に。基底変換で `x₂ = (I S / 0 I)`。`S` は対角値非零の lower triangular。
   さらに **「行 2 と行 `m+1` を入れ替える置換行列 `P`」で共役**を取ると、新基底 `(u_i)` で:

   ```
   x₁ = (1 0      *)    x₂ = (1 λ      *)     (λ = S の (0,0) 成分)
        (1 1      *)         (0 1      *)
        (*  *     *)         (*  *     *)
   ```

   ⇒ **`u₁, u₂` が張る 2 次元部分空間 `U` は `x₁` と `x₂` の両方で不変**。

5. **既約性で `U = V`**: `G = ⟨x₁, x₂⟩` も `U` 不変。`U ≠ 0`(`u₁ ≠ 0`)、既約 ⇒ `U = V` ⇒
   **`dim V = 2`**。∎

(Gorenstein はこの後 Dickson でさらに `SL(2,p) ⊆ G` を出すが、**BG A.2 の `|G|` 偶のためには
ここまで(dim=2)で十分**。後は repo A.1 で閉じる。)

### ★ Step 4 の精密化: Jordan form 不要(eigenvector 1 個で足りる)

Gorenstein 8.1 Step 4-5 を精読すると、**「`S` が Jordan canonical form である」という構造全体は
不要**で、**`S` の最初の列が `(λ, 0, …, 0)ᵀ`(= `e₁` が `S` の eigenvector)**だけで議論が回る。

理由: 置換共役後、`x₂ u₂` の `U = span(u₁, u₂)` 外への成分は `S` の最初の列の (2 行目以降) で
支配される。これがゼロ ⇔ `S e₁ = λ e₁` ⇔ `R` の対応する元が eigenvector。

⇒ **Jordan form 全体を構成せず、`R` の eigenvector 1 個で足りる**。

**Clean argument (Jordan form を使わない、Lean 実装で採るべき版)**:

```
T := (x₂ - 1) ∘ (x₁ - 1) : V₂ → V₂        -- composition of two isomorphisms
  (x₁ - 1)|_{V₂} : V₂ → V₁ iso, (x₂ - 1)|_{V₁} : V₁ → V₂ iso
T 非特異, V₂ 有限次元 nontrivial, F alg-closed
⇒ ∃ v ∈ V₂ \ {0}, ∃ λ ∈ F \ {0}, T(v) = λ v        -- Module.End.exists_eigenvalue

u₁ := v ∈ V₂                              -- nonzero eigenvector
u₂ := (x₁ - 1)(v) ∈ V₁                    -- in V₁ via the iso (x₁-1)|_{V₂}

U := span(u₁, u₂)
  - u₁, u₂ 線形独立 (V₁ ∩ V₂ = 0, u₁ ∈ V₂\0, u₂ ∈ V₁\0 since (x₁-1)|_{V₂} 単射)
  - x₁ u₁ = u₁ + (x₁-1)(u₁) = u₁ + u₂        ∈ U  ✓
  - x₁ u₂ = u₂                  (u₂ ∈ V₁)    ∈ U  ✓
  - x₂ u₁ = u₁                  (u₁ ∈ V₂)    ∈ U  ✓
  - x₂ u₂ = u₂ + (x₂-1)(u₂) = u₂ + T(v) = u₂ + λ u₁  ∈ U  ✓

⇒ U は x₁, x₂ 不変 ⇒ G = ⟨x₁,x₂⟩ 不変 ⇒ G-submodule.
既約 + u₁ ≠ 0 ⇒ U = V ⇒ dim V = 2. ∎
```

つまり Step 4-5 はまとめて 「`T` の eigenvector + `U` 不変性 + 既約 ⇒ `dim V = 2`」 の
**~30-50 行**。

**Lean 翻訳の中身**(更新版):
- ステップ 1, 2: `LinearMap.range_le_ker_iff` (or 同等), `LinearMap.finrank_range`,
  rank-nullity (`LinearMap.finrank_range_add_finrank_ker` 等), `IsSimpleModule.eq_top` 系の
  既約性論証。
- ステップ 3: `V = V₁ ⊕ V₂` を `Submodule.IsCompl` で取り、`v_{m+i} = (x₁-1)(v_i)` の基底構成は
  不要(`u₂ := (x₁-1)(v)` を直接定義すれば足りる)。
- ステップ 4-5: **`T := (x₂-1)∘(x₁-1): V₂ →ₗ V₂`** を作り、`Module.End.exists_eigenvalue`
  (`[IsAlgClosed F] [FiniteDimensional F V₂] [Nontrivial V₂]`) で eigenvector を得る。
  `u₁ := v`, `u₂ := (x₁-1)(v)`, `U := Submodule.span F {u₁, u₂}` の不変性 4 本を proof.
  `IsSimpleModule + Nontrivial U ⇒ U = ⊤` で `Module.finrank F V = 2`(= `finrank_span` 等)。
- **Jordan form / generalized eigenspace 系は使わない**。

## repo で使える部品(確認済・sorry-free)

| 部品 | 名前 / 場所 | 用途 |
|---|---|---|
| **BG Thm 2.6** (体一般, 2-dim faithful) | `OddOrder.BG.Ch1.S02.odd_two_dim_sylow_abelian` / `odd_two_dim_abelian`([S02_Representations.lean](../../OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) L4627/L4680) | **A.1 の主部品**。`Odd |G|`, `finrank F V = 2`, faithful `ρ`, `p ∣ |G|`, `CharP F p` ⇒ Sylow-`p` abelian ∧ `G' ≤ P` |
| p-group fixed vector | `OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector.{exists_fixed_vector_ne_zero, invariants_ne_bot}` (L289/L197) | **A.1**: char-`p` で `p`-群の固定ベクトル `≠ 0` |
| mathlib | `Representation` / `Module.End` / `Module.End.eigenspace` / `LinearMap.range` / `LinearMap.ker` / `Module.finrank` / `Module.Basis` / `IsSimpleModule` / `Polynomial.splits` / Jordan/eigenspace API | 線形代数の基盤 |

### A.1 の組み立てレシピ(prover への確認用、follow-on)

A.1: `V` 2-dim over `F` (odd char `p`), `G ≤ GL(V)` 有限既約, `|G|` 奇 ⇒ `p ∤ |G|`。
1. `p ∣ |G|` と仮定。
2. `odd_two_dim_sylow_abelian` ⇒ Sylow-`p` `P` は abelian, `G' ≤ P`。
3. `G' ≤ P` ⇒ `P ⊴ G`(`P/G'` は abelian `G/G'` の部分群なので正規)。
4. `P` は正規 `p`-群 → char `p` 作用で `C_V(P) ≠ 0`(`PGroupFixedVector`)、`C_V(P)` は
   `G`-不変 → 既約より `C_V(P) = V` → `P` は自明作用 → 忠実より `P = 1`。`p ∣ |G|` と Sylow に矛盾。
5. ∴ `p ∤ |G|`。∎

## 直接は使えないもの(誤解しやすい点)

- `gl2_pSubgroup_centralizes_of_normalizes` (Lem 7.3) と `sylow_normal_of_elementary_normal_P_theorem` (Thm 7.5):
  **本 issue には使わない**(reduced J(P) 経路の道具。理由はノート §0)。
- `OddOrder.RepresentationTheory.Clifford.lean` は **ℂ 上の指標 Clifford**(Isaacs 6.5、しかも
  proof deferred)。本 issue が必要としていると当初(spike 段階で)思っていた「`F̄_p` 上の加群
  Clifford」**は実際には不要**(Gorenstein 8.1 の proof を読むと出てこない)。流用不要・不可。
- `OddOrder.RepresentationTheory.EigenspaceUnderCyclicAction.lean` は BG Prop 2.4 用(ℂ 寄り)。
  本 issue には**ほぼ不要**(Jordan/eigenspace は mathlib の `Module.End.eigenspace` で直接組める)。

## 作るかもしれないインフラ

**新規インフラ: 不要**(2026-05-28 late PM 確認済)。

不要だと当初想定していた中で確定したもの:
- ~~**Jordan canonical form**~~ — Step 4 の精密化で eigenvector 1 個で十分と判明。
  mathlib `Module.End.exists_eigenvalue` (`LinearAlgebra/Eigenspace/Triangularizable.lean:63-66`)
  で直接。**自前実装不要**。
- ~~加群の primitivity / imprimitivity~~ — proof に出てこない。
- ~~加群 Clifford(homogeneous component 分解)~~ — proof に出てこない。
- ~~tensor 分解~~ — proof に出てこない。

参考 — mathlib にあるが本 issue では使わないもの:
- `Module.End.iSup_maxGenEigenspace_eq_top [IsAlgClosed]` (Triangularizable.lean L75-137)
- Jordan-Chevalley 分解 (`Module.End.exists_isNilpotent_isSemisimple`, JordanChevalley.lean L76-101)
- packaged Jordan canonical form は mathlib に**無い**(が、本 issue では不要なので問題なし)。

## やること(着手順)

- [ ] **(A.1)** 上記レシピで A.1 を組む(部品済、interface/型の早い確認)。新規ファイル
      `OddOrder/BG/AppA_PStability.lean`(または相当)を作る。配置は ROADMAP / 既存 BG 構成に合わせる。
- [ ] **(縮約 Step 1-3)** `V₁ ∩ V₂ = 0`, `V = V₁ ⊕ V₂` を `Submodule.IsCompl` で。
      rank-nullity + 既約性論証。
- [ ] **(縮約 Step 4-5)** `T := (x₂-1)∘(x₁-1): V₂ →ₗ V₂` 構成 → `Module.End.exists_eigenvalue`
      で `(v, λ)` 取得 → `u₁ := v`, `u₂ := (x₁-1)(v)`, `U := span {u₁, u₂}` 不変性 4 本 →
      既約より `U = V` → `Module.finrank F V = 2`。
- [ ] **(A.2)** 縮約 + A.1 で A.2(`|G|` 偶)を閉じる。Dickson 不要。

## 完了条件

- 次元縮約補題(`finrank F V = 2`)が `sorry`/`axiom` 無しで証明され `lake build` が通る。
- できれば A.1・A.2 も sorry-free で配線(A.2 = 本ルートの真のゲート)。
- docstring に `**BG Thm A.2** (= Gorenstein 3.8.1 weakening, mmd L2204+)` のトレーサビリティ。
- 完了後 `notes/meta/log/bg_s6_appAB_route_2026_05_28.md` §0 と per-section
  [`notes/bg/appA_pstability.md`](../../notes/bg/appA_pstability.md) の状態を更新。

## 参照

- **設計・依存閉包・リスクモデル(必読)**: [`notes/meta/log/bg_s6_appAB_route_2026_05_28.md`](../../notes/meta/log/bg_s6_appAB_route_2026_05_28.md) **§0 + §0.1**(spike 訂正 + Gorenstein 追加後の再評価)
- per-section: [`notes/bg/appA_pstability.md`](../../notes/bg/appA_pstability.md) / [`notes/bg/s06_additional.md`](../../notes/bg/s06_additional.md)
- **Gorenstein 1968 原文**(本 issue の primary source、`references/gorenstein/finite-groups.mmd`):
  Ch.3 §8 Thm 8.1 **statement L2204 / proof L2210–L2240**(本 issue の翻訳対象)。
  関連: Ch.3 §8 Thm 8.2/8.3/8.4(BG A.3 の materials)、Ch.2 §8 Thm 8.4(Dickson、BG A.2 では不要)。
- BG 原文: `references/bg/local-analysis.mmd` — A.1 L4460–4464, **A.2 L4468–4472**, A.3 L4476, A.4 L4480–4485, A.5 L4488–4513, App.A 序文 L4452–4458。
- repo 部品: S02 `odd_two_dim_sylow_abelian` (L4680) / `PGroupFixedVector`。
- ポリシー: CLAUDE.md「Gorenstein 1968 は形式化対象ではない…BG の行間を埋めるためにのみ原文参照」
  — 本 issue がまさにその典型用途。Gorenstein 全形式化はしない。
- 隣接 issue: closed #0035 (Thm 2.6 は S02 で実装済)、#28 (Prop 2.4)、#33 (AbsolutelyIrreducible)。
- 下流(A.2 が出来た後): A.3 → A.4(a/b/c) → A.5 → App.B(B.1–B.4)→ BG §8–§16 を L(S) 化。
