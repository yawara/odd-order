---
id: 168
slug: pf-part2-ch4-psu3
title: "Peterfalvi Part II, Ch. IV: Characterization of PSU(3,q) (pp. 122-134)"
created: 2026-07-31
---

# Peterfalvi Part II, Ch. IV: Characterization of PSU(3,q) (pp. 122-134)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 進捗 (2026-07-31): §1 の `f`, `g`, `h`

`OddOrder/GroupTheory/RankOneBNPair.lean` (新 leaf)。

⚠ **設計判断**: 「2 重推移作用」から出発せず、証明が実際に使う**2 つの一意分解**を
仮説に取った:
* `M = Q ⋊ D` (`M` の元は一意に `q · d`)
* `L − M` の元は一意に `a · t · b` (`a ∈ M`, `b ∈ Q`) — 書籍が Ch. I §1 Prop 4 を
  引くところ
* `x ∈ Q^#` に対し `t x t ∉ M` (`Q^t ∩ M = 1` が効く箇所)

書籍自身がこの 3 つしか使っていないので、2 重推移性の一般論を先に積む必要がない
(必要になったら供給側で示せばよい)。

* `exists_fgh` — `t x t = g(x) h(x) t f(x)` を満たす `f, g, h : L → L` の存在
  (値の所属 `f x, g x ∈ Q`, `h x ∈ D` 込み)。
* `fgh_unique` — 2 組が `Q^#` 上で一致する (両方の一意分解から)。

* `Setup` / `IsFGH` — standing hypothesis を 2 つの構造にまとめた (下記)。
* `IsFGH.f_ne_one` / `g_ne_one` — **`f, g : Q^# → Q^#`** (書籍の型付けの根拠)。
  `f x = 1` なら `t x = g(x)h(x) ∈ M`、`g x = 1` なら `x t = (t h(x) t) f(x) ∈ M` で
  どちらも `Q^t ∩ M = 1` に反する。そのため `Setup` に `t x ∉ M` を入れてある
  (書籍の `t x t ∉ M ∪ Mt ∪ tM` のうち必要な部分)。

* `fgh_eq_of_canonical` — **読み取り補題**。`t y t = p · d · t · q`
  (`p, q ∈ Q`, `d ∈ D`) の形の分解は必ず `f, g, h` が与えるものと一致。
  (H1)-(H6) は全部「canonical 分解を書き下す + これで読み取る」の 2 段。
* `canonical_inv` / `canonical_f` / `canonical_conj` / `expand_mul` +
  `canonical_mul` — その canonical 分解たち (定義式の純粋な書き換え)。

* `hOne` — **(H1)** `f(x⁻¹) = g(x)⁻¹` + `g(x⁻¹) = f(x)⁻¹` + **(H4)**
  `h(x⁻¹) = (h(x)^t)⁻¹`。⚠ 要点は `h(x)⁻¹` を `t` の向こうへ押し出すこと
  (`D = M ∩ M^t` なので `t h(x)⁻¹ t ∈ D`)。
* `hTwo` — **(H2)** `f(f(x)) = x` + **(H4)** `h(f(x)) = h(x)⁻¹`。
  `t f(x) t = h(x)⁻¹ g(x)⁻¹ t x` が**そのまま canonical** なのが要点。
* `hThree` — **(H3)** `f(x^a) = f(x)^{a^t}` + `g` 版 + **(H4)**
  `h(x^a) = a^{-t} h(x) a`。⚠ **指数が `a` でなく `a^t`** — この計算で先に分かり、
  ページ画像で確認した (`pdftotext` が上付き `t` を落としていた)。
* `hFive` — **(H5)** `(f∘j)³(x) = x^{h(x)⁻¹}`。写像の等式として (H1) は
  `f∘j = j∘g`, `g∘j = j∘f` なので `(f∘j)³ = j ∘ (g∘f) ∘ g` に畳める。
  補助等式 `g(g(x)) = x` と `h(g(x)) = h(x)⁻¹` ((H1)+(H2) から、`t` 捻れが
  2 回で相殺) で `h(x) x h(x)⁻¹` に落ちる。
* `f_mul_g_ne_one` + `hSix` — **(H6)**。`z := f(x)g(y)` として
  `f(xy) = f(z)^{h(y)^t} f(y)`、`h(xy) = h(x)h(z)h(y)`、
  `g(xy) = g(x)·g(z)^{h(x)⁻¹}`。`z ≠ 1` は `expand_mul` で
  `t(xy)t = g(x)h(x)·(t z t)·(t h(y) t)·f(y)` と書いてから
  「`z = 1` なら右辺が丸ごと `M` に入る」で出る。

**技術メモ (5 回使った)**: `group` は `t * t = 1` を知らないので `t` 共役の
並べ替えがそのままでは通らない。**共役対の 2 つめの `t` を `t⁻¹` で書くと
自由群の恒等式**になって `group` が閉じ、`rw [hS.tinv]` で目的の形に戻せる。

### §1 の Lemma (p. 123) — 完了

書籍は `X` を `Q ∪ {a}` と同一視 (`x ∈ Q` ↔ 点 `a t x`) する。ここでは
`X = L ⧸ M`、`a` = `1` の剰余類、`a t x` = **`x⁻¹ t` の左剰余類**とした。
⚠ 左剰余類にすると `t` の作用がちょうど `f` になる (`x t` を使うと `g` が出る)。

* `Setup.conj_mem_Q` (`Q ⊴ M`) / `Setup.closure_M_union_t` (`L = ⟨M,t⟩`) /
  `Setup.closure_conj_Q` (`⟨Q^y | y ∈ L⟩ = ⟨Q ∪ Q^t⟩`) — 生成の部分。
  `f, g, h` を使わず分解 `L = M ∪ M t Q` だけから出る。
* `coords` / `coords_bijective` / `coordsEquiv` — 同一視 `Option ↥Q ≃ L ⧸ M`。
  単射性は `t ∉ M` と `t x t ∉ M`、全射性は `y = a t b`, `a = q d`,
  `d t M = t (t d t) M = t M`。⚠ `Setup` に `t ∉ M` を足した (書籍の
  「`t` は `L − M` の対合」; `Q^# ≠ ∅` を仮定しない限り他の field から出ない)。
* `coords_smul_t_some` — **`t` は `f` で作用する**。(H1) の
  `g(x⁻¹) = f(x)⁻¹` が効く。`coords_smul_t_none`/`_t_one` で `a ↔ 1` を交換
  ((H2) `f∘f = id` がこの対合性に対応)。
* `coords_smul_none_of_mem_M` / `_some_of_mem_M` — **`M` は `Q ⋊ D` だけで
  作用する** (`m x⁻¹ = q d` の `D` 成分は `d t M = t M` で消える)。

忠実性は mathlib の `Subgroup.normalCore_eq_ker` (`M.normalCore = ⊥` ⟺
`MulAction.toPermHom L (L ⧸ M)` が単射)。これと `L = ⟨M,t⟩` を合わせて
`L` は `Equiv.Perm (Option ↥Q)` の中で `M = Q ⋊ D` と `f` から復元される。

**⟹ §1 完了** (`OddOrder/GroupTheory/RankOneBNPair.lean`, 714 行, sorry 0)。

### `⟨f,j⟩` の `Q^#/D` への作用 (p. 123 の注) — 完了

* `dOrbitRel` (+ `refl`/`symm`/`trans`/`inv`) / `IsFGH.dOrbitRel_f` /
  `IsFGH.dOrbitRel_fj_cube`。`j² = f² = (f∘j)³ = 1` が位数 6 の二面体群の提示。
  `f` が降りるのは (H3) の捻れ `a ↦ a^t` が `D` 内に留まるから、
  `(f∘j)³ = 1` は (H5) のずれ `x^{h(x)⁻¹}` が軌道上で見えないから。
* §2 step (5) で「`|D|` 奇数 ⟹ `j` は軌道集合上に不動点なし」を `f` へ移すのに使う。

### 仮説 (A1)-(A3) → `Setup` の橋渡し — 完了

`OddOrder/Peterfalvi/Appendices/Suzuki/RankOneSetup.lean` (新 leaf)。

⚠ **重要な発見**: Ch. IV §1 冒頭の設定は repo に既にある Part II の standing
hypothesis **`Hypothesis G Ω` (p. 97, (A1)-(A3))** と逐語で同じ。よって
`Setup` の 9 フィールドのうち 7 つは `Hypothesis` の公理そのもので、残り 2 つも
既存資産で埋まる:
* `fact` (`G − H` の一意分解 `H t Q`) = Ch. I §1 Prop 4 (a)
  = 既存の `Hypothesis.existsUnique_canonicalForm`
* `tconj` (`t x t ∉ H` for `x ∈ Q^#`) = `Q ∩ D = 1` (`t x t ∈ H` かつ `x ∈ H`
  はちょうど `x ∈ D`)

`Hypothesis.rankOneSetup` / `Hypothesis.exists_fgh` で **(H1)-(H6) と §1 の
Lemma が全部 `G` で使える**。

## §2 Preliminary Calculation (p. 123-124)

⚠ **以下はページ画像 `references/peterfalvi/pages/peterfalvi-p123.png` で確定**。
以前の `pdftotext` 転記は (1) の `a ∈ A^#`、(4) の結論 `ω = 1` など複数が誤り
だった ([[pdftotext-drops-superscripts]])。

(C2) より `tst = sts`。よって (H3) と (H4) から

* **(1)** `a ∈ K` に対し `f(s^a) = g(s^a) = s^{a⁻¹}` かつ `h(s^a) = a²`
* **(2)** `f(ω s^a) = f(f(ω) s^{a⁻¹})^{a⁻²} s^{a⁻¹}`  (`ω ∈ Q − Q₀`, `a ∈ K`)
  — (H6) を `x = ω`, `y = s^a` に適用
* **(3)** `f(ω s^a) = f(g(ω) s^{a⁻¹})^{h(ω)^t} f(ω)` — (H6) を `x = s^a`, `y = ω` に
* **(4)** `f(ωx) = f(ω)y` (`ω ∈ Q−Q₀`, `x,y ∈ Q₀`) なら **`x = 1`**
* **(5)** `f(ω) = (ωy)^a` (`ω ∈ Q−Q₀`, `y ∈ Q₀`, `a ∈ D`) なら `y ≠ 1` かつ `a ∉ K`
  — `|D|` が奇数ゆえ `j` は `Q−Q₀` の `D`-軌道集合上に不動点を持たず、
  `f` は誘導置換群の中で `j` と共役 (= 上記 p.123 の注) だから `f` も持たない
* **(6)** `f(ωx) = (f(ω)y)^a` (`x,y ∈ Q₀`, `y ≠ 1`, `a ∈ D`) なら `a ∈ K`

### 進捗 (2026-07-31): (1)-(3) 完了

`OddOrder/Peterfalvi/Appendices/Suzuki/PSU3Preliminary.lean` (新 leaf)。

* `fgh_at_distinguishedInvolution` — `f(s) = g(s) = s`, `h(s) = 1`。
  **`s t s` が既に §1 の canonical form** (`p = q = s ∈ Q`, `d = 1 ∈ D`) なので
  `fgh_eq_of_canonical` が直接読み取る。
* `fgh_at_conj_distinguishedInvolution` — **(1)**。(H3) が 3 つ全部を `a^t` で運び、
  `a ∈ K ⟺ a^t = a⁻¹` で `s^{a⁻¹}` と `a²` が出る。
* `f_mul_conj_distinguishedInvolution` — **(2)** ((H6) を `x = ω, y = s^a`)。
  指数 `a⁻²` は `h(s^a) = a²` の `t` 捻れ。
* `f_conj_distinguishedInvolution_mul` — **(3)** ((H6) を `x = s^a, y = ω`)。

⚠ **書籍の (3) は積の順序が両方逆** (`f(ω s^a) = f(g(ω)s^{a⁻¹})^{h(ω)^t}f(ω)`;
300dpi 画像で確認)。一致の理由は `s^a, s^{a⁻¹}` が `Q` の対合 ⟹ `Q₀ = Z(Q)` に属して
`Q` の全元と可換だから。repo では (H6) が直接与える形で述べ docstring に注記。

(C2) は `hC2 : t s t = s t s` を明示仮説で取っている ((C1)/(C2) の構造体は repo に
未形式化 — 書籍自身が §2 冒頭で「Ch. III の (C1)(C2) を再開する」と言うので仮説で正しい)。
Ch. III §3 原文の (C2) = 「`S` は type B の Suzuki 2-群、`st` の位数 3、`W ≠ 1`」で、
`st` の位数 3 ⟺ `tst = sts` (`s`,`t` が対合ゆえ)。

### (4) 完了 (2026-07-31)

**機関部 = `f`, `g` が `Q₀` を保存し、かつ反映する**:
`Q₀^#` は既存 `image_conj_KSet_eq_involutions_H` によりちょうど `{s^k : k ∈ K}` で、
段 (1) が `f(s^k) = g(s^k) = s^{k⁻¹}` (また対合) を与える。反映は `f∘f = id` ((H2)) と
`g∘g = id` から — 後者のため `g_involutive` を `hFive` の中から取り出して
`RankOneBNPair` の独立定理に格上げした。

* `exists_mem_KSet_conj_eq_of_mem_Q0` / `f_mem_Q0_of_mem_Q0` / `g_mem_Q0_of_mem_Q0`
  / `mem_Q0_of_f_mem_Q0` / `mem_Q0_of_g_mem_Q0` / `eq_one_of_f_mul_eq`

⚠ **(4) の証明で「書籍の (3) は順序が逆」問題が実際に効いた**: `f(ωx)` を
`f(s^k ω)` に直すのに `Q₀` が `Q` を中心化すること
(`involutions_H_subset_centralizer_Q`) をちょうど使う。予告どおり。

⚠ **重複回避**: `conj_mem_Q0_of_mem_H` (StructureOfH/WielandtOnQ) と
`distinguishedInvolution_mem_Q`/`_mem_Q0` (StructureOfH/TConjugateTriple) は既存
だったので自作分を破棄して既存を import・使用。**Ch. IV の leaf を書くときは
`StructureOfH/**` に同名がないか先に grep すること** (AxiomsCheck が全部 import
するので衝突は build を壊す)。

### (5) 完了 (2026-07-31) + ページ画像で (5)-(7) を確定

⚠ **p.124 を 300dpi で読んで転記を訂正**。以前の pdftotext 由来の記述は誤り:
* **(6) の結論は `a ∈ K` でなく `a ∉ K`**
* (5) の証明中の表示式は pdftotext が丸ごと落としていた:
  `f(ωy) = ω^{a^{-t}} = (f(ω)^{a⁻¹} y)^{a^{-t}} = (f(ω) y^a)^{a⁻¹ a^{-t}}`

**形式化済**:
* `inv_ne_conj_of_not_mem_Q0` — `j` は `Q−Q₀` の `D`-軌道上に不動点を持たない。
  `ω⁻¹ = ω^d` ⟹ `d²` が `ω` を中心化 ⟹ (`|D|` 奇数、既存
  `invertedBy.pow_half_sq` で `d` は `d²` の冪) `d` も中心化 ⟹ `ω² = 1` ⟹ `ω ∈ Q₀`。
* `f_ne_conj_of_not_mem_Q0` — `f` も持たない。`f(ω) = ω^d` に `g` を当てると
  (H3)+(H2) で `g(ω)⁻¹ = g(ω)^e` (`e = d^t h(ω)⁻¹ ∈ D`) — `g(ω)` での `j` 不動点。
* `ne_one_of_f_eq_conj` — (5) 前半 `y ≠ 1`。
* `not_mem_KSet_of_f_eq_conj` — (5) 後半 `a ∉ K`。**対偶を直接取った**:
  `a ∈ K` なら捻れ `a⁻¹a^{-t}` が自明になり式が `f(ωy) = f(ω)y^a` に潰れ、
  (4) が `y = 1` を強制して前半に矛盾。

### 🎯 (6) 完了 — §2 の (1)-(6) が全部揃った (2026-07-31)

`not_mem_KSet_of_f_mul_eq_conj`。`x = s^k`, `u = s^{k⁻¹}` として段 (2) で `f(ωx)` を
評価し、仮説と突き合わせて内側の値について解くと

    f(f(ω)u) = ((f(ω)u) · y')^{a k²},   y' = u y u^{a⁻¹} ∈ Q₀

これはちょうど段 (5) の形 (`ω' = f(ω)u ∈ Q−Q₀`)。よって `a k² ∉ K`。

**着手前の必須調査項目だった「`ak² ∉ K` ⟹ `a ∉ K`」は解決**:
* `commute_of_mem_K` — `K` の元は可換。既存 instance `K_isCyclic` (KCyclic.lean) から。
* `mul_sq_mem_KSet` — `a, k ∈ K ⟹ a k² ∈ K`。`(ak²)^t = a⁻¹k⁻²` と
  `(ak²)⁻¹ = k⁻²a⁻¹` の一致に `a⁻¹`/`k⁻²` の可換性が要り、それが巡回性から出る。

`OddOrder/Peterfalvi/Appendices/Suzuki/PSU3Preliminary.lean` = 554 行, sorry 0。

### 🎯 (7) 完了 — §2 の (1)-(7) が揃った (2026-07-31)

`not_mem_mul_KSet_of_f_mul_eq_conj`。2 つの仮説から `ω'` を消去すると
(`y₁² = 1` を使う)

    f(ωx₂) = (f(ωx₁)^{a₁⁻¹} y₁y₂)^{a₂} = (f(ωx₁)(y₁y₂)^{a₁})^{a₁⁻¹a₂}

でちょうど段 (6) の形。**要点は `(ωx₁)(x₁⁻¹x₂) = ωx₂`** — (6) を
`ω ↦ ωx₁`, `x ↦ x₁⁻¹x₂`, `y ↦ (y₁y₂)^{a₁}`, `a ↦ a₁⁻¹a₂` で適用する。

`PSU3Preliminary.lean` = 606 行, sorry 0。

### 次 = (8) 以降 — ここから標準モデルとの同一視が要る

⚠ **(8) で性格が変わる**。p.124 の (7) の後に書籍は記号を導入する:

> Set `m = |W|` and `n = (q+1)/m = |E*/KW|`. For `ω ∈ Q`, let `ω̄` denote the image
> of `ω` in `Q/Q₀`. If `ω = (α, β)`, then `ω̄` is identified with `α ∈ E`.
> Let `ω₁,…,ω_n ∈ Q − Q₀` be such that the `ω̄_i` comprise a system of
> representatives of the orbits of `(Q/Q₀)^#` under `KW`.

**(8)** `x ∈ Q₀` で `f(ω₁x)‾` が `ω̄_i` の `KW`-軌道に入るものの個数は
`i > 1` なら `m`、`i = 1` なら `m − 1`。
証明: `m_i` をその個数とすると `i > 1` では (7) (`ω = ω₁`, `ω' = ω_i`) から
`m_i ≤ m`、`i = 1` では (7)+(5) から `m₁ ≤ m − 1`。よって
`q = Σ m_i ≤ nm − 1 = q` で全て等号。

⟹ **前提**: `ω = (α, β)` という座標表示 = Ch. III §3 の標準モデル
`Q ⋊ KW ≅ S₁ ⋊ K₁W₁` (0167 の `exists_standardModel`) との同一視。
`m = |W|`, `n = (q+1)/m = |E*/KW|`, `|Q₀| = q`, `Q/Q₀ ≅ E` も要る。

**(8) の設計調査 — 完了 (2026-07-31)**。必要な部品は**ほぼ全部 repo にある**:

* `QuotientFieldModel hyp m` (QuotientKWField.lean:338) がちょうど求める interface:
  - `E` + `card : Nat.card E = (2^m)^2` — つまり `q = 2^m`、`|E| = q²`
  - `coord : Additive (↥Q ⧸ Z(Q)) ≃+ E` — 書籍の `ω ↦ ω̄ ↦ α` そのもの
  - `coord_act` — `KW` 作用が `E` の乗法 `mu kv * ·` になる
  - `mu : K × W →* Eˣ` — 書籍の `K₁W₁ ≤ E^×`
* `exists_standardModel` (ModelAction.lean:731) は `Φ : ↥Q ≃* BilinearTwistedProduct φ`
  と `Θ` を与え、`(Θ kv p).quotient = μ(kv) * p.quotient`。
* `Nat.card ↥hyp.D = Nat.card ↥hyp.V * hyp.KSet.ncard` (CentralizerStructure.lean:160)

**(8) の証明の中身 (書籍の "by (7)" の展開)**: `x, x' ∈ Q₀` が同じ `i` を与えると
(7) を `ω = ω₁`, `ω' = ω_i` で適用して `a, a'` が `K` の**相異なる剰余類**に入る。
よって `m_i ≤ |D : K|`。⚠ **`|D : K| = m = |W|` は Ch. IV の標準仮説 `V = W`
に依存する** (`|D| = |V|·|K|` かつ `W = C_V(K)`; 章の主張自体が「`V = W` なら
`G ≅ PSU(3,q)` または `PGU(3,q)`」)。**`V = W` をまだ仮説に入れていない** —
(8) に着手する前に `Setup`/`hC2` と同じ流儀で明示仮説として導入すること。

**(8) 基盤 = 完了 (2026-07-31)**:
* `card_D_eq_card_V_mul_card_K` — `|D| = |V|·|K|` (既存の一般補題
  `card_eq_card_centralizer_mul_ncard_invertedBy` に渡すだけ; `V = D ⊓ C(t)` と
  `KSet = invertedBy D t` は定義的一致)
* `index_K_subgroupOf_D` — **`|D : K| = |V|`**
* `eq_of_inv_mul_mem_K` — **(7) の数え上げ形**: `a₁⁻¹a₂ ∈ K` ⟹ `x₁ = x₂`。
  `x ↦ a_x K` の単射性で、(8) が直接消費する形。

**(8) の評価は両方完了 (2026-07-31) — どちらも標準モデル不要の純群論**:
* `ncard_le_card_V_of_f_eq_conj` — `#{x ∈ Q₀ | ∃ y ∈ Q₀, ∃ a ∈ D,
  f(ωx) = (ω'y)^a} ≤ |D:K| = |V|` (= 書籍の `m_i ≤ m`)。各 `x` に `a` を選んで
  `D/K` の剰余類へ送る写像が単射 (段 (7))。
* `not_mem_K_of_f_eq_conj_self` — `ω' = ω` なら `a ∉ K` (= `m₁ ≤ m − 1` の中身)。
  書籍が「by (7) and (5)」とだけ書く所の展開: `a ∈ K` なら `a^t = a⁻¹` なので
  `f` を当てると**同じ `a` で対称な** `f(ωy) = (ωx)^a` が出る → 段 (7) が
  `x = y` を強制 (`a⁻¹a = 1 ∈ K`) → `f(ωx) = (ωx)^a` は `f` が `D`-軌道を固定
  することを意味し `f_ne_conj_of_not_mem_Q0` に矛盾。

**翻訳の群論部分も完了 (2026-07-31)**:
* `exists_conj_mul_Q0_iff` — 「`Q₀` を法として `ω'` の `D`-共役に合同」と
  `∃ y ∈ Q₀, ∃ a ∈ D, z = (ω'y)^a` の**同値** (`D` が `Q₀` を正規化することだけ)。
* `K_inf_W_eq_bot` — **`K ∩ W = 1`**。`K` の元は `t` で反転、`W ≤ C_D(t)` の元は
  `t` で中心化 ⟹ `x² = 1` ⟹ `|D|` 奇数より `x = 1`。

**(8) の群論側は全部完了 (2026-07-31)**:
* `ncard_le_card_V_of_f_eq_conj` — `m_i ≤ |D:K| = |V|`
* `not_mem_K_of_f_eq_conj_self` — `i = 1` では像が単位剰余類を外す ⟹ `m₁ ≤ |V|−1`
* `exists_conj_mul_Q0_iff` — 「`Q₀` を法として `D`-共役」⟺ `∃ y ∈ Q₀, ∃ a ∈ D,
  z = (ω'y)^a`
* `K_inf_W_eq_bot` — `K ∩ W = 1`
* `exists_mem_K_mem_W_mul` — **`D = KW`** (`V = W` の下)。これで「`KW`-軌道」=
  「`D`-共役」の同一視が付いた。

**(8) 数値部分の部品調査 = 完了 (2026-07-31)。必要な事実はすべて所在が判明**:

| 必要な事実 | 出所 |
|---|---|
| `\|μ(K)\| = q−1` | `exists_actualKActor_mu_eq` (μ(K×1) が `F^×` を覆う) + `M.mu_K_injective` |
| `\|μ(W)\| = \|W\| = m` | `quotientWHom_injective` (QuotientKWField.lean:134) + `coord_act` |
| `μ(K) ∩ μ(W) = 1` | `mu_K_frobFixed` (⊆`F^×`, 位数 `q−1`) + `mu_W_normOne` (⊆ norm-1, 位数 `q+1`) + **`coprime_two_pow_sub_one_two_pow_add_one`** (本 leaf, 新規) |
| `\|E^×\| = q²−1` | `QuotientFieldModel.card` (`\|E\| = (2^m)^2`) |
| `Σ m_i = \|Q₀\| = q` | `f_mem_sdiff_Q0` + `hQ0card` |

`μ(K) ∩ μ(W) = 1` の群論形も用意済:
**`eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one`** (任意の群で
`x^(2^m−1) = x^(2^m+1) = 1` ⟹ `x = 1`)。`E^×` に適用すればよい。

**`E^×` での実現も完了 (2026-07-31)**:
* `mu_K_pow_two_pow_sub_one` — `μ(k)^{q−1} = 1` (`mu_K_frobFixed` を `Eˣ` へ持ち上げ、
  `q = 1 + (q−1)` で分解して左簡約)
* `mu_K_eq_mu_W_imp_eq_one` — **`μ(K) ∩ μ(W) = 1`**

**基数化の部品も所在確定**: `|F| = 2^m` は
`OddOrder.FiniteField.natCard_frobFixedSubfield` (Algebra/QuadraticFrobenius.lean:189)。
`|F^×| = 2^m − 1` の計算は `ModelIsomorphism.lean:108-115` に `hT` として
インラインで既にある (`Set.ncard_sdiff_singleton_of_mem` 経由) — **export されて
いないので、`|actualKActor| = 2^m − 1` を作るときはそこを参照して同じ形で書く**
(`exists_actualKActor_mu_eq` の全射性 + `M.mu_K_injective` の単射性で全単射)。

**`|K| = q−1` 完了**: `card_actualKActor_eq`。`μ` が `K` を `F^×` の上へ全単射
(`mu_K_injective` + `exists_actualKActor_mu_eq`) と `natCard_frobFixedSubfield`。

⚠ **`μ` の単射性は既存だった (2026-07-31 の訂正)**。`QuotientKWField.lean:504` の
**`mu_injective : Function.Injective M.mu`** が `K × W` 全体で成り立つので、
`|μ(KW)| = |K|·|W| = (q−1)·|W|` は直ちに出る。自作した `mu_W_injective` は
重複だったので撤回した。**Ch. IV の leaf に補題を足す前に
`QuotientKWField` / `ModelIsomorphism` / `StructureOfH/**` を grep すること**
(本 issue で 2 度目 — 1 度目は `conj_mem_Q0_of_mem_H` 等)。

⟹ **`|μ(KW)| = (q−1)·|W|` に必要なものは全部揃っている**
(`card_actualKActor_eq` + 既存 `mu_injective`)。

**指数算術も完了**: `two_pow_sq_sub_one_div` — `(q²−1)/((q−1)m) = (q+1)/m`。
`|W| ∣ q+1` は既存 `isCyclic_W_and_card_dvd_of_orderThree` (WCyclicDivides.lean)。

⟹ **段 (8) の部品は数値側も含めて全部揃った**:

| | |
|---|---|
| `\|E^×\| = q²−1` | `QuotientFieldModel.card` |
| `\|μ(KW)\| = (q−1)·\|W\|` | `card_actualKActor_eq` + 既存 `mu_injective` |
| `\|W\| ∣ q+1` | 既存 `isCyclic_W_and_card_dvd_of_orderThree` |
| `n = (q+1)/\|W\|` | `two_pow_sq_sub_one_div` |
| `m_i ≤ \|W\|`, `m₁ ≤ \|W\|−1` | `ncard_le_card_V_of_f_eq_conj`, `not_mem_K_of_f_eq_conj_self` (+ `V = W`) |
| `Σ m_i = \|Q₀\| = q` | `f_mem_sdiff_Q0` + `hQ0card` |

**挟み込み補題も完了**: `card_fiber_eq_of_card_eq` — `Φ : α → β` の全ファイバーが
`≤ M`、特定の `b₀` が `≤ M−1`、`|α| = |β|·M − 1` なら**全部等号**。
書籍 p.124 の「whence all the inequalities are in fact equalities」そのもの。
完全に一般な補題 (`Finset.sum_eq_sum_iff_of_le` ベース) なので namespace 外。

**残るのは instantiate のみ**。⚠ **設計上の要点 (2026-07-31 に気づいた): 軌道集合を
一般の `MulAction.orbitRel.Quotient` として作る必要はない**。

`KW` は `Q/Q₀ ≅ E` に**スカラー倍**で作用する (`coord_act`) ので、
`(Q/Q₀)^# ≅ E^×` 上の `μ(KW)`-軌道は**部分群 `μ(KW) ≤ E^×` の剰余類そのもの**。
`E^×` は可換なので

    β := Eˣ ⧸ (MonoidHom.range M.mu)

が軌道集合で、これは**商群**なので `Fintype`/`DecidableEq` は mathlib から出る。
`|β| = (MonoidHom.range M.mu).index` で、`|Eˣ| = q²−1` (`Fintype.card_units`) と
`|range μ| = |K×W| = (q−1)|W|` (既存 `mu_injective` + `card_actualKActor_eq`) から
`|β| = (q+1)/|W| = n` ✓。

`Φ : ↥Q₀ → β` は `x ↦ ⟦coord(f(ω₁x) の Q/Q₀ 像) を単位として⟧`。
`f(ω₁x) ∈ Q−Q₀` (`f_mem_sdiff_Q0`) なので `coord` の値は非零 ⟹ 単位 ✓。

**(ii) は完了**: `index_range_mu` — `(MonoidHom.range M.mu).index = (q+1)/|W|`。
`MonoidHom.ofInjective` (既存 `mu_injective`) + `card_actualKActor_eq` +
`Fintype.card_units` + `Subgroup.index_mul_card` + `two_pow_sq_sub_one_div`。

**(i) の第一歩も完了**: `coord_ne_zero_of_not_mem_Q0` — `z ∈ Q−Q₀` なら
`M.coord ⟦z⟧ ≠ 0` (`coord` が加法同型 + `Z(Q) = Q₀`)。これで
`f(ω₁x)` の座標を**単位**として扱える。

**(i) 完了**: `orbitOfF : ↥Q₀ → M.Eˣ ⧸ (MonoidHom.range M.mu)` —
`x ↦ f(ω x) の座標の μ(KW)-剰余類`。well-defined は
`mul_mem_sdiff_Q0` → `f_mem_sdiff_Q0` → `coord_ne_zero_of_not_mem_Q0` → `Units.mk0`。

### 残る 1 ステップ = ファイバーの翻訳 (設計を確定した)

**要点の補題**:

    Φ x = Φ x'  ⟺  ∃ a ∈ D, ∃ y ∈ Q₀, f(ω x) = a⁻¹ · (f(ω x') · y) · a

* **⟸ / ⟹ の中身**: 同じ剰余類 ⟺ `coord(f(ωx)) = μ(kv) · coord(f(ωx'))`。
  `coord_act` によりこれは `f(ωx) ≡ quotientKWHom kv (f(ωx')) (mod Q₀)`。
  `KW` の `Q` への作用は `conjQHom` すなわち `D` の元による共役なので
  (`D = KW` = `exists_mem_K_mem_W_mul`)、`f(ωx) ≡ a⁻¹ f(ωx') a (mod Q₀)`。
  最後に `exists_conj_mul_Q0_iff` で目的の形へ。
* ✅ **商と `Q` の作用の突き合わせは既にある**: `quotientKWHom_mk` (:219) が
  `quotientKWHom kv ⟦x⟧ = ⟦conjQHom kv x⟧` を **`rfl` かつ `@[simp]`** で与える。
* ✅ **`conjQHom kv` の同定も完了**: `exists_mem_D_conjQHom` —
  `∃ d ∈ D, ∀ x, conjQHom kv x = d x d⁻¹`。`actualKActor = conjQByK.range` かつ
  `conjQByK` / `conjQByW` は**定義がそのまま共役**なので、合成は `k·v` (∈ `D`)
  による共役。

⟹ **翻訳に要る部品はすべて揃った**。導出は手で追い切ってあるので以下をそのまま
Lean に落とせばよい (`u_x := Units.mk0 (coord (f(ω x))) …` と書く):

1. `Φ x = Φ x'` ⟺ `u_x⁻¹ * u_{x'} ∈ MonoidHom.range M.mu` (`QuotientGroup.eq`)
   ⟺ `∃ kv, u_{x'} = u_x * μ kv`。
   ✅ **step 1-4 は `exists_conjQHom_quotient_eq_of_coset_eq` として形式化済**。
2. `E` に降ろす: `coord (f(ω x')) = μ kv * coord (f(ω x))` (`Eˣ` は可換)。
3. `coord_act` で右辺 = `coord (quotientKWHom kv ⟦f(ω x)⟧)`。
4. `coord` は同型なので `⟦f(ω x')⟧ = quotientKWHom kv ⟦f(ω x)⟧`
   `= ⟦conjQHom kv (f(ω x))⟧` (`quotientKWHom_mk`, rfl)。
5. `exists_mem_D_conjQHom` で `conjQHom kv (f(ωx)) = d · f(ωx) · d⁻¹` (`d ∈ D`)。✅
6. 商での等式 ⟹ `f(ω x') = d · f(ω x) · d⁻¹ · w` (`w ∈ Z(Q) = Q₀`)。
   ✅ **`exists_mem_Q0_mul_of_quotient_eq` として形式化済**。
7. `a := d⁻¹ ∈ D` とおくと `a⁻¹ · f(ωx) · a = d · f(ωx) · d⁻¹` なので、これは
   `exists_conj_mul_Q0_iff` の左辺の形。よって
   `∃ y ∈ Q₀, ∃ a ∈ D, f(ω x') = (f(ω x) · y)^a` ✓

🎯 **翻訳 7 ステップは全部形式化済 (2026-07-31)**。結合済の到達点 =
**`exists_conj_of_coset_eq`**: 座標が同じ剰余類 ⟹ `z' = (z·y)^a`
(`y ∈ Q₀`, `a ∈ D`) — **これは `ncard_le_card_V_of_f_eq_conj` と
`not_mem_K_of_f_eq_conj_self` の仮説の形そのもの**。

⟹ **段 (8) の残りは `card_fiber_eq_of_card_eq` への流し込みのみ**:
* ✅ **`ncard_fiber_orbitOfF_le` として形式化済** — 各ファイバーは `≤ |V|`
  (`V = W` の下で書籍の `m_i ≤ m`)。空の場合と代表を取る場合で分け、
  `exists_conj_of_coset_eq` + `ncard_le_card_V_of_f_eq_conj` + `Subtype.val` の単射性。
  `fUnit_val` を `rfl` にしておいたので `hu`/`hu'` は `rfl` で埋まった。
* `ω` 自身の類では `not_mem_K_of_f_eq_conj_self` が単位剰余類を除外 ⟹ `≤ |W|−1`。
* `|α| = |Q₀| = q` (`hQ0card`)、`|β| = index = (q+1)/|W|` (`index_range_mu`)。

### 🎯🎯 段 (8) 完成 (2026-07-31)

**`stepEight`** (`PSU3OrbitCount.lean`)。`Φ = orbitOfF` の各ファイバーが
ちょうど `|W|` 個、区別されたものだけ `|W| − 1` 個。
書籍の「whence all the inequalities are in fact equalities」そのもの。

組み立ては 5 点を `card_fiber_eq_of_card_eq` に渡すだけだった:
ファイバー評価 2 本 (+ `V = W` で `|V| → |W|`)、`|Q₀| = q`、
`|E^× ⧸ μ(KW)| = (q+1)/|W|`、`|W| ∣ q+1` から `q = ((q+1)/|W|)·|W| − 1`。

⚠ 挟み込み補題を先に `Set.ncard` 版へ書き直しておいたので変換が不要だった
(そうしなければ使用側で毎回 `Finset.card` 変換が要った)。

**⟹ §2 Preliminary Calculation の (1)-(8) 完了。**

### 次 = (9) (p.124 末〜125) — ページ画像で確定済

`ζ` = `W` の生成元。(C2) より `ζ ≠ 1`。

**(9)** すべての `i` (`1 ≤ i ≤ n`) に対し `ω'_i ∈ Q − Q₀` と `y_i ∈ Q₀^#` が存在して
`ω̄'_i` が `ω̄_i` の `KW`-軌道に入り、かつ **`f(ω'_i) = (ω'_i y_i)^ζ`**。

**証明** (p.124 末): `ω` を `ω_i` の一つとする。(5)(7)(8) により
`x, z ∈ Q₀` と `k ∈ K` が存在して **`f(ωx) = (ωz)^{kζ}`**。
`a ∈ K` なら

    f((ωx)^a) = f(ωx)^{a⁻¹} = (ωz)^{a⁻¹kζ} = ((ωx)^a (xz)^a)^{a⁻²kζ}

(以降は p.125 — 未読)

⚠ **`kζ` の出所 (段 (8) の使い方)**: 段 (8) で区別されたファイバーは
ちょうど `|W| − 1` 個。一方 `x ↦ a_x K` は単射 (段 (7)) で、像は
単位剰余類 `K` を外す (`not_mem_K_of_f_eq_conj_self`)。`D = KW` なので
`D/K` の剰余類は `Kw` (`w ∈ W`) で全部で `|W|` 個 ⟹
**像はちょうど `{Kw : w ≠ 1}` 全体**。`ζ ≠ 1` なので `Kζ` も像に入り、
対応する `x` が `a = kζ` を与える。

⟹ **次の形式化タスク**: 「段 (8) の単射が `(D/K) ∖ {1}` への**全単射**になる」
(単射 + 基数一致 `|W| − 1` から)。これが (9) の入口。

⚠ **要リファクタ**: 現状その単射は `ncard_le_card_V_sub_one_of_f_eq_conj_self` /
`ncard_fiber_orbitOfF_base_le` の**証明の中に `choose!` で埋め込まれている**ので、
全射性を言うには外に出す必要がある。手順:
1. ✅ **`exists_witness_not_mem_K` で存在 + `a ∉ K` を 1 本にまとめた** (完了)。
   残りは `choose!` された剰余類写像の全射性。

   ⚠ **設計上の要点 (2026-07-31)**: 全射性には `stepEight` の**厳密な個数**が要る。
   `stepEight` は `{x : ↥Q₀ | Φ x = c₀}.ncard = |W| − 1` を与え、
   `ncard_fiber_orbitOfF_base_le` の証明はその像が集合
   `S = {z ∈ Q₀ | ∃ y ∈ Q₀, ∃ a ∈ D, f(ωz) = (ωy)^a}` に含まれることを示し、
   `ncard_le_card_V_sub_one_of_f_eq_conj_self` は `S.ncard ≤ |V| − 1`。
   `|V| = |W|` なので **両者とも ちょうど `|W| − 1`** ⟹ 包含は等号 ⟹
   `S` 上の剰余類写像 (単射・像は `1` を外す・`|S| = |D/K| − 1`) は
   `(D/K) ∖ {1}` への**全単射**。
   ⟸ この補題は `stepEight` を使うので **`PSU3OrbitCount` 側**に置くこと。
2. ✅ **`ncard_eq_card_W_sub_one_of_f_eq_conj_self` で `|S| = |W| − 1` (厳密) を
   証明済** (段 (8) の厳密個数 + 既存の `≤`)。

   **残り = 全射性の読み取り**。手順が確定した:
   * `S` 上の剰余類写像 `Ψ z = ⟦A' z⟧ ∈ ↥D ⧸ K.subgroupOf D` を作る
     (`choose!` — `ncard_le_card_V_sub_one_of_f_eq_conj_self` と同じ定型 ~15 行)
   * `Ψ '' S ⊆ univ ∖ {1}` (`not_mem_K_of_f_eq_conj_self`)
   * `(Ψ '' S).ncard = S.ncard = |W| − 1` (`Set.ncard_image_of_injOn` + 上記)
   * `(univ ∖ {1}).ncard = |D:K| − 1 = |W| − 1`
   * ⟹ **`Set.eq_of_subset_of_ncard_le`** で `Ψ '' S = univ ∖ {1}` ✓
     ⟸ **この補題名が最後の未確定要素だった (確認済: Mathlib/Data/Set/Card.lean:875)**
   * `d ∈ D ∖ K` なら `⟦d⟧ ≠ 1` なので像に入る ⟹ 対応する `z ∈ S` が取れる
3. `ζ ≠ 1` (C2) より `ζK ∈ 像` ⟹ 対応する `x` が `a = kζ` を与える
   (`K` と `W` は可換 — `W = C_V(K)` — なので `Kζ = ζK`、左右の剰余類は一致)。

⟹ そのあと (9) 本体 — **p.125 冒頭で確定済**:

> Taking `a ∈ K` to be such that `a² = k` and setting `ω' = (ωx)^a` and
> `y = (xz)^a`, we see that `f(ω') = (ω'y)^ζ`. By (5), `y ≠ 1`.

`f((ωx)^a) = f(ωx)^{a⁻¹} = (ωz)^{a⁻¹kζ} = ((ωx)^a(xz)^a)^{a⁻²kζ}` で、
`a² = k` より **`a⁻²k = 1`** ⟹ 指数が `ζ` に潰れる。
⚠ `k ∈ K` の平方根 `a ∈ K` の存在は **`|K|` が奇数** (`K ≤ D`, `|D|` 奇数) から。
既存 `invertedBy.pow_half_sq` (`(a²)^{(|X|+1)/2} = a`) がそのまま使える。

### (9) の組み立て — 手で追い切った (2026-07-31)

部品は全部揃った: `exists_witness_coset_eq` (入口) と
`exists_sq_eq_of_mem_K` (締め)。あとは以下を Lean に落とすだけ:

1. `exists_witness_coset_eq` を `d := ζ` で適用 ⟹ `z, b ∈ Q₀`, `a ∈ D` で
   `a⁻¹ζ ∈ K` かつ `f(ωz) = (ωb)^a`。
   `a⁻¹ζ ∈ K` すなわち `a ∈ ζK`。`K` と `W` は可換 (`W = C_V(K)`) なので
   **`a = kζ` (`k ∈ K`) と書ける**。
2. `exists_sq_eq_of_mem_K` で `c ∈ K`, `c² = k` を取る。
3. `ω' := (ω z)^c`、`y := (z b)^c` とおく。
4. **計算**: (H3) を `c ∈ K` (⟹ `c^t = c⁻¹`) で使うと
   `f(ω') = f((ωz)^c) = f(ωz)^{c⁻¹} = ((ωb))^{c⁻¹kζ}`。
   `ωb = (ωz)(zb)` (`z² = 1`, `z ∈ Q₀`) と書き直して conjugation を
   ばらすと `((ωz)^c (zb)^c)^{c⁻²kζ}`。**`c² = k` より `c⁻²k = 1`** ⟹
   `= (ω' y)^ζ` ✓
5. `y ≠ 1` は (5) (`ne_one_of_f_eq_conj`) から。
6. `ω' ∈ Q − Q₀` は `mul_mem_sdiff_Q0` + `D`-共役が `Q₀` を保つことから。

⚠ 4 の conjugation の付け替えが唯一の手数。`z² = 1` (`Q₀` は指数 2) と
`(u^c)^{c⁻²kζ} = u^{c⁻¹kζ}` を使う。

### ⚠ (9) の後の「正規化」— §2 の残りの前提

> **We will assume from here on in §2** that the elements `ω_i` have been chosen in
> such a way that `f(ω_i) = (ω_i y_i)^ζ`, `y_i ∈ Q₀^#`.
> In (10) to (18), we let `ω` denote one of the elements `ω_i`; we set
> `y_i = y = (0, α)`.

⟹ (10) 以降は**この正規化された代表系**が前提。形式化では
「(9) の結論を満たす代表系を取る」を仮説として持ち回るのが自然。
`y = (0, α)` は `BilinearTwistedProduct` 座標 ⟹ **ここからモデル座標が本格的に要る**。

### 🎯🎯 段 (9) 完成 (2026-07-31) — §2 (1)-(9) 完了

`stepNine` (`PSU3OrbitCount.lean`)。`ζ ∈ W`, `ζ ≠ 1` に対し
`∃ ω' ∈ Q−Q₀, ∃ y ∈ Q₀^#, f(ω') = (ω'y)^ζ`。

部品 (すべて本セッションで証明):
`exists_witness_coset_eq` (入口) / `commute_of_mem_W_of_mem_K` (剰余類の読み替え)
/ `exists_sq_eq_of_mem_K` (平方根) / `f_conj_collapse` (指数潰し)
/ `ne_one_of_f_eq_conj` (段 (5), `y ≠ 1`)。

### (10) (p.125) — 確定済

`a, b ∈ K` が `b^{1+θ} = α + a^{-(1+θ)}` を満たすなら

    f(ω s^a) = (f(ω s^b) s^a)^{ζ a⁻²}

証明: (2) より
`f(ωs^a) = f(f(ω)s^{a⁻¹})^{a⁻²}s^{a⁻¹} = f(ωys^{a⁻¹})^{ζa⁻²}s^{a⁻¹}
= (f(ωs^b)s^a)^{ζa⁻²}`。

⚠ `θ` = モデルの Frobenius (`exists_standardModel` の `θ : E ≃ₐ[ZMod 2] E`)、
`α` = `y` の `E`-座標。**(10) 以降は 0167 の標準モデルの座標計算**になる。

その後: `τ` = `u ↦ u^{1+θ} : F^× → F^×` の逆写像 (`θ` が奇数位数ゆえ全単射)。

⚠ **「`θ` が奇数位数ゆえ全単射」の中身 (2026-07-31)**。書籍は 1 節で済ませている。
最初に群環 `ℤ[θ]` で `(1+θ)·(交代和) = 2` という論法を書いたが、
**もっと簡単な論法がある** (こちらを採る):

`N : F^× → F^×`, `N(u) = u · θ(u)` は**準同型** (`frobNorm_mul`)。核が自明を示せば、
有限集合上の自己準同型なので全単射。

    u ∈ ker N  ⟹  θ(u) = u⁻¹
               ⟹  θ²(u) = θ(u⁻¹) = (u⁻¹)⁻¹ = u      (θ² が u を固定)
               ⟹  θ も u を固定                        (θ の位数 d が奇数なので
                                                         θ = (θ²)^{(d+1)/2})
               ⟹  u⁻¹ = θ(u) = u  ⟹  u² = 1
               ⟹  u = 1                                (|F^×| = q−1 が奇数)

⚠ **`inv_ne_conj_of_not_mem_Q0` と同じ形の論法** (「`d²` が中心化 ⟹ `d` が中心化」)。
奇数位数から「2 乗が全単射」を使う定型。`Finset.prod` の telescoping 帰納法は不要。

**必要な入力**: `θ` の位数が奇数であること。0167 の `θ` は `E` の Frobenius 冪で、
`F` 上の作用の位数は…要確認 (`exists_standardModel` の `θ` の性質を見る)。

### 🎯 段 (10) 完成 (2026-07-31) — `stepTen` (`PSU3Preliminary.lean`)

書籍の "By (2)," 1 行を展開。**仮説をモデル座標でなく群論的に取った**ので
モデル非依存側に置けた:

    f(ω) = (ωy)^ζ,  a,b ∈ K,  y·s^{a⁻¹} = s^b   ⟹   f(ω s^a) = (f(ω s^b) s^a)^{ζa⁻²}

論法: 段 (2) → `f(ω) = (ωy)^ζ` + `ζ` が `Q₀` を中心化 → (H3) で `ζ` が `f` を
通り抜ける (`ζ ∈ V` ゆえ `ζ^t = ζ`) → `ζ` が `a`, `s` と可換なことによる並べ替え。

### 📌 Ch. III §3 の作用公式 (p.119-121 で確定、2026-07-31)

段 (10) 以降の座標計算の基礎。**書籍 p.119-120 から直接読んだ**:

* `K₁W₁ ≤ E^×`、`K₁ = F^×`、`W₁ ≤ {x ∈ E^× | x^{1+q} = 1}` (非自明)。
* `σ` = `E` の自己同型で `σ|_F = θ`、かつ **`x^σ = x^{-1}` for `x ∈ W₁`**。
* **`S₁` 上の `K₁W₁` の作用: `(x,y)^a = (a x, a^{1+σ} y)`** (`a ∈ K₁W₁`)。
* 同型は **`s ↦ (0,1)`**、`K` を `K₁` へ送る。

⟹ 帰結 2 つ:

1. **`ζ ∈ W` は `Q₀` を中心化する** — `ζ^σ = ζ^{-1}` なので `ζ^{1+σ} = 1`。
   repo 側では既に `W_centralizes_Q0` (`KCyclic.lean:122`) として独立に在る ✓
2. **`a ∈ K` の `Q₀` 上の作用は `c ↦ a^{1+θ} c`** (`σ|_F = θ`)。
   `|F^×| = q-1` 上では `a^{1+θ} = a^{1+2^j}` = **整数冪**なので、repo の
   `exists_mulEquiv_bookCocycle` が持つ `μ(k,1)^d` (`d : ℤ`) と整合する。

⟹ **段 (10) の座標版への翻訳** = 次の 3 点があれば機械的:
   (a) `ι' : Q₀ ≃+ F` (`CenterFieldExponent` に有り)、
   (b) `K` 作用 `ι'(centerKHom k z) = μ(k,1)^d · ι'(z)` (`hequiv'` に有り)、
   (c) `ι'(s) = 1` — 「`s` を `(0,1)` へ送る」正規化。**repo に無い**
       (model 層に `distinguishedInvolution` は (C2) の `orderOf (s·t) = 3` としてしか
       現れない)。

⚠⚠ **(c) は不要だった (2026-07-31)**。座標版は正規化なしで書ける:

    y·s^{a⁻¹} = s^b   ⟺   ι'(y) + μ(a)^{-d}·ι'(s) = μ(b)^d·ι'(s)

`s ≠ 1` ゆえ `ι'(s) ≠ 0` なので両辺を `ι'(s)` で割れば、**`α := ι'(y)/ι'(s)`** と
おくだけで書籍の `b^{1+θ} = α + a^{-(1+θ)}` そのものになる。書籍の `α` は
「正規化されたモデルでの `y` の座標」であり、それは `ι'(y)/ι'(s)` に他ならない。

⟹ `ModelIsomorphism.lean` の巨大な存在命題に `ι'(s) = 1` を足す (= `ι'` を
`ι'(s)⁻¹` 倍にスケールし直して K 作用・双加法性・非等方性の保存を確かめる) という
**1 session 級の infra 作業が丸ごと不要**。座標橋は `ι'`/`centerKHom`/`μ` の
向きの規約を合わせるだけの機械作業になる。

⟸ 揃っている部品: `Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q`
   (`ActualCenter.lean:145`、PSU3OrbitCount では仮説 `hZ` として持ち回り済)。

### 座標橋の仕様を確定 (2026-07-31) — 規約を実測で照合済

repo 側の向きの規約 (すべて実測):

| repo | 内容 |
|---|---|
| `conjQByK_apply_val` | `(conjQByK k x : G) = k · x · k⁻¹` |
| `centerKHom_apply_val` | `(centerKHom k z : Q) = actualKActor.subtype k (z : Q)` |
| `hequiv'` (`exists_mulEquiv_bookCocycle`) | `ι'(centerKHom k z) = μ(k,1)^d · ι'(z)` (`d : ℤ`) |
| `coord_act` (`QuotientFieldModel`) | `coord(quotientKWHom kv y) = μ(kv) · coord(y)` |
| `ActualCenter.lean:145` | `center Q = Q0.subgroupOf Q` |

⟹ `A := μ(conjQByK a, 1)`, `B := μ(conjQByK b, 1)` とおくと

    a·s·a⁻¹ = s^{a⁻¹}  ↦  ι'(·) = A^{d}·ι'(s)
    b⁻¹·s·b = s^{b}    ↦  ι'(·) = B^{-d}·ι'(s)

したがって

    y·s^{a⁻¹} = s^b   ⟺   ι'(y) + A^{d}·ι'(s) = B^{-d}·ι'(s)
                      ⟺   α + A^{d} = B^{-d}       (`α := ι'(y)/ι'(s)`, `ι'(s) ≠ 0`)

書籍は `b^{1+θ} = α + a^{-(1+θ)}`。⟹ **書籍の `x ↦ x^{1+θ}` = repo の
`x ↦ μ(conjQByK x, 1)^{-d}`** で整合 ✓ (符号は `d` が吸収する)。

⚠ 残る作業は**強い数学でなく coercion の配管**: `Additive`/`Subtype`/`subgroupOf`/
`frobFixedSubfield` の往復。`ι'` は `Additive ↥(center Q) ≃+ ↥F` なので
`Q0 → center Q` の持ち上げ (`hZ` 経由) と `ofMul` の出し入れが要る。
`ι'(s) ≠ 0` は `s ≠ 1` + `ι'` が同型であることから。

### 次 — 段 (11) (p.125)

`u_i, v_i ∈ F`, `d_i ∈ KW` を `f(ω(0,u_i)) = (ω(0,v_i))^{d_i}` を満たすよう帰納的に:

    u₁ = 0,  v₁ = α,  d₁ = ζ
    u_{i+1} = 1/(α + u_i),  v_{i+1} = v_i + u_{i+1} d_i^{-(1+σ)},  d_{i+1} = d_i ζ u_{i+1}^{-2τ}

`u_i = α` になった時点で停止 (標数 2 ゆえ `α + u_i = 0 ⟺ u_i = α`、
これが `u_{i+1}` の well-definedness)。`τ` は本セッションで用意済 ✓

その後 (12): `β + β⁻¹ = α` (`X² + αX + 1` の根)、`β ∈ E`、`β ∉ F ⟹ β⁻¹ = β^q`。
`((0,1),(1,α))` の対角化と `i` 乗公式。**モデル軽め**で自己完結するので、
(11) の座標整備が重いなら (12) を先に切り出す手もある。

### p.126 を読んだ — (13)-(17) の構造 (2026-07-31)

* **(13)** `u_i = (β^{i-1} + β^{-i+1})/(β^i + β^{-i})` — **閉じた式**
* **(14)** `d_i = ζ^i ((β^i + β^{-i})/α)^{2τ}` — **閉じた式** ((11) から i の帰納法)
* **(15)** 列は `i = m-1` まで定義され `u_{m-1} = α = β^{m-1} + β^{-m+1}`。
  `f(ω(0,u))` が `ω̄` の `KW` 軌道に入る `u ∈ F` は `u_i` のいずれか (証明は (8) を使う)
* **(16)** `β` は `W` の生成元、特に `β^σ = β⁻¹`
* **(17)** `1 ≤ i ≤ m-1` で `f(ω(0,u_i)) = (ω(0, u_i + α))^{d_i}` — すなわち **`v_i = u_i + α`**

⟹ **形式化方針**: (13)/(14) が閉じた式なので、**部分再帰でなく閉じた式で `u_i`, `d_i` を
定義し、(11) の漸化式を満たすことを証明する**方が Lean では圧倒的に楽。停止条件つき
部分列を作る必要がない。`v_i := u_i + α` は (17) から。

### 🎯 段 (12) の証明戦略 — 数え上げで一発 (2026-07-31)

`α ∈ F` に対し `β + β⁻¹ = α` なる `β ∈ E^×` が要る (= `X² + αX + 1` の根)。
**Artin-Schreier / トレース / 体の拡大は一切不要**。以下の数え上げで
(12) の**両方の主張が同時に**出る:

`S := F^× ∪ N`, `N := {x ∈ E^× | x^{q+1} = 1}` (ノルム 1 部分群) とおく。

1. `x ∈ S ⟹ x + x⁻¹ ∈ F`。`x^q = x` なら自明、`x^{q+1} = 1` なら
   `x + x⁻¹ = x + x^q = Tr_{E/F}(x) ∈ F` ✓
2. `ψ(x) := x + x⁻¹` の**繊維は `{x, x⁻¹}` のみ** ⟸ `add_inv_eq_add_inv_iff`
   (本セッションで証明済 ✓)
3. `ψ(x) = 0 ⟺ x² = 1 ⟺ x = 1` (標数 2) なので `0` の上の繊維は `{1}` の 1 点
4. `|F^×| = q-1` (`natCard_frobFixedSubfield` ✓)、**`|N| ≥ q+1`** は
   `E^×` が位数 `q²-1` の巡回群ゆえ生成元 `g` に対し `⟨g^{q-1}⟩` が位数 `q+1`
   (⚠ **下界だけでよい** ので mathlib の exact-count 補題を探す必要がない)
5. `F^× ∩ N = {1}` ⟸ `eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one` (既存 ✓)
   ⟹ `|S| ≥ (q-1) + (q+1) - 1 = 2q - 1`
6. 繊維の大きさ ≤ 2、`0` の上だけ 1 ⟹ `|ψ(S)| ≥ 1 + (|S|-1)/2 ≥ q`
7. `ψ(S) ⊆ F` かつ `|F| = q` ⟹ **`ψ(S) = F`** ✓ (`Set.eq_of_subset_of_ncard_le`)

⟹ 任意の `α ∈ F` に `β ∈ S` が取れ、`β ∈ F^×` (= `β^q = β`) か
`β ∈ N` (= `β⁻¹ = β^q`) のいずれか — これが (12) の
「`β ∈ E` and if `β ∉ F` then `β⁻¹ = β^q`」そのもの ✓

⚠ **部品の状況 (2026-07-31 更新)**:

| 部品 | 状態 |
|---|---|
| `add_inv_eq_add_inv_iff` (繊維 = `{x,x⁻¹}`) | ✓ 証明済 |
| `card_rootsOfUnity_ge` (`\|N\| ≥ q+1`) | ✓ 証明済 (本セッション) |
| `natCard_frobFixedSubfield` (`\|F\| = q`) | ✓ 既存 |
| `eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one` (`F^× ∩ N = 1`) | ✓ 既存 |
| 組み立て | ← **残り** |

**組み立てに使う mathlib API (実測で確認済)**:

* `Finset.card_le_mul_card_image (s) (n) (hn : ∀ b ∈ s.image f, #{a ∈ s \| f a = b} ≤ n)`
  `: #s ≤ n * #(s.image f)` — `n := 2` で使う。⚠ 姉妹補題
  `card_le_mul_card_image_of_maps_to` (`t` を陽に取る版) は**使えない**:
  `#S ≤ 2·#F` が出るだけで全射性が出ない。像を `t` にする方を使うこと。
* `Finset.eq_of_subset_of_card_le : s ⊆ t → #t ≤ #s → s = t`
* `mem_frobFixedSubfield : x ∈ frobFixedSubfield E p n ↔ x ^ p ^ n = x` (simp)
* `Fintype.card_subtype` + `Equiv.subtypeEquivRight` で
  `#{x ∈ univ \| x^q = x}` ↔ `Nat.card ↥(frobFixedSubfield E 2 m)`
* `card_rootsOfUnity` は `[NeZero k]` を要求 (引数順は `(k := ) (R := )` で明示)

**残りの手順**: `Sfin := {x ≠ 0 ∧ (x^q = x ∨ x^{q+1} = 1)}` を作り、
(a) `#Sfin ≥ 2q-1` (`F^×` と `N` の合併、交わりは `{1}`)、
(b) `ψ(Sfin) ⊆ Ffin`、(c) 繊維 ≤ 2 ⟹ `#Sfin ≤ 2·#(image)` ⟹ `#image ≥ q`
(∵ `2(q-1) = 2q-2 < 2q-1`)、(d) `eq_of_subset_of_card_le` で `image = Ffin`。

### 📊 2026-07-31 セッション終盤の状態 (§2 の到達点)

| 段 | 状態 | 主定理 |
|---|---|---|
| §1 全体 | ✅ | `RankOneBNPair.lean` (784 行, sorry-free) |
| (A1)-(A3) → Setup 橋 | ✅ | `Hypothesis.rankOneSetup` |
| (1)-(9) | ✅ | `PSU3Preliminary` + `PSU3OrbitCount` |
| **(10)** | ✅ 群論版+座標版 | `stepTen` / `stepTen_exists` / `stepTen_base` / `stepTen_coord` |
| **(11)** | 🔶 帰納段のみ | `stepEleven_step` |
| **(12)** | ✅ | `exists_add_inv_eq` |
| **(13)** | ✅ | `betaRatio_succ` (+ `betaSum_eq_zero_iff`) |
| **(14)** | ✅ 帰納段 | `betaScale_succ` (+ `frobNormEquiv` = τ) |
| **(15)** | 🔶 結論 2 本を導出済 | `stepFifteen_length` (長さ `m₁+1=m`) / `eq_one_of_kPart_eq_one` (`c_{m₁}=α`) |
| **(16)** | 🔶 体論的核 | `pow_eq_one_of_betaSum_eq` |
| **(17)** | ✅ | `betaSum_mul_betaSum_add_two` / `betaRatio_div_betaRatio` |
| **(18)** | 🔶 部品 4 本 | `betaSum_fixed_of_inv` / `frobNormEquiv_symm_sq_of_fixed` / `eq_pow_mul_prod_of_rec` / `prod_betaRatio` |
| **(19)** | 🔶 入口 | `exists_inv_frobNorm_eq_of_ne` |
| **(20)** | 🔶 結論 | `eq_add_of_add_char_two` (`α₁ = α₂ = x₁+x₂`) |
| 座標橋 | ✅ | `PSU3CenterCoordinate.lean` |
| §3 以降 (pp.129-134) | ❌ 未読 (p.129/130 は画像保存済) | — |

**ファイル構成 (本セッションで整理)**:
* `PSU3Preliminary.lean` (1256 行) — §2 の群論 (1)-(7), (10), (11)
* `PSU3OrbitCount.lean` (656 行) — (8)/(9) の軌道数え上げ (モデル依存)
* `PSU3FieldArithmetic.lean` (~760 行) — `E/F` の算術 (12)-(16) (モデル非依存)
* `PSU3CenterCoordinate.lean` (~210 行) — 座標橋
* `RankOneSetup.lean` (122 行) — (A1)-(A3) → Setup

**次の一手 (2026-07-31 終盤時点)**: (19) の (a)(b) 本体。段 (2) を使う等式の連鎖で、
`ω₁(0,x)` 記法 (= `ω` に `Q₀` の元を掛ける) の座標インタフェースが要る。
座標橋 (`centerCoord`) は完成しているので、あとは `f` の値と `KW` 軌道の対応。

**旧・次の一手 (完了)**: (15) の組み立て。部品は 3 本とも揃っている:
1. `d_{m₁} = ζ⁻¹` を `ζ^{m₁+1} · (c_{m₁}/α)^{2τ} = 1` へ ((14) の閉じた式から)
2. `eq_one_of_mul_eq_one_of_mem_K_of_mem_W` で両因子を 1 に
3. `eq_one_of_frobNormEquiv_symm_sq_eq_one` で `c_{m₁} = α`、
   `eq_of_pow_succ_eq_one_of_le` で `m₁ = m-1`
⚠ 残るのは `d_i ∈ KW` の同定 (μ 経由) と `m₁ ≤ m-1` (段 (5) との矛盾)。
前者は座標橋と同種の配管、後者は段 (5) `not_mem_KSet_of_f_eq_conj` を使う。

⚠ **本セッションで 2 回 forward reference をやらかした** (定義より前に補題を置く)。
Lean に前方参照は無い — 新補題は依存先の**後ろ**に置く。

### p.127-128 を読了 — (18)-(20) の構造 (2026-07-31)

ページ画像 p.127-130 を `references/peterfalvi/pages/` に保存済。

* **(18)** `(h(ω)ζ⁻¹)^m = 1`。
  入口が `u_i^θ = u_i` (⟸ (16) の `β^σ = β⁻¹` で `c_j` が固定) と
  `u_i^{2τ} = u_i` (⟸ θ-固定元では `u^{1+θ}` は 2 乗)。
  本体は漸化式 `h(ω(0,u_i)) = (h(ω)ζ⁻¹)h(ω(0,u_{i-1}))(ζu_i)` の展開 +
  telescoping 積 `u₂⋯u_i = c₁/c_i`。最後に (H4) で
  `h(ω(0,α)) = ζh(ω)⁻¹ζ⁻¹` と突き合わせる。
* **(19)** `n ≥ 2` を仮定し `ω₁, ω₂` から 2 組の列 `(u_i)`/`(u'_i)` を走らせる。
  (a)(b) は互いに `ω₁ ↔ ω₂` を入れ替えた形。
* **(20)** **`α₁ = α₂`**、および `f(ω₁(0,x)) = (ω₂(0,x+α))^{d(x)}`。
  証明の骨は (∗)(∗∗)(∗∗∗) の 3 本の等式で、**(∗∗∗) の `i=1` と `i=m-1` から
  `x₁ = x₂ + α₂` と `x₁ + α₁ = x₂` が出て、標数 2 で `α₁ = α₂ = x₁ + x₂`**。
  ⟹ `u'_i = u_i`, `v'_i = v_i`, `d'_i = d_i` (2 組の列が一致)。

⚠ §2 は (18) で終わらず (19)(20) まで続く。(19)(20) は
**`n ≥ 2` の下での 2 組の列の比較**で、`f` の値の軌道を突き合わせる。

## 2026-08-01: (19) 完成 / (20) の核 / (11) の実体化 / (15) の長さ

### 🎯 段 (19)(a)(b) 完成 — `PSU3PairComparison.lean` (新 leaf)

⚠ **座標は要らなかった**。書籍の等式連鎖は (H3) + 段 (2) + 不変式だけで閉じ、
`u, v, d` に所属仮説すら不要 (`d ∈ KW` も不要)。

* `stepNineteen` — **(19)(a)**: `f(ω₂ z₂ · s^{ak⁻¹}) = (ω₁ v · s^{ad⁻¹})^{d a⁻² k}`。
* `f_conj_swap` (`f x = y^e` ⟹ `f y = x^{e^{-t}}`, `e ∈ D`) / `f_swap_of_pair`
  (`e = k ∈ K` の場合) — (19)(b) は (a) を `ω₁ ↔ ω₂` で呼ぶだけ (`stepNineteen_swap`)。

書籍の `1/(k^{1+θ}(x₁+u_i))` 等は**結論を座標で読むだけ** (module docstring に対応表:
`s^{ak⁻¹} = (0, a^{1+θ}k^{-(1+θ)})`, `a⁻² = (x₁+u_i)^{2τ}`, `e_i = k d_i a⁻²`)。

### 🎯 段 (20) の核 — (∗)(∗∗)(∗∗∗) を段 (7) + `K` の自由性から

* `eq_and_conj_of_inv_mul_mem_K` — 段 (7) が与えるもの: 引数一致 (= (∗)) と
  `ω' y₂ = (ω' y₁)^{a₁a₂⁻¹}`。
* 🎯 `eq_one_of_conj_eq_mul_Q0` — **`K` は `(Q/Q₀)^#` に自由に作用する**。
  ⚠ **書籍は標準モデル (`μ` 単射) で読むが、モデル不要だった**: Prop 1(a)
  (`Q_inf_centralizer_eq_bot_of_mem_KSet`) の固定点自由性のみ。
  論法 = `ψ : z ↦ z·z^c` が `Q₀` 上単射 (`z⁻¹ = z` と `(z'^c)² = 1` だけ使う)
  ⟹ 有限性から全射 ⟹ `ω^c = ωy` なら `ψ(z) = y` なる `z` で `ωz` が `c` の
  非自明固定点になり矛盾。
* `eq_and_eq_of_inv_mul_mem_K` — **(∗) と (∗∗∗) を同時に**: 同じ `K`-剰余類の
  2 表示 `f(ω x_j) = (ω' y_j)^{a_j}` は完全一致 (`x₁=x₂ ∧ a₁=a₂ ∧ y₁=y₂`)。
  可換性仮説は `D = KW` (`V = W` の下 abelian) から満たされる。

### 🎯 段 (11) の実体化 — `PSU3Sequence.lean` (新 leaf)

⚠ **設計**: 状態 `(z,w,d)` = 書籍の `((0,u_i),(0,v_i),d_i)` として**群の中で**再帰。
停止条件 (`y z = 1` ⟺ `u_i = α`) では**状態をそのまま返す**ので、不変式が
**全 index で無条件**に成り立ち、長さを定義に埋め込まずに済む。

* `exists_mem_K_conj_eq_mul` / `stepElevenNext` / `stepElevenSeq` (`Nat.rec`,
  初期値 `(1, y, ζ)`) / `stepElevenSeq_succ_of_ne` (非停止時の明示形)
* `stepElevenSeq_mem` (`z_i,w_i ∈ Q₀`, `d_i ∈ D`; `f` も段 (10) も使わない)
* `stepElevenSeq_spec` — **不変式 `f(ω z_i) = (ω w_i)^{d_i}`**
* `stepElevenSeq_coset` — **`d_i K = ζ^i K`** (各段は `d` に `ζ` と `K` の平方を
  掛けるだけ + `ζ` が `K` を中心化)

### 🎯 段 (15) の長さ

* `stepElevenSeq_fst_mem_orbitSet` — 各 `z_i` は段 (8) が数える集合そのものに入る
* `stepElevenSeq_pow_ne_one` — 非停止で `n` 段進めたなら `ζ^{n+1} ≠ 1`
  (`not_mem_K_of_f_eq_conj_self` で `d_i ∉ K`、`d_i ∈ ζ^i K` と突き合わせ)
* `exists_stop_lt_orderOf` — **列は `orderOf ζ − 1` 未満で停止**
  (`ζ` が `W` 生成元なら `= m`、書籍の「`1 ≤ i ≤ m−1`」)

### 📊 状態 (2026-08-01)

| 段 | 状態 | 主定理 |
|---|---|---|
| §1 / (A1)-(A3) 橋 / (1)-(10) | ✅ | 既存 |
| **(11)** | ✅ 群レベル完成 | `stepElevenSeq` + `_spec` + `_coset` |
| (12)(13)(14)(17) | ✅ 体側 | `PSU3FieldArithmetic` |
| **(15)** | 🔶 長さ ✅ / 「`u_i` で尽くす」= 残 | `exists_stop_lt_orderOf` |
| (16) | 🔶 体論的核 | `pow_eq_one_of_betaSum_eq` |
| (18) | 🔶 部品 4 本 (`h` の漸化式が残り) | — |
| **(19)** | ✅ | `stepNineteen` / `stepNineteen_swap` |
| **(20)** | 🔶 核 ✅ / 列の instantiate が残り | `eq_and_eq_of_inv_mul_mem_K` |

### 段 (18) も群レベルで完成 (2026-08-01)

* `stepEighteen_step` — `h(ω s^a) = h(ω)·h(ω z)^ζ·a²` ((H6) の `h` 節 + 段 (1) + (H4))
* `stepEighteen_unroll` — 閉じた形 `h(ω z_i) = (h(ω)ζ⁻¹)^i·h(ω)·(ζ^i k)` (`k ∈ K`)

### ⚠⚠ 残る crux が 1 本に同定された: `D` の `(Q/Q₀)^#` への自由性

**次の 3 つが全部これ待ち**:
1. (15) の「`f(ω(0,u))` が軌道に入る `u` は `u_i` に尽きる」 —
   `z_i` の相異性に要る (`z_i = z_j` から `d_i d_j⁻¹` が `ω̄` を固定する、を潰す)
2. (18) の締め `d_{m-1} = ζ⁻¹` ⟹ `(h(ω)ζ⁻¹)^m = 1` —
   停止点で `f(ωy) = ω^{ζ⁻¹}` (`f_conj_swap` で出る) と不変式を突き合わせると
   `ζ⁻¹d_N⁻¹` が `ω̄` を固定する形になる
3. (20) の (∗∗∗) を一般の `a_j ∈ D` で使うとき

**`K` 版は群論的に取れた** (`eq_one_of_conj_eq_mul_Q0`, `PSU3PairComparison.lean`)。
**`W` の元は `Q₀` を中心化する**ので同じ ψ 論法 (`Q` 上の固定点自由性) は効かない。
⟹ **モデル経由が正解**: `D = KW` の元は `Q/Q₀ ≅ E` にスカラー `μ(k,v)` 倍で作用し、
`μ` は単射。

**部品はすべて所在確認済 (2026-08-01、着手可能)**:

| 必要なもの | 出所 |
|---|---|
| `D = KW` の分解 | `exists_mem_K_mem_W_mul hVW` (PSU3Preliminary:993) |
| 対 `(kActor k, v)` の作用 = `c` による共役 | `conjQHom_apply` + `conjQByK_apply_val` (SylowTwo:56) + `conjQByW_apply_val` (TypeBFromW:75) — どれも `rfl` |
| 商への降下 | `quotientKWHom_mk` (QuotientKWField:219, `rfl`/`simp`) |
| スカラー作用 | `M.coord_act` (`QuotientFieldModel` の field) |
| `coord ≠ 0` | `coord_ne_zero_of_not_mem_Q0` (PSU3OrbitCount:154) |
| `μ` 単射 | `mu_injective` (QuotientKWField:504) — 仮説で受けるのが簡単 (hst/hm/hQ0card/hcardQ/induction/s/M が要る) |
| `kv = 1` から `k = 1` | `conjQByK_injective` (ActualKActor:33) |

⟹ **書く場所 = `PSU3OrbitCount.lean`** (モデル配管が全部そこにある、695 行で余裕)。
署名案:
```
theorem eq_one_of_conj_eq_mul_Q0_of_mem_D {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ω c y : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hcD : c ∈ hyp.D)
    (hy : y ∈ hyp.Q0) (hconj : c * ω * c⁻¹ = ω * y) : c = 1
```

**その後**: (a) (15) の尽くし、(b) (18) の締め、(c) (20) の組み立て。

## 2026-08-01 (2): crux 解消 → 段 (15)(13)(16) 完成

### 🎯 残る crux が落ちた — `D` の `(Q/Q₀)^#` への自由性

`PSU3OrbitCount.lean` に追加 (前回の「部品所在」表どおりの配管で通った):

* `conjQHom_kActor_apply_val` — 対 `(kActor k, v)` の `Q` 上の作用が `k v` による
  共役そのもの (定義の展開; `exists_mem_D_conjQHom` の逆向き)。
* 🎯 `eq_one_of_conj_eq_mul_Q0_of_mem_D` — **`c ∈ D`, `ω ∈ Q − Q₀`, `y ∈ Q₀`,
  `ω^c = ω y` ⟹ `c = 1`**。`D = KW` (⟸ `V = W`) で `c⁻¹ = k v` と分解し、
  `quotientKWHom_mk` で `Q/Z(Q)` へ降ろし、`coord_act` でスカラー倍に翻訳、
  `coord_ne_zero_of_not_mem_Q0` で `μ(k,v) = 1`、`μ` 単射 + `conjQByK_injective`。

### 🎯 段 (15) 完成 — `PSU3StepFifteen.lean` (新 leaf)

* `f_mul_eq_conj_of_normalized` — 正規化を裏返して `f(ωy) = ω^{ζ⁻¹}`。
* 🎯 `stepFifteen_stop_d_eq_inv` — **`d_N = ζ⁻¹`** (書籍 p.126 の
  `d_{m₁} = ζ⁻¹`)。⚠ 書籍はここを「By (14), it follows that」で済ませているが、
  2 つの表示を突き合わせて `ζ⁻¹d_N⁻¹ = 1` と結論するには**自由性が要る** — それが
  この章で自由性を必要とした本当の理由。
* `lt_orderOf_of_not_stopped` / 🎯 `stepFifteen_length_eq` — **`N + 2 = orderOf ζ`**
  (= `m₁ = m−1`) と `d_N` の `K` 成分の自明性 (= `c_{m₁} = α`)。
* `pow_sub_eq_one_of_coset_eq` / 🎯 `stepElevenSeq_fst_injOn` — **`z_i` は相異なる**。
  ⚠ 書籍は「`u_i` が相異なるのは `d_i` が相異なるから」と書くだけだが、
  `z_i = z_j ⟹ d_i = d_j` は自由性そのもの。
* 🎯 `stepFifteen_exhaust` — **段 (8) が数える集合 = `{z_0, …, z_N}`**。

### 🎯 段 (13) の橋渡し + 段 (16) — `PSU3SequenceCoordinate.lean` (新 leaf)

* `IsCenterCoordAction` (仮説の命名) / `centerCoord_congr` / `centerCoord_conj_eq`
  (共役を等式で受ける版) / `kActor_inv`。
* 🎯 `stepElevenCoord` + `_succ` — 正規化座標 `U_i = coord(z_i)/coord(s)` が
  **`U_{i+1} = 1/(α + U_i)`** を満たす。
* 🎯 `stepElevenCoord_eq_betaRatio` — **段 (13)**: `U_i = betaRatio β i`。
* 🎯 `stepElevenSeq_ne_one_iff` — 停止則を座標で: 段 `n` で続行可能 ⟺ `β^{n+2} ≠ 1`。
* 🎯 `stepSixteen` — **段 (16)**: `β^{N+2} = 1` かつ `orderOf β = N + 2 = orderOf ζ`。
  ⚠ 書籍は `c_{m−1} = α` 経由だが、停止則を座標で読むと**逆順に**取れて
  `pow_eq_one_of_betaSum_eq` を経由しない (後者は今のところ未使用のまま残る)。
* `betaSum_eq_of_pow_eq_one` — 書籍の `c_{m−1} = α` は `β^m = 1` の系。

### 📊 状態 (2026-08-01 セッション 2 終了時)

| 段 | 状態 | 主定理 |
|---|---|---|
| §1 / (A1)-(A3) 橋 / (1)-(10) | ✅ | 既存 |
| (11) | ✅ | `stepElevenSeq` + `_spec` + `_coset` |
| **(13)** | ✅ 群↔体 の橋渡し込み | `stepElevenCoord_eq_betaRatio` |
| (12)(14)(17) | 🔶 体側のみ | `PSU3FieldArithmetic` |
| **(15)** | ✅ **完成** (長さ + 尽くし) | `stepFifteen_length_eq` / `stepFifteen_exhaust` |
| **(16)** | ✅ **完成** | `stepSixteen` |
| (18) | 🔶 漸化式 ✅ / 締めが残り | `stepEighteen_unroll` |
| (19) | ✅ | `stepNineteen` / `stepNineteen_swap` |
| (20) | 🔶 核 ✅ / 列の instantiate が残り | `eq_and_eq_of_inv_mul_mem_K` |

### ⚠ 次の一手 = (17) の群レベル ⟹ (18) の締め

**(17)** `f(ω(0,u_i)) = (ω(0,u_i+α))^{d_i}` は、群レベルでは
**`w_i = y z_i`** (第 2 成分が `y z_i` に等しい) と同値。列の漸化式で書くと
`w_{i+1} = w_i · (d_i z_{i+1} d_i⁻¹)` なので、必要なのは

    d_i z_{i+1} d_i⁻¹ = z_i z_{i+1}      (⟸ `W` は `Q₀` を中心化するので `K` 成分だけ効く)

座標では `μ(kActor k_i)^d · U_{i+1} = U_i + U_{i+1}`、ここで `k_i` は `d_i` の `K` 成分で
`μ(kActor k_i)^d = (∏_{j=1}^{i} U_j)² = (α/c_{i+1})²`。あとは
`betaSum_mul_betaSum_add_two` (`c_n c_{n+2} = c_{n+1}² + c_1²`, 既存) で閉じる。
⟹ **必要な新規部品 = 「`d_i` の `K` 成分のスカラーを座標で追う」帰納法 1 本**。

**(18)** の締めもこれ待ち: `stepEighteen_unroll` の `k` (= `∏ a_j²`) が
`i = m−1` で 1 になることが要り、それが上と同じ telescoping (書籍の
`α/(β^i + β^{-i})` が `i = m−1` で `α/α = 1`)。
`D = KW` は `V = W` の下 abelian なので、そこまで来れば
`(h(ω)ζ⁻¹)^m = h(ω)^m = k⁻¹ = 1` は 3 行。

## 2026-08-01 (3): 段 (17)(18) 完成 — §2 は (20) の組み立てだけ

### 🎯 段 (17) — `PSU3StepSeventeen.lean` (新 leaf)

段 (17) は群レベルでは**列の第 2 成分が第 1 成分で決まる** = `w_i = y z_i`。

* `betaSum_sq_div_mul_betaRatio` — 体の恒等式
  `(c₁/c_{i+1})² u_{i+1} = u_i + u_{i+1}`。分母を払うと
  `c₁² = c_i c_{i+2} + c_{i+1}²` = 既存の `betaSum_mul_betaSum_add_two`。
  ⚠ 書籍の `u_i/u_{i+1} = 1 + (c₁/c_{i+1})²` と違い `u_i` で割らないので
  `c_0 = 0` の `i = 0` でも成立 → 帰納法を 0 から始められる。
* 🎯 `centerCoord_conj_stepElevenSeq` — **`d_i` は `Q₀` にスカラー `(c₁/c_{i+1})²`
  (書籍の `d_i^{-(1+σ)}`) で作用する**。`d_0 = ζ` は `Q₀` を中心化し、各段は
  `ζ`(無効) と `a⁻²`(スカラー `u_{i+1}²`) を掛けるだけ → telescoping。
* 🎯 `stepElevenSeq_snd_fst_eq` (= (17) の群形) / `stepSeventeen`
  (`f(ω z_i) = (ω y z_i)^{d_i}`)。

### 🎯 段 (18) 完成 — `PSU3StepEighteen.lean` (新 leaf)

* `stepEighteen_unroll` (PSU3Sequence, **差し替え**) — 閉じた形の `K` 成分を
  **`d_i` の `K` 成分の逆元として同定**:
  `∃ k ∈ K, d_i = ζ^{i+1}k ∧ h(ω z_i) = (h(ω)ζ⁻¹)^i h(ω) (ζ^i k⁻¹)`。
  各段は前者に `a⁻²`・後者に `a²` を足すので、2 つの帰納法を 1 本にすると
  段 (15) の `k = 1` (= 書籍の `c_{m−1} = α`) がそのまま (18) に効く。
  ⟹ **書籍の telescoping 体計算 (`α/(β^i+β^{-i})`) を経由しない**。
* `h_mul_eq_conj_inv` ((H4)+(H2) で `h(ωy) = ζ h(ω)⁻¹ ζ⁻¹`) /
  `commute_h_zeta` (`h(ω) ∈ D = KW`; `K` 成分は `W = C_V(K)`、`W` 成分は
  `orderOf ζ = |W|` ⟹ `W = ⟨ζ⟩` から `ζ` と可換)。
* 🎯 `stepEighteen` — **`(h(ω)ζ⁻¹)^{orderOf ζ} = 1`**。

### 📊 状態 (2026-08-01 セッション 3 終了時)

| 段 | 状態 | 主定理 |
|---|---|---|
| §1 / (A1)-(A3) 橋 / (1)-(11) | ✅ | 既存 |
| (12) | 🔶 体側のみ (`exists_add_inv_eq`) | 群側は `β` の供給だけ |
| **(13)** | ✅ 群↔体 の橋渡し込み | `stepElevenCoord_eq_betaRatio` |
| **(14)** | ✅ 群形も (`stepFourteen`) | `d_i = ζ^{i+1}k` + `k` のスカラー |
| **(15)(16)(17)(18)(19)** | ✅ **完成** | 各 leaf |
| (20) | 🔶 核 ✅ / 2 本の列の instantiate が残り | `eq_and_eq_of_inv_mul_mem_K` |

### ⚠ 次の一手 = 段 (20) の組み立て (p.128 を読了済)

書籍の (20) の証明:
1. `x₁` と `x₁ + 1/(k^{1+θ}(x₂+u'_i))` は相異なる ⟹ (8)(19) から、
   `f(ω₁(0,x))‾` が `ω̄₂` の `KW`-軌道に入る `x` を尽くす。
2. (19)(a) を `(u_i)` に、(19)(b) を `(u'_{m−i})` に適用。
3. **(14) と (19) から `e_i^{-t} ∈ e'_{m−i} K`**、これに (7) を当てて
   (∗)(∗∗)(∗∗∗) を得る。
4. (∗∗∗) を `i = 1` と `i = m−1` で読んで `x₁ = x₂ + α₂`, `x₁ + α₁ = x₂`
   ⟹ 標数 2 で `α₁ = α₂ = x₁ + x₂`。⟹ `u'_i = u_i`, `v'_i = v_i`, `d'_i = d_i`。

**🎯 (20) の鍵になる観察 (2026-08-01)**: 書籍が「(14) と (19) から
`e_i^{-t} ∈ e'_{m−i}K`」と書く箇所は、**体のスカラーを一切使わない**。
`t` は `W` を中心化し `K` を反転するので、`D = KW` 上で `(wk)^{-t} = w⁻¹k`
(= `inv_conj_t_of_mem_W_mul_KSet`, 実装済)。よって `W` 成分だけの話になり、
`e_i` の `W` 成分 `ζ^i` (⟸ 段 (14) の coset) が `e_i^{-t}` では `ζ^{-i}` に、
これが `ζ^m = 1` (段 (16)) で `e'_{m−i}` の `W` 成分 `ζ^{m−i}` と一致する。

**残っている部品**:
* 2 本の列 (`α = α₁` 用と `α = α₂` 用) を同時に走らせる設定 (`n ≥ 2` の下)。
* ~~段 (14) の群↔体 橋渡し~~ → **完了** (`stepFourteen`, 2026-08-01):
  `d_i = ζ^{i+1}k` かつ `k` は `Q₀` にスカラー `(c₁/c_{i+1})²` で作用する。
  ⚠ 書籍の `(c_i/α)^{2τ}` とは規約が逆向き (書籍の `c^a = a^{1+θ}c` は `a⁻¹`
  による共役)。
* 添字反転 `i ↔ m − i` の扱い (2 本目の列を逆向きに読む)。

## 2026-08-01 (4): 段 (20) の第一主張 `α₁ = α₂` — §2 の主要部が閉じた

### 🎯 `PSU3StepTwenty.lean` (新 leaf) — **列の機構が要らなかった**

書籍は 2 本の列 (`α = α₁` / `α = α₂`) を走らせ、(19)(a) を index `i`、(19)(b) を
index `m−i` で使い、(∗∗∗) を `i = 1` と `i = m−1` で読む。しかし**その 2 つの
index では列のデータが退化する**:

| index | 列のデータ | (19) の仮説になるもの |
|---|---|---|
| `i = 1` | `(u₁,v₁,d₁) = (0,α,ζ)` | **正規化 `f(ω) = (ωy)^ζ` そのもの** |
| `i = m−1` | `(u_{m−1},v_{m−1},d_{m−1}) = (α,0,ζ⁻¹)` (⟸ 段 (15)(17)) | **裏返した正規化 `f(ωy) = ω^{ζ⁻¹}`** |

⟹ (20) の第一主張は 2 つの正規化だけから回り、`stepElevenSeq` は一切現れない。
書籍の `e_i^{-t} ∈ e'_{m−i}K` も体を使わない (twist が `W` 成分を反転し `K` 成分を
保つ + 両方の `W` 成分が `ζ^{±1}`)。

* `mem_KSet_iff_mem_K`
* 🎯 `stepTwenty_fst_eq` — **`z₁ = z₂ y₂`** (= 書籍の `x₁ = x₂ + α₂`)。
  (19)(a) を `f_conj_swap` で裏返して (19)(b) と向きを揃え、
  `eq_and_eq_of_inv_mul_mem_K` (段 (7)) で共役元の一致 (∗∗∗) を取り、
  `eq_of_sq_eq_of_odd_orderOf` で `a = a'`。
* 🎯 `stepTwenty` — **`α₁ = α₂`** (= `y₁ = y₂`)。核を `ω₁ ↔ ω₂` で 2 回使う。

⚠ 側条件 `z₁ ≠ 1`, `z₂ ≠ 1`, `z_j y_j ≠ 1` を明示仮説にした。これは書籍の
「`ω₁`, `ω₂` は異なる `KW`-軌道にある」に相当し、書籍は (8) 経由で暗黙に使う。
Theorem A の組み立て側で discharge する。

### 📊 状態 (2026-08-01 セッション 4 終了時)

| 段 | 状態 |
|---|---|
| §1 / (A1)-(A3) 橋 / (1)-(11) | ✅ |
| (12) | 🔶 体側 ✅ (`exists_add_inv_eq`); 群側は `β` の供給だけ |
| (13)(14)(15)(16)(17)(18)(19) | ✅ |
| **(20)** | 🔶 **第一主張 `α₁ = α₂` ✅**; 第二主張 (`f(ω₁(0,x)) = (ω₂(0,x+α))^{d(x)}` を全ての `x` で) が残り |

### ⚠ 次の一手

1. **(20) の第二主張**: 「`f(ω₁(0,x))‾` が `ω̄₂` の軌道に入る `x`」は `m` 個あり
   (段 (8))、`x₁` と `x₁ + 1/(k^{1+θ}(x₂+u'_i))` (`1 ≤ i ≤ m−1`) が相異なるので
   尽くす。各々に (19)(b) を当てれば形が出る。⟹ ここでは**列が要る**
   (`stepElevenSeq` + 段 (15) の尽くし `stepFifteen_exhaust` の類似)。

   **計算の中身は同定済 (2026-08-01)**: (19)(b) の右辺引数が `x + α` になる条件は
   `x₁ + u_i = x₂ + u'_{m−i}`、`α₁ = α₂` で `u'_j = u_j` なので
   **`u_i + u_{m−i} = α`**、これは `betaRatio_add_betaRatio` (実装済) そのもの。
   ⟹ 残るのは **2 本の列が一致すること (`u'_j = u_j`) の群レベルでの言明**と、
   一般 index での (∗)(∗∗) の instantiate。
2. **p.129-134 (§3 以降) の調査** — まだ未読。Theorem A の結論
   (`G ≅ PSU(3,q)` または `PGU(3,q)`) への接続。

## 2026-08-01 (5): 段 (20) 第二主張 — **§2 の (1)-(20) が全部揃った**

### 🎯 `stepTwenty_snd` — ここでも列が要らなかった

書籍は (11) の列で「`f(ω₁(0,x))‾` が `ω̄₂` の軌道に入る `x`」を尽くし、
1 つずつ (19)(b) を当てて第二主張を出す。しかし `stepTwenty_fst_eq` は
**すべての `z` について**成立しており (仮説は `z ∈ Q₀` と共役元が `K` にあること
だけ)、必要なのは**共役元を `K` に落とすこと**だけ:

* `c ∈ D = KW` を `c = κ v` と分解 (`exists_mem_K_mem_W_mul`)。
* `v ∈ W` は `Q₀` を中心化するので `ω₂` 側へ移せる: `(ω₂ w)^c = ((ω₂)^v · w)^κ`。
* `ω₂^v` が同じ正規化を満たす: `t` が `W` を中心化 ((H3) の捻れが消える) +
  `v` が `ζ` と可換 (`W = ⟨ζ⟩`)。

⟹ `f(ω₁ z) = (ω₂ w)^c` (`c ∈ D`) なら常に **`w = z y`**。

副産物: `W_eq_zpowers` / `commute_of_mem_W_of_W_eq_zpowers` を
`PSU3StepFifteen.lean` に切り出し (`commute_h_zeta` の内部展開を置換)。

### 📊 Ch. IV §2 の状態: **完了**

| 段 | 主定理 |
|---|---|
| (1)-(11) | 既存 |
| (12) | `exists_add_inv_eq` (体側; 群側は `β` の供給のみ) |
| (13) | `stepElevenCoord_eq_betaRatio` |
| (14) | `stepFourteen` |
| (15) | `stepFifteen_length_eq` / `stepFifteen_exhaust` |
| (16) | `stepSixteen` |
| (17) | `stepSeventeen` |
| (18) | `stepEighteen` |
| (19) | `stepNineteen` / `stepNineteen_swap` |
| (20) | `stepTwenty` (`α₁ = α₂`) / `stepTwenty_snd` (第二主張) |

⚠ (20) の側条件 (`z ≠ 1`, `w y ≠ 1` 等) は書籍の「`ω₁`, `ω₂` は異なる
`KW`-軌道」に相当し、明示仮説として残してある。Theorem A の組み立て側で
discharge する。

### p.129 読了 — §2 締めの Proposition と §3 の入口

**§2 締めの Proposition (p.129)**:
> `D` が `(Q/Q₀)^#` に固定点なく作用すると仮定する。すると、ある `i`
> (`1 ≤ i ≤ n`) が存在して `ω = ω_i` に対し `f(ω) = (ω⁻¹)^ζ` かつ `h(ω) ∈ W`。

⚠ **その仮説は本セッションで定理になった** (`eq_one_of_conj_eq_mul_Q0_of_mem_D`;
`V = W` + 標準モデルの下)。

* 🎯 **前半 `h(ω) ∈ W` は完了** (`h_mem_W`, PSU3StepEighteen.lean)。
  ⚠ 書籍は Sylow ([H] Kap.V Satz 8.15 で `D` の Sylow が巡回) で回すが、
  `D = KW` を持っていれば `κ^m = 1` (段 (18)) と `κ^{q−1} = 1` (`|K| = q−1`) の
  互いに素性で直接出る。
* ✅ **後半も完了** (2026-08-01, PSU3StepTwenty.lean):
  `dOrbitRel_of_stepTwenty_chain` ((H5) 連鎖) →
  `sq_eq_of_dOrbitRel` (`D` の自由性で `ω² = (0,α)`) →
  `f_eq_conj_inv_of_sq_eq` (正規化と合わせて `f(ω) = (ω⁻¹)^ζ`)、
  まとめが `f_eq_conj_inv_of_stepTwenty_chain`。
  ⚠ 書籍の「whence `i = k`」(軌道代表系 `ω_1,…,ω_n` の相異性) だけは、代表系を
  まだ形式化していないので `ω_i = ω_k` を仮説にしてある。
  書籍の論法: `ω₁² = (0,r)` と置き、`f(ω₁⁻¹)‾` が `ω̄_i` の軌道に、
  `f(ω₁⁻¹(0,α))‾` が `ω̄_k` の軌道に入るとして、(17)(20) から 3 本の等式を出し、
  (H4)+(H5) で `i = k` と `ω_i² = (0,α)` を得る。
  ⟹ **(H5) (`(f∘j)³(x) = x^{h(x)⁻¹}`) を初めて使う箇所**。

**§3. Determination of `f` (p.129-)**:
> Proposition. `ω ∈ Q − Q₀` と `ζ ∈ W^#` があって `f(ω) = (ω⁻¹)^ζ` かつ
> `h(ω) ∈ W` なら、`θ = 1` かつ `f(ρ) = (ρ̄/y, 1/y)` (すべての
> `ρ = (ρ̄,y) ∈ Q − Q₀` について)。

### 📋 (H5) 連鎖の設計 (2026-08-01 に読解済 — 次セッションはこれを実装)

`ρ := ω²` (∈ `Q₀`) と置く。`ω⁻¹ = ω ρ` (⟸ `ρ² = 1` ⟹ `ω⁴ = 1`)。
書籍の `i`, `k` は「`f(ω⁻¹)‾` が `ω̄_i` の軌道」「`f(ω⁻¹(0,α))‾` が `ω̄_k` の軌道」。
段 (20) (`stepTwenty_snd`) をペア `(ω, ω_i)` / `(ω, ω_k)` に当てると:

* `f(ω ρ)` は `ω_i (ρ y)` と `D`-共役 (∵ (20): `f(ω z) = (ω_i (z y))^d`, `z = ρ`)
* `f(ω (ρ y))` は `ω_k ρ` と `D`-共役 (∵ `z = ρ y`, `(ρy)y = ρ`)

`X := ω_k⁻¹ ρ` と置く。`j(X) = X⁻¹ = ω_k ρ`。軌道の上で:

| 段 | 使うもの | 結果 |
|---|---|---|
| `(f∘j)(X)` | 上の 2 つ目に `f` を当てて (H2) | `[ω (ρ y)]` |
| `(f∘j)²(X)` | `j`: `(ω(ρy))⁻¹ = ω y` (∵ `ω⁻¹ = ωρ`), `f`: 正規化 + (H2) | `[ω]` |
| `(f∘j)³(X)` | `j`: `ω⁻¹ = ω ρ`, `f`: 上の 1 つ目 | `[ω_i (ρ y)]` |

`dOrbitRel_fj_cube` (⟸ (H5); `h(x) ∈ D` は常に成立するので書籍の
「`h(ω_k⁻¹(0,r)) ∈ KW`」は `D = KW` から自動) より `(f∘j)³(X) = [X]`、
すなわち **`[ω_k⁻¹ ρ] = [ω_i (ρ y)]`**。

軌道代表系の相異性から `i = k`、あとは `sq_eq_of_dOrbitRel` (実装済) で
`ω² = (0,α)`、`f_eq_conj_inv_of_sq_eq` (実装済) で `f(ω) = (ω⁻¹)^ζ`。

⚠ 実装上の道具: `dOrbitRel` / `dOrbitRel.symm` / `dOrbitRel.trans` /
`dOrbitRel.inv` / `dOrbitRel_f` / `dOrbitRel_fj_cube` (すべて
`OddOrder/GroupTheory/RankOneBNPair.lean`)。`f` が軌道に降りることを使う各段で
(H2) (`hTwo`) の `f(f x) = x` が要る。

### ⚠ 次の一手

1. **§3 "Determination of `f`" (pp.129-134)**。
   > Proposition. `ω ∈ Q − Q₀` と `ζ ∈ W^#` があって `f(ω) = (ω⁻¹)^ζ` かつ
   > `h(ω) ∈ W` なら、`θ = 1` かつ `f(ρ) = (ρ̄/y, 1/y)` (すべての
   > `ρ = (ρ̄,y) ∈ Q − Q₀`)。

   ⚠ **その 2 つの仮説は §2 で定理になった** (`f_eq_conj_inv_of_stepTwenty_chain` と
   `h_mem_W`)。p.130 のページ画像は保存済、p.131-134 は未取得
   (`pdftoppm -png -r 200 -f <first> -l <last>` で取得して
   `references/peterfalvi/pages/` に保存する規約)。
2. 軌道代表系 `ω_1,…,ω_n` の形式化 (「異なる `KW`-軌道」)。段 (20) の側条件と
   §2 締めの `i = k` がこれ待ちで仮説として残っている。

## 2026-08-01 (6): §3 "Determination of `f`" に着手

ページ画像 p.131-134 を取得し `references/peterfalvi/pages/` に保存 (references
リポにコミット済)。p.130 の構成:

* **(1)** `a ∈ K` に対し `f(ωs^a)^{ζ⁻¹a²}s^a = f(ωs^a)^{ζ⁻²}ω^{ζ⁻¹}`。
  冒頭が `(f∘j)³(ω⁻¹) = ω^{-ζ³}` と `h(ω⁻¹) = ζ⁻³`、続いて §2 の (2)(3) を使う。
* **(2)** `f(ωs^a)‾ = ω̄/(a² + ζ⁻¹)` (右辺は `E` で計算)。
* **(3)** **`θ = 1`** かつ `ω² = (0, ζ + ζ⁻¹)`。
  ⚠ `θ = 1` の論法: `c = X + X^θ` が `X ∈ F − {0, α^{2τ}}` に依らない ⟹
  `θ ≠ 1` なら `|F| ≥ 8` (θ は奇数位数) で `{X,Y,X+Y} ∩ {0,α^{2τ}} = ∅` なる
  `X,Y` が取れて `c = c + c = 0` ⟹ `X^θ = X` ⟹ `θ = 1`。
* **(4)** `y + y^q = ω̄^{1+q}` なる全ての `y ∈ E` で `f(ω̄,y) = (ω̄/y, 1/y)`。

### 🎯 実装済 (`PSU3SectionThree.lean`, 新 leaf)

* `conj_t_pow_eq` — `t` は `W` の元の冪を中心化。
* `fj_cube_of_f_eq_conj_inv` — **`(f∘j)³(ω⁻¹) = ω^{-ζ³}`** ((H3) を 3 回)。
* 🎯 `h_inv_eq` — **`h(ω⁻¹) = ζ⁻³`**。(H5) と突き合わせると `ζ³h(ω⁻¹) ∈ D` が
  `ω⁻¹` を固定 ⟹ 自由性で自明。⚠ 書籍の `h(ω⁻¹) = h(ω)^{-t} ∈ W` 経由は不要。
* `h_eq_zpow_three` — `h(ω) ∈ W` なら `h(ω) = ζ³`。

* 🎯 `eq_self_of_add_eq_const` (PSU3FieldArithmetic.lean, 2026-08-01) —
  **§3 (3) の `θ = 1` の数え上げ論法**。標数 2 の有限体で、単射な加法写像 `θ` が
  2 元集合 `{0,z}` の外で `X + θX = c` を満たし `|F| ≥ 5` なら `θ = id`。
  `X` を `{0,z}` の外、`Y` を `{0,z,X,X+z}` の外に取ると `X,Y,X+Y` が全て
  適用域に入り `c = c + c = 0`。残る点 `z` は `θ` の単射性で固定。
  ⚠ 書籍の `|F| ≥ 8` は「`θ` が巡回な自己同型群で奇数位数」から来るが、
  数え上げに要るのは `5` だけ。

* 🎯 `f_inv_eq` / `g_inv_eq` (2026-08-01) — 書籍が一行で済ませる
  「Also, `f(ω⁻¹) = ω^{ζ⁻¹}` and `g(ω⁻¹) = ω^ζ`」。前者は仮説に `f` を当て
  (H2) + (H3)、後者は (H1) の `g(x⁻¹) = f(x)⁻¹` そのまま。

* ✅ **§3 (1) 完了** (`stepOne_chain`, 2026-08-01)。両辺は同じ元 `f(ω⁻¹s^a)` を
  §2 の段 (2)(3) の 2 通りで読んだもの。出会うのは `s^a ∈ Q₀ = Z(Q)` で積の順序が
  入れ替わるから。代入は `f_inv_eq` / `g_inv_eq` / `h_inv_eq`。

### 📊 §3 の状態 (2026-08-01 夕 更新)

| 段 | 状態 |
|---|---|
| (1) | ✅ `stepOne_chain` (+ `fj_cube_of_f_eq_conj_inv` / `h_inv_eq` / `h_eq_zpow_three`) |
| (2) | ✅ `stepTwo_linear` — `(μ(a²,1) + μ(1,ζ))·f(ωs^a)‾ = ω̄` |
| (3) | ✅ **`stepThree`** — `θ = 1` (= `σ\|_F = τ\|_F`) かつ `α = σ(ζ+ζ⁻¹)`。側条件 `5 ≤ \|F\|` 付き |
| (4) | ⬜ `y + y^q = ω̄^{1+q}` なる `y` で `f(ω̄,y) = (ω̄/y, 1/y)` |

### 🎯 §3 (3) の連鎖 — `(∗)` まで完成 (2026-08-01)

**スカラー規約の罠は決着した**。repo のスカラーは書籍の**一様な逆元**
(書籍の `x^d = d⁻¹xd` に対し `coord_act` は `d` 共役)。段 (2) と段 (10) が
同じ向きに反転するので**最終の体の等式は書籍と同じ形**になる。前セッションで
机上の食い違いに見えたのは片方だけ反転させたため。

**書籍の割り算経路は不要だった**。書籍は段 (2) の 2 実例から
`1/(a²+ζ⁻¹) = ζa⁻²/(b²+ζ⁻¹)` を作って襷掛けするが、2 実例は同じ `ω̄` を
評価し段 (10) が 2 つの未知数を結ぶので、`b` 側の未知数 (≠ 0) を約すだけで
出る ⟹ **側条件 `a²+ζ⁻¹ ≠ 0` が要らない**。

| 補題 | 内容 |
|---|---|
| `kActor_eq_inv` / `kActor_eq_pow` | `conjQByK` が準同型 ⟹ `kActor` は逆元/冪を保つ |
| `stepTen_quotient_coord` | 段 (10) を `Q ⧸ Z(Q) ≅ E` で読む: `f(ωs^a)‾ = (μ(a²)μ(ζ))⁻¹·f(ωz)‾` |
| `eq_add_inv_add_inv_of_mul_inv_eq` | `(A+Z)(AZ)⁻¹ = B+Z` ⟹ `B = A⁻¹+Z+Z⁻¹` |
| 🎯 `stepThree_sq_eq` | **群↔体の橋渡し** = 書籍の `b² = ζ+ζ⁻¹+a⁻²` |
| `stepThree_center_relation` | `Q₀` 側 = 書籍の `b^{2(1+θ)} = α² + a^{-2(1+θ)}` |
| `star_of_scaling_pair` | scaling pair `(σ,τ)` 経由で 2 本を合流させる純代数 |
| 🎯 `stepThree_star` | **`(∗)`** (admissible な `a` 1 つに対して) |

体側の 3 本は **`w = ζ + ζ⁻¹` で述べ直した** (`eq_of_sq_add_sq` /
`eq_one_and_eq_of_star` / `star_of_sq_eq`)。⚠ 美観でなく**必要性**:
数え上げが走るのは部分体 `F` (`|F| = q`) の上で `E` (`q²`) ではない。`ζ` は
`F` に入らないが `w` はトレースなので入る (`ζ^σ = ζ⁻¹`)。`X = a⁻²` も `K` の
スカラーゆえ `F` の元。⟹ `w` 版でないと `F` に instantiate できない。

### ✅ 正規化の差は解消した (2026-08-01、下記 `eq_id_of_sq_eq_mul_on`)

**以下の節は歴史的記録**。結論だけ先に: 書籍の `{μ|_F, ν|_F} = {1_F, θ}` は
**追加の選択でなく帰結**で、`σ|_F = 1` もモデルの `θ|_F = 1` も強制される。

### ⚠ 正規化の差 (当初の記録)

`stepThree_star` の結論の `α` は **`σ⁻¹ α`** の形で出る。書籍は
`{μ|_F, ν|_F} = {1_F, θ}` すなわち `σ|_F = 1` に正規化するのでここが消えるが、
repo の model 層はその正規化を持たない
(`exists_scalingPair_of_lemmaFiveSetup` の docstring 自身が
"before the normalization" と言っている)。

⚠ **これは gap でなく座標の取り方の差**: 本証明が出す `σ|_F = τ|_F` は
「`φ(ax,by) = (ab)^{2^i}φ(x,y)`」すなわち**全体 Frobenius 捻れを除いた
`θ = 1`**。書籍の `θ` は type B のデータとして与えられており、repo は
`θ` を `σ` から**定義**している (issue 0167 の方針) ので、repo での
「`θ = 1`」の正しい表明は `σ|_F = τ|_F` である。

⚠ 机上で確認した反例: `d ≡ 2^i + 2^{i'} (mod 2^m−1)` は一般に
`1 + 2^{j}` の形にならない (`m = 3`, `i = i' = 1` で `d ≡ 6`、
`1+2^j ∈ {2,3,5}`)。⟹ `σ|_F = 1` は `(σ,τ)` のデータだけからは出ない。

### 🎯 走査は完成 (2026-08-01)

* `mu_kActor_sq` — `μ(a²) = μ(a)²`。
* `exists_mem_K_mu_sq_inv_eq` — `c ∈ F^×` に対し `a ∈ K` で
  `μ(kActor(a²),1)⁻¹ = c`。`μ(K) = F^×` (`exists_actualKActor_mu_eq`) +
  標数 2 の平方の全単射性 (逆写像 `x ↦ x^{2^{m-1}}` を明示)。
⟹ `(∗)` は `X ∈ F^×` 全体で使える。

### ⚠⚠ `5 ≤ |F|` は自明でない (2026-08-01 に机上で確認)

`eq_one_and_eq_of_star` は `5 ≤ Nat.card F` を要求する。**`|F| = 4` では
数え上げが実際に破れる**: `F = 𝔽₄`, `θ = Frob` (位数 2) とすると
`X + θX = Tr(X) = 1` が `X ∈ 𝔽₄ ∖ 𝔽₂` の両方で成り立つので、除外集合
`{0,1}` の外で `X + θX` は定数だが `θ ≠ id`。

書籍の逃げ道は「**`θ` は奇数位数**ゆえ `θ ≠ 1` なら `|F| ≥ 8`」
(`Aut(F) ≅ ℤ/m` で `m ≤ 2` なら奇数位数の元は 1 のみ)。しかし repo の
`θ := σ⁻¹τ` は奇数位数が既知でない (`θ` の奇数位数は type B のデータ側の
情報で、`(σ,τ)` からは出ない — 上記「正規化の差」と同根)。

⟹ **選択肢**: (a) `3 ≤ m` (= `8 ≤ q`) を明示仮説として持ち回り、供給を
別タスクにする / (b) `θ` の奇数位数を model 層 (Ch. III §3) で用意する。
⚠ どちらにせよ**隠さず側条件として見えるようにする**こと。

### 🎯🎯 §3 (3) 完成 (2026-08-01) — `stepThree`

数え上げの組み立てに要った部品 (すべて本セッション):

| 補題 | 役割 |
|---|---|
| `exists_mem_K_mu_sq_inv_eq` | `X` が `F^×` 全体を掃く |
| `eq_of_conj_distinguishedInvolution_eq` | `K` は `Q₀^#` に regular ⟹ 除外点は**一意** |
| `subfieldRestrict` / `eq_one_and_eq_of_star_subfield` | 数え上げを `F` へ移送 |
| `mu_W_add_inv_mem_frobFixed` / `_ne_zero` | `w = ζ+ζ⁻¹ ∈ F`、`w ≠ 0` |
| `stepThree` | 🎯 組み立て |

⚠ **持ち回っている側条件 `hcard : 5 ≤ |F|`** = 書籍の「`θ` は奇数位数ゆえ
`|F| ≥ 8`」。無しでは数え上げが実際に破れる (`𝐅₄` の反例は上記)。供給は
type B のデータ側 (`θ` の奇数位数) か `3 ≤ m` の別ルートで、**別タスク**。

### 📐 §3 (4) の設計調査 (2026-08-01) — **座標系の食い違いが本体**

p.131 で (4) の証明を読み切った。骨格:
* `ω = (ω̄, x)` と置き、(1)+(3) から `a ∈ F^#` に対する等式を出す。
* (2) より `f(ω̄, x+a) = (ω̄/(a+ζ⁻¹), γ(a))` (`γ(a) ∈ E`)。
* 第 2 成分の比較で **`(∗∗) (a²+1)γ(a) = x + a + (1+ζ⁻²)/(a+ζ⁻¹)`**。
* `a = 1` で `x = ζ⁻¹`。すると `(∗∗)` は `(a²+1)γ(a) = (a²+1)/(a+ζ⁻¹)` に化け、
  `a ∈ F − {0,1}` で **`γ(a) = 1/(a+ζ⁻¹)`**。
* `y = ζ⁻¹` は `(ω̄,y) = ω` 自身で別途、最後に `ω ↦ ω⁻¹`, `ζ ↦ ζ⁻¹` で
  残る 1 点を潰す (`ζ+1 ≠ ζ⁻¹+1`)。

⚠⚠ **ここまでと質が変わる。(4) は書籍の座標表示そのものの上の計算であり、
しかも書籍と repo でパラメータ化が違う**:

| | 第 1 成分 | 第 2 成分 | 積 |
|---|---|---|---|
| repo (`BilinearTwistedProduct φ`) | `x ∈ E` | `z ∈ F` | `(x,z)(x',z') = (x+x', φ(x,x')+z+z')` |
| 書籍 §3 (4) | `ω̄ ∈ E` | `y ∈ E` で `y + y^q = ω̄^{1+q}` | PSU(3,q) の unipotent 座標 |

`{y ∈ E : Tr(y) = ω̄^{1+q}}` はトレース写像 `E → F` のファイバー ⟹ `F` の剰余類
(位数 `q`) で、repo の `z ∈ F` と同じ大きさ。**両者は同じ群の別表示**であって、
`f(ω̄,y) = (ω̄/y, 1/y)` という書籍の式は書籍側の表示でしか意味を持たない。

⟹ **(4) の実体 = repo の `BilinearTwistedProduct φ` と PSU(3,q) unipotent 座標の
橋渡しを作ること**。これは章末の「`G ≅ PSU(3,q)`」でどうせ要る本体作業。
`GroupTheory/SpecificGroups/ProjectiveUnitary/*` の実測から始める。

**追い風 2 つ**:
* `exists_standardModel` は **`Φ (x₀) = ⟨0,1⟩`** (`s ↦ (0,1)` の正規化) を
  既に持っている — 段 (10) の頃「repo に無い」と書いたが誤りだった。
* **`θ = 1` (= §3 (3)) で `φ(ax,by) = a·θb·φ(x,y)` が `ab·φ(x,y)` になる** —
  すなわち `φ` が本当に `F`-双線型になる。(4) の計算はこれが前提。

⚠ **接続の注意**: `exists_standardModel` の `θ : M.E ≃ₐ[ZMod 2] M.E` と
`stepThree` の `θ : M.E →+ M.E` (= `σ⁻¹∘τ`) は**別物**。前者は `σ` 側、後者は
`σ⁻¹τ`。上記「正規化の差」と同じ話なので、(4) に入る前に**この 2 つの `θ` の
関係を確定させること**が最初のタスク。

### ✅ 2 つの `θ` の照合 = 完了 (2026-08-01) — `eq_id_of_sq_eq_mul_on`

**標数 2 の体で環準同型 `ρ, ψ` が `ρ(a)² = a·ψ(a)` を満たせば `ρ = ψ = id`**。
証明 5 行、`Aut F` の分類も整数論も不要:
`a+b` に適用 + `(ρa+ρb)² = ρa²+ρb²` ⟹ `a·ψ(b) = b·ψ(a)`、`b = 1` で `ψ = id`、
すると `ρ(a)² = a²` で平方の単射性から `ρ = id`。

**適用**: モデルは中心を `a ↦ a·θ_model(a)` でスケールし (`hdiagscale` + `hsemi`
を `b := a` で使う; `φ(x,x) ≠ 0` の非等方性で `b` を同定)、scaling pair は
`σ(a)τ(a)` でスケールする。§3 (3) の `σ|_F = τ|_F` を入れると `F` 上で
`σ(a)² = a·θ_model(a)` ⟹ 両方 id。

⟹ **`θ_model|_F = 1` (書籍の `θ = 1` そのもの) かつ `σ|_F = 1`**
⟹ `stepThree` の `σ⁻¹α` は `α`。⚠ 当初「正規化の差」として記録した 2 点は
**解消**した (`stepThree` の docstring も訂正済)。

✅ **配線も完了** — `thetaModel_eq_id_on_frobFixed` (2026-08-01)。
`hsemi` と `hscaleQ0` を `x = y = 1` で評価して `μ(k)·θ(μ(k)) = μ(k)^d` を出し
(非等方性 `φ(1,1) ≠ 0` が正当化)、`hpair` の `σ(μ(k))τ(μ(k)) = μ(k)^d` と
突き合わせ、`μ(K) = F^×` で `F` 全体に広げて `eq_id_of_sq_eq_mul_on` へ。

仮説の出所: `hsemi`/`haniso` = `exists_standardModel` の第 1・2 節 /
`hpair` = `exists_scalingPair_of_lemmaFiveSetup` / `hστ` = `stepThree`
(`σ.symm (τ a) = a` から `τ a = σ a`)。
✅ **`hscaleQ0` も完了** — `cocycle_scale_of_diagScale` (2026-08-01)。
`hdiagscale` の前提がちょうど `centreQuadraticMap_smul` (降下した平方写像の
`K`-同変性) で、直接の instantiation だった。

⟹ **照合チェーンは端から端まで閉じた**:
`hdiagscale` + `centreQuadraticMap_smul` → `hscaleQ0` → (`hsemi`+`haniso`)
`μ(k)·θ(μ(k)) = μ(k)^d` → (`hpair` + `stepThree` + `μ(K)=F^×`)
`σ(a)² = a·θ(a)` → `eq_id_of_sq_eq_mul_on` → `σ|_F = θ_model|_F = id`。

### 📐 PSU(3,q) 座標の実測 (2026-08-01) — `RootGroup` が書籍の座標そのものだった

`OddOrder/GroupTheory/SpecificGroups/ProjectiveUnitary/RootGroup.lean`:

    structure RootGroup (n : ℕ) where
      fst, snd : Field n
      condition : snd + star snd = fst * star fst
    (a,b)*(c,d) = (a+c, b+d+ a * star c)

**書籍 §3 (4) の `(ω̄, y)` (`y + y^q = ω̄^{1+q}`) と逐語で同じ**。docstring 自身が
「This is Peterfalvi Part II, Chapter III §3, where `phi(x,y) = x * y^q`」と書いている。
`equivSigma` / `natCard` (= `q³`) / `natCard_add_star_eq_mul_star` (ファイバーは
ちょうど `q` 個) まで在る。

⚠⚠ **橋渡しの正体が判明した — 素朴な座標変換では**ない:
* `RootGroup` の 2 つ目の成分は `E` の元 (トレース条件付き)、
  `BilinearTwistedProduct φ` のそれは `F` の元。
* 素朴に切断 `b₀` を取って `b = b₀(a) + z` と書くと
  `φ_std(a,c) = b₀(a)+b₀(c)+b₀(a+c) + a·star c` になるが、
  **これは双加法的でない** (`b₀` の 2 次コバウンダリ欠損が残る; `Tr∘b₀ = N` で
  `N` が非加法的ゆえ `b₀` を線型に取れない)。机上で確認した。
* 正体は **「対角を保ったまま非対角値を `F` に補正する」** 操作で、
  repo は既に持っている: `exists_bilinear_frobFixed_of_diag`
  (`ModelIsomorphism.lean:744` で `φ₀ ↦ φ` にまさに使われている)。
  `φ₀(x,y) = x·y^q` は `E` 値だが対角 `φ₀(x,x) = x^{1+q}` は `F` 値、というのが
  適用条件。

⟹ **橋渡しの正しい形**: `RootGroup n` と `Q` を、*同じ対角 `x^{1+q}` を持つ
`F`-双線型 `φ`* を経由して突き合わせる。Ch. III §3 が `Q ≃* BilinearTwistedProduct φ`
を与えているので、`RootGroup n ≃* BilinearTwistedProduct φ'` を同じ補正で作り、
`φ` と `φ'` を対角の一致から同定する。⚠ `θ = 1` (§3 (3) + `thetaModel_eq_id_on_frobFixed`)
が `φ` の `F`-双線型性を保証しているので**今この道が通る**。

### 🎯 橋渡しの明示公式を導出した (2026-08-01) — 次セッションは実装のみ

`u` を `frobTrace n u = 1` なる元とする (`exists_frobTrace_eq_one`)。
`φ₀(x,y) := x · star y` (= `x·y^q`) と置く。これは `ZMod 2`-双線型
(`star` = `2^n` 乗は加法的) で、対角 `φ₀(x,x) = x·star x = N(x)` は `F` 値。

    ψ(x,y) := φ₀(x,y) + u · frobTrace n (φ₀(x,y))        -- F 値・同じ対角

**同型**:

    Ξ : RootGroup n → BilinearTwistedProduct ψ'
    Ξ (a, b) = ⟨ a , b + u · a · star a ⟩

* **終域に入ること**: `Tr(b + u·N(a)) = Tr b + N(a)·Tr u = N(a) + N(a) = 0`
  (`Tr b = b + star b = N(a)` が `RootGroup` の条件、`N(a) ∈ F` ゆえ
  `Tr(u·N(a)) = N(a)·Tr(u) = N(a)`)。
* **乗法性** (机上で検算済): `γ(a) := u·N(a)` と置くと必要なのは
  `γ(a)+γ(c)+γ(a+c) = u·Tr(a·star c)` で、
  `N(a+c) = N(a)+N(c)+a·star c+star a·c` から左辺 `= u(a star c + star a c)`、
  右辺も `u·Tr(a star c) = u(a star c + star a c)` ✓。
  ⟹ `Ξ((a,b)(c,d)) = Ξ(a,b)·Ξ(c,d)` が厳密に成立。
* **全単射**: `Ξ⁻¹⟨a,z⟩ = (a, z + u·N(a))`。

⚠ **`exists_bilinear_frobFixed_of_diag` をそのまま使わない**理由: その結論は
`ψ x y = φ x y + u * frobTrace (φ x y)` の形で `u` を出すが、**`frobTrace u = 1`
を結論に含めない** (証明内部の `exists_frobTrace_eq_one` に隠れている)。
上の `γ` は同じ `u` の `Tr u = 1` を要るので、`exists_frobTrace_eq_one` から
`u` を自分で取り `ψ` を直接定義する方が短い。

**API 接続**: `star x = conjugation n x = x ^ 2 ^ n` (`conjugation_apply`, 要 `0 < n`)
⟹ `OddOrder.FiniteField` 側の `qFrobenius (Field n) 2 n` / `frobTrace n` /
`frobFixedSubfield (Field n) 2 n` と繋がる。`Nat.card (Field n) = (2^n)^2` は
`natCard_field`。

### 🎯🎯 橋渡し完成 (2026-08-01) — `toTwistedProduct`

新 leaf `ProjectiveUnitary/RootGroupTwistedCoordinates.lean` (root aggregator 配線済)。

| 補題 | 内容 |
|---|---|
| `frobTrace_eq_add_star` | `star` (= `q` 乗) と `frobTrace` API の接続 |
| `norm_mem_frobFixed` | `a·ā ∈ F` |
| `snd_add_norm_mem` | 補正後の第 2 成分が `F` に入る |
| `norm_cocycle` | `a ↦ u·a·ā` の余境界 = `u·Tr(a c̄)` |
| `hermitianBilin` / `correctedBilin` / `rootBilin` | `x·ȳ + u·Tr(x·ȳ)` を `F` 値双線型写像として |
| 🎯 `toTwistedProduct` | **`RootGroup n ≃* BilinearTwistedProduct (rootBilin …)`** |

full build green (4973 jobs) / lint --strict clean / sorry 0 / AxiomsCheck OK。

### 📐 次に要るのは**余輪体の同定** (2026-08-01 の分析)

`toTwistedProduct` は `RootGroup` 側だけの話。§3 (4) を書くには `Q` と繋ぐ必要があり、
* `Q ≃* BilinearTwistedProduct φ` (Ch. III §3 `exists_standardModel`)
* `RootGroup n ≃* BilinearTwistedProduct (rootBilin)` (今回)
の**2 つの `φ` を同定する**のが残り。repo には `BilinearTwistedProduct.congrEquiv`
(余輪体の同値に沿った輸送) が既にある。

**同定の中身**: `θ = 1` (§3 (3)) により `φ` は `F`-双線型で、`E` は `F` 上 2 次元。
両者とも非等方。⚠ **対角が鍵**:
* `rootBilin(x,x) = N(x) + u·Tr(N(x)) = N(x)` — `N(x) ∈ F` ゆえ `Tr(N(x)) = 0`。
  **対角はちょうどノルム**。
* `φ(x,x) = χ(x)` (`centreQuadraticMapE`、= `Q` の平方写像)。
⟹ 標数 2・2 次元の非等方二次形式の分類 (本質的に二次拡大のノルム形式ただ一つ) に
帰着する。`φ` と `rootBilin` の対角を突き合わせれば `congrEquiv` で輸送できる。

⚠ これは章末の `G ≅ PSU(3,q)` でも必ず要る (repo の PSU(3,q) は `RootGroup` +
`StandardGenerators` + `Bruhat` で構成されている) ので、迂回できない本体作業。

**足がかりは landing 済** (2026-08-01): `rootBilin_diag_coe` /
`rootBilin_anisotropic` — `rootBilin(x,x) = x·x̄` (補正項は対角で消える)。

### 📐 同定は既存の type B 基盤に載せる (2026-08-01 の実測)

⚠ `BilinearTwistedProduct.congrEquiv` は**同じ `B` の自己同型**用で、異なる 2 つの
余輪体を繋ぐものではない。2 余輪体版 (`B' (f x) (f y) = g (B x y)` から
`BilinearTwistedProduct B ≃* BilinearTwistedProduct B'`) の一般化が要る
(`congrEquiv` の直接の一般化、~30 行)。

**より重要**: repo には type B の分類基盤が既にある — 手で分類を書き起こす前に
必ずこちらを読むこと:
* `Suzuki2Groups/Types.lean` — `typeBQuadraticMap phi epsilon` と
  `typeBQuadraticMap_anisotropic`。**`phi = 1` がまさに我々の `θ = 1` の場合**。
* `Suzuki2Groups/FieldModel.lean` — `epsilon_ne_zero_of_anisotropic` /
  `isField (hq : (typeBQuadraticMap (1 : RingAut F) ε).Anisotropic)`。
* `Suzuki2Groups/SplitUniqueness.lean` — Appendix III Theorem (e) の一意性半分
  (`nonempty_summandEquiv_of_isomorphic`)。
* `Suzuki2Groups/QuotientPlaneModel.lean` — `exists_planeCoordinates_of_isomorphicSplit`。

⟹ **`φ` と `rootBilin` をそれぞれ `typeBQuadraticMap 1 ε` の形に同定し、`ε` の
スケーリングで突き合わせる**のが筋。⚠ 標数 2・2 次元の非等方二次形式の分類を
自前で書き起こす前に、上記が何を既に与えているかを実測すること。

### ⚠ 次の一手 (次セッションはここから)

1. `Suzuki2Groups/Types.lean` + `FieldModel.lean` + `SplitUniqueness.lean` の実測
   (何が既にあるか)。
2. 2 余輪体版 `congrEquiv` の一般化。
3. `φ` と `rootBilin` の同定 ⟹ `Q ≃* RootGroup n`。
4. §3 (4) 本体 (骨格は上記で確定済)。
5. `5 ≤ |F|` の供給 (場合分けは上記に記録)。
2. §3 (4) 本体 (骨格は上記のとおり確定済)。
3. `5 ≤ |F|` の供給。⚠ 完全な解決は場合分けになる:
   `m ≥ 3` は数え上げ / `m = 2` は「`θ|_F = Frob` なら `σ(x)τ(x) = σ(x³) = 1`
   ⟹ `x^d = 1` が `F^×` 全体で成り立ち `x ↦ x^d` の全単射性に矛盾」/
   `m = 1` は `F = 𝐅₂` で自明 (環準同型は `0,1` を固定)。
   ⟹ 要 `x ↦ x^d` の `F^×` 上の全単射性 (全射は
   `exists_mem_KSet_conj_eq_of_mem_Q0` + `centerCoord` の全単射性から)。
4. 軌道代表系 `ω_1,…,ω_n` の形式化 (段 (20) の側条件と §2 締めの `i = k` 用)。

## 2026-08-01 (8): 🎯🎯 同定完成 — `Q ≃* RootGroup q`

§3 (4) が要求していた「Ch. III §3 のモデルと PSU(3,q) ユニタリ座標の同定」が
**端から端まで閉じた**。3 コミット。

### 🎯 数学的核 — `OddOrder/Algebra/AnisotropicNormForm.lean` (新 leaf)

**標数 2 の有限体上、非等方な 2 変数二次形式は二次拡大のノルム形式ただ一つ**。
既存の type B 基盤 (`Suzuki2Groups/FieldModel.lean`) は `F[X]/(X²+εX+1)` を
*作る*向きしか持たなかった (⟸ 前セッションの「同定は既存 type B 基盤に載せる」
という見立ては半分だけ正しかった: `mul_conj` は使えず、逆向きを書く必要があった)。

| 補題 | 内容 |
|---|---|
| `artinSchreier` | `℘ : t ↦ t² + t` (標数 2 で加法的)、核 = `{0,1}` |
| `index_range_artinSchreier` | 像の指数は 2 |
| `add_mem_range_artinSchreier` | **像の外の 2 元の和は像に入る** (Arf 不変量の実体) |
| `frobCoordEquiv` | `F` 上独立な 2 元から座標 `F × F ≃+ E` |
| 🎯 `exists_addEquiv_norm_of_anisotropic` | **`χ x = f x · (f x)^q` なる `F`-線型全単射 `f`** |

証明 (多項式・体拡大の機構を一切使わない形に組んだ):
* 極形式 `B` は恒等的に 0 でない — さもなくば `x ↦ √(χ x)` が `E → F` の単射で
  `q² ≤ q` に矛盾。
* `B v w = χ v =: c` に正規化 ⟹ `χ(av+bw) = c(a² + ab + δb²)`。
* 相対トレース 1 の `u` (repo の `exists_frobTrace_eq_one`) を取ると `u^q = u+1` で
  **`N(a+bu) = a² + ab + b²P`** (`P := u²+u`)。⚠ ここで `{1,u}` が `F`-基底。
* **非等方性 = `δ, P ∉ ℘(F)`** (`δ = t²+t` なら `χ(tv+w) = 0`、`P = b²+b` なら
  `u+b ∈ {0,1}` で `u ∈ F`)。指数 2 から `δ + P = t² + t` が解け、置換
  `a ↦ a + tb` で 2 つの形が一致。
* ⚠ Artin–Schreier の**可解性** (`∀β∈F, ∃y∈E, y²+y=β`) は**要らなかった** —
  必要なのは `℘(F)` の指数が 2 という一点だけ。

### 🎯 捻れ積側 — `Suzuki2Groups/TwistedProductComparison.lean` (新 leaf)

* `congrEquiv` を **2 余輪体版に一般化** (`QuadraticExtensions.lean`)。
  既存の自己同型用途は `B' = B` の特殊化として不変。
* `BilinearTwistedProduct.comap` — 座標同値に沿った余輪体の引き戻し
  (`ZMod 2` 加群間の加法写像は自動的に線型)。
* 🎯 `nonempty_mulEquiv_of_diag` — **対角が対応する 2 つの捻れ積は同型**。
  ⚠ 座標同値が余輪体そのものを保つ必要は**ない** (それは `congrEquiv`) —
  「同じ平方写像を持つ中心拡大」として `GroupExtension.equivOfCommonSquareMap`
  (= Appendix III Lemma 1(c)) に渡す。

### 🎯 合流 — `ProjectiveUnitary/RootGroupIdentification.lean` (新 leaf)

* `frobFixedAddEquiv` — 環同型は `x^q = x` を保つので固定部分体が対応する。
* 🎯 `nonempty_mulEquiv_rootGroup_of_anisotropic` —
  **`|E| = q²` で `φ` が非等方 `F`-双線型なら
  `BilinearTwistedProduct φ ≃* RootGroup n`**。
  体の同定は `FiniteField.ringEquivOfCardEq` (同位数の有限体は同型)。

### 🎯 適用 — `Suzuki/PSU3RootGroupModel.lean` (新 leaf)

* `Hypothesis.nonempty_mulEquiv_rootGroup` — **`Q ≃* RootGroup q`**。
  仮説は `exists_standardModel` の出力そのもの + `θ = 1` (§3 (3) +
  `thetaModel_eq_id_on_frobFixed`)。`θ` は素の関数として取る (2 つの束ね方
  (`≃ₐ[ZMod 2]` と `→+*`) の差を吸収し、`F` 上の値しか使わないため)。

### 📊 状態

| 段 | 状態 |
|---|---|
| §1 / §2 (1)-(20) | ✅ 完了 |
| §3 (1)(2)(3) | ✅ 完了 |
| §3 (4) 座標橋 | ✅ **完了** (本セッション) |
| §3 (4) 本体 | ⬜ `f(ρ̄,y) = (ρ̄/y, 1/y)` の計算 |

すべて sorry 0 / AxiomsCheck OK (propext, Classical.choice, Quot.sound) / lint clean。

### ⚠ 次の一手

1. **§3 (4) 本体**。骨格は 2026-08-01 の設計調査どおり:
   `(1)+(3)` から `a ∈ F^#` の等式 → (2) で `f(ω̄, x+a) = (ω̄/(a+ζ⁻¹), γ(a))` →
   第 2 成分の比較で `(∗∗) (a²+1)γ(a) = x + a + (1+ζ⁻²)/(a+ζ⁻¹)` →
   `a = 1` で `x = ζ⁻¹` → `γ(a) = 1/(a+ζ⁻¹)` → 残り 1 点を `ω ↦ ω⁻¹`, `ζ ↦ ζ⁻¹` で。
   ⚠ **`Q ≃* RootGroup q` の具体的な形が要る**: 現在の
   `nonempty_mulEquiv_rootGroup` は `Nonempty` (存在) しか言わない。(4) の計算は
   `f` (Ch. IV の写像) を座標に写して行うので、**同型を 1 つ固定して
   `Q` 側の既知の等式 (§2, §3 (1)-(3)) を座標に翻訳する**層が要る。
2. `5 ≤ |F|` の供給 (場合分けは下記に既述)。
3. 軌道代表系 `ω_1,…,ω_n` の形式化。

## セッション総括 (2026-07-31)

**Ch. IV で形式化されたもの** (すべて sorry 0 / AxiomsCheck OK / lint 0):

| leaf | 行数 | 内容 |
|---|---|---|
| `OddOrder/GroupTheory/RankOneBNPair.lean` | 784 | §1 全体 — `Setup`/`IsFGH`、(H1)-(H6)、Lemma (置換モデル)、`⟨f,j⟩` の `D`-軌道作用 |
| `…/Suzuki/RankOneSetup.lean` | 122 | (A1)-(A3) → `Setup` の橋渡し |
| `…/Suzuki/PSU3Preliminary.lean` | 1025 | §2 (1)-(7)、ファイバー評価 (集合版)、`\|D:K\|`、`D = KW`、翻訳の群論部分、(9) の部品 |
| `…/Suzuki/PSU3OrbitCount.lean` | 778 | モデル数値部分 — `μ(KW)` の位数、`n = (q+1)/\|W\|`、`Φ`、翻訳、段 (8)、段 (9) |

**到達点**: §1 完了 + 橋渡し + §2 (1)-(9) 完了。

**次の一手**: 段 (10)。`exists_mulEquiv_bilinearTwistedProduct` を直接使って
`y = (0, α)` (`α ∈ F`) と `coord = Φ.quotient` を取り、正規化仮説
(`f(ω) = (ωy)^ζ`) の下で `b^{1+θ} = α + a^{-(1+θ)} ⟹ f(ωs^a) = (f(ωs^b)s^a)^{ζa⁻²}`
を示す。⚠ **(10) 以降は座標計算**なので §1-§2(9) とは作業の質が変わる。

**本セッションで訂正したこと** (再発防止):
1. `pdftotext` の上付き落ちで **3 件**の転記ミス ((H3) の指数 / (6) の結論
   `a ∉ K` / (5) の表示式欠落)。**すべてページ画像を見て初めて判明**。
   ⟹ Ch. IV の式は必ず 300dpi 画像で確認する。
2. `mu_injective` を**重複証明**して撤回。⟹ Ch. IV に補題を足す前に
   `QuotientKWField` / `ModelIsomorphism` / `StructureOfH/**` を grep する。

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

[0167](closed/0167-pf-part2-ch3-s3-model.md) で Ch. III §3 の Proposition
(`exists_standardModel`) が完成し、`S ⋊ KW ≅ S₁ ⋊ K₁W₁` の標準モデルが手に入った。
Ch. IV はそれを土台に **Theorem A の証明を締める**章:

> In this chapter we conclude the proof of Theorem A. We show in particular that,
> if `V = W`, then `G` is isomorphic either to `PSU(3,q)` or to `PGU(3,q)`.
> The proof is accomplished by an explicit calculation with the operation in `G`;
> it follows a method due to Suzuki.

正本 = `references/peterfalvi/pdftotext/05.6_pp_122_134_Characterization_of_PSU3_q.txt`
+ ページ画像 (式は画像で確定する)。

## §1 The Mappings `f`, `g`, `h` (p. 122-123)

**設定 (一般)**: `L` が集合 `X` に 2 重推移的に作用、`M` = 1 点の固定化群、
`t` は `L − M` の対合、`D = M ∩ M^t`、そして `M = Q ⋊ D` なる `Q ≤ M` がある
(= `L` が階数 1 の split BN-pair を持つ)。このとき

    f, g : Q^# → Q^#,  h : Q^# → D    with    t x t = g(x) h(x) t f(x)

が一意に定まる (`L − M` の元が `a t b` (`a ∈ M`, `b ∈ Q`) と一意表示できることから;
Ch. I §1 Prop 4 と同じ論法)。

**恒等式 (H1)-(H6)** — ⚠ **ページ画像 (p.122) で確定した正本**。
`pdftotext` 抽出は**上付きの `t` を全部落としていた**ので、下の (H3)(H4)(H6) は
テキストと食い違う ([[pdftotext-drops-superscripts]] の再現):

* (H1) `f(x⁻¹) = g(x)⁻¹`
* (H2) `f(f(x)) = x`
* (H3) `f(x^a) = f(x)^{a^t}` (`a ∈ D`)  ← **`a` でなく `a^t`**
* (H4) `h(x^a) = a^{-t} h(x) a` (`a ∈ D`)、`h(x⁻¹) = h(x)^{-t}`、
  `h(f(x)) = h(x)⁻¹`  ← 前 2 つは **`-t` 乗**
* (H5) `j : x ↦ x⁻¹` として `(f ∘ j)³(x) = x^{h(x)⁻¹}`
* (H6) `x, y ∈ Q^#`, `xy ≠ 1` のとき `f(x)g(y) ≠ 1` かつ
  `f(xy) = f(f(x)g(y))^{h(y)^t} f(y)`、`h(xy) = h(x) h(f(x)g(y)) h(y)`
  ← 指数は **`h(y)^t`**

⚠ **`t` による捻れは本質的**: `D = M ∩ M^t` は `t` で正規化されるが**中心化される
とは限らない**ので、`a^t ≠ a` が普通。実際 (H3) を計算すると
`t x^a t = (t a⁻¹ t)(t x t)(t a t)` で `a^t = t a t ∈ D` が自然に現れる
(この計算で OCR の誤りに気づいた)。

保存したページ画像 = `references/peterfalvi/pages/peterfalvi-p{122,123}.png`。

**Lemma**: `L` が `X` に忠実に作用するなら `⟨Q^x | x ∈ L⟩` は `Q` と `f` で、
`L` は `M = Q ⋊ D` と `f` で、それぞれ同型を除いて決まる。

⟹ **§1 は Suzuki の設定に依らない一般命題**なので、最初に着手する上流部品として
適切 (`OddOrder/GroupTheory/` 配下の新 leaf が妥当)。

## §2 以降 (p. 123-134)

`(C1)`/`(C2)` (Ch. III の仮説) を再導入し、`L = G`, `M = H` として `f` を決定していく。
`Q ⋊ W` を Ch. III §3 の `S₁ ⋊ K₁W₁` と同一視する。
* (1) `a ∈ A^#` に対し `f(s^a) = g(s^a) = s^{a⁻¹}`、`h(s^a) = a²`
* (2)-(4) `ω ∈ Q − Q₀` の場合の漸化式
* (以降は未調査 — ページ画像で式を確定してから列挙する)

## repo 側の既存部品 (2026-07-31 初期調査)

| 必要なもの | 所在 | 状態 |
|---|---|---|
| Ch. III §3 の標準モデル | `Appendices/Suzuki/ModelAction.lean` `exists_standardModel` | ✅ (0167) |
| PSU(3,q) の構成・単純性・トーラス | `GroupTheory/SpecificGroups/ProjectiveUnitary/*` | ✅ (要実測) |
| 2 重推移作用の一般論 | `Isaacs/Ch08_PermutationGroups/*` ほか | ❓ 未実測 |
| Ch. I §1 Prop 4 (`L − M` の `a t b` 一意表示) | ❓ | ❓ 未実測 |

## やること

- [x] `f`, `g`, `h` の存在と一意性 — **完了** (2026-07-31,
  `GroupTheory/RankOneBNPair.lean`: `exists_fgh` / `fgh_unique`)
- [~] (H1)-(H6) — (H1)(H3) 完了 (2026-07-31)
- [ ] Lemma (`f` が `L` を決める)
- [ ] §2 以降の調査 (ページ画像で式を確定) → 段ごとに issue 更新
- [ ] Theorem A の結論への接続

## 参照

* pp. 122-134 = `references/peterfalvi/pdftotext/05.6_pp_122_134_Characterization_of_PSU3_q.txt`
* 上流 = [0167](closed/0167-pf-part2-ch3-s3-model.md) (Ch. III §3)
* Coq 併読 = `coq/theories/PFsection*.v` の該当箇所 (対応表 = `notes/meta/coq_odd_order_reference.md`)
