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

## 2026-08-01 (9): p.130-131 精読 — (4) は **`χ = c·N`** を要求する

### ⚠ 発見: 書籍は (3)→(4) でユニタリ座標へ**暗黙に**移っている

p.130 (3) までの座標は Ch. III §3 のモデル (`ω² = (0,α)`, `α ∈ F`)。ところが
p.130 (4) の主張は

> **(4)** For all `y ∈ E` such that `y + y^q = ω̄^{1+q}`, `f(ω̄,y) = (ω̄/y, 1/y)`.

で、第 2 成分が **`E` の元** (トレース条件付き) になっている。p.131 では
「As `ω̄^{1+q} = ζ + ζ⁻¹` by (3)」と書かれ、(3) の `α` が **`ω̄^{1+q}`**、
すなわち**平方写像がエルミートノルムそのもの**として使われている。

⟹ 書籍が Appendix III Prop 1 (`θ = 1` ⟹ type B の平方写像 = 二次拡大のノルム、
repo では `FieldModel.mul_conj`) を暗黙に適用して座標を張り替えている。
**これが (4) の前に埋めるべき行間**。

### ⚠ 一般の分類だけでは足りない (今セッションの橋渡しの限界)

`exists_addEquiv_norm_of_anisotropic` が与える `f₀` は **`F`-線型**にすぎない。
一方 (2)(4) の計算は `ω̄/(a² + ζ⁻¹)` のように **`E` の乗法**を使う (`a ∈ F`,
`ζ ∈ μ(W)` の和は `E` の一般の元)。`f₀` が `E`-線型でないと §2/§3 の等式が
座標に移らない。⟹ 必要なのは「モデル自身の `E` 座標で `χ` がノルムに比例する」
こと。

### 🎯 `χ = χ(1)·N` は 3 点評価で出る (2026-08-01 に机上で確定)

`ψ(x) := χ(x) + N(x)·χ(1)` と置く (`N(x) = x^{1+q}`)。両項とも `F`-二次形式
(`F` 上 `λ²` でスケール) なので `ψ` も `F`-二次形式。`μ ∈ μ(W)`, `μ ≠ 1` を取ると:

* `ψ(1) = χ(1) + χ(1) = 0`。
* `ψ(μ) = χ(μ) + N(μ)χ(1) = χ(μ) + χ(1) = 0` — `N(μ) = μ^{1+q} = 1`
  (`mu_W_normOne`) と **`χ(μ·1) = χ(1)`** から。
* `ψ(μ²) = 0` — 同上 (`μ² ∈ μ(W)`)。

そして `{1, μ}` は `F`-基底 (`μ ∉ F`: `μ^{q+1} = 1` かつ `μ^{q-1} = 1` なら
`gcd(q+1,q-1) = 1` で `μ = 1`)。`μ² = a + bμ` と書くと `a ≠ 0`, `b ≠ 0`
(どちらか 0 なら `μ ∈ F`)。基底表示 `ψ(x + yμ) = A x² + B xy + C y²` で
`A = ψ(1) = 0`, `C = ψ(μ) = 0`, そして `ψ(μ²) = B ab = 0` ⟹ `B = 0`。
⟹ **`ψ ≡ 0`、すなわち `χ(x) = χ(1)·x^{1+q}`**。

⚠ 数え上げ (「非零な 2 変数二次形式の零点は `≤ 2(q-1)` 個」) は不要で、
**3 点の評価だけ**で済む (= 「3 本の相異なる直線上で消える 2 変数二次形式は 0」)。

**残る入力は 1 つだけ**: **`χ(μ) = χ(1)` for `μ ∈ μ(W)`** = `W` が `Z(Q)` に
自明に作用すること (PSU(3,q) では `y ↦ N(λ)y` で `N(λ)=1` ゆえ自明)。
`exists_standardModel` は中心成分のスケール `hΘc` を結論に出していないので、
`hyp.exists_modelScalarHom` を直接使うか、`W ≤ C(Q₀)` を repo から取る。

### ⟹ そのあとは全部繋がる

`χ = c·N` なら `c = e²` (`e ∈ F`, Frobenius 全射) で `χ(x) = N(e·x)` ⟹
分類写像は**乗法 `x ↦ e·x`、すなわち `E`-線型**に取れる ⟹ `KW` 作用がそのまま
移る ⟹ §2/§3 の等式を座標に翻訳できる ⟹ (4) の計算に入れる。
(今セッションの `nonempty_mulEquiv_of_diag` / `toTwistedProduct` はそのまま使う。
一般の分類 `exists_addEquiv_norm_of_anisotropic` は `|W| = 1` の退化ケースや
他章のために残す。)

### ⚠ 次の一手 (この順で)

1. `χ(μ) = χ(1)` (`μ ∈ μ(W)`) の供給 — `exists_modelScalarHom` の `hΘc` または
   `W` の `Q₀`-中心化から。
2. `χ = χ(1)·N` (上記 3 点評価)。⚠ `μ(W) ≠ 1` は §3 の仮説 `ζ ∈ W^#` から。
3. `Q ≃* RootGroup q` を **`E`-線型な座標**で取り直す (第 1 成分 = `x ↦ e·x`)。
4. §3 (4) 本体 = p.131 の計算 (`(∗∗)` → `x = ζ⁻¹` → `γ(a) = 1/(a+ζ⁻¹)`)。
5. §3 (5) = p.131 後半 (`KW`-軌道 + (H3) で全 `ρ` へ)。

## 2026-08-01 (10): `χ = c·N` 完成 — 座標の張り替えが閉じた

前節の設計どおり実装完了 (2 コミット)。

| 補題 | 場所 | 内容 |
|---|---|---|
| `eq_one_of_sq_eq_one` | `AnisotropicNormForm` | 標数 2 で `z² = 1 ⟹ z = 1` |
| `notMem_frobFixedSubfield_of_normOne` | 同 | `μ^{q+1} = 1`, `μ ≠ 1` ⟹ `μ ∉ F` |
| `cocycle_diag_add` / `_smul` / `cocycle_polar_left` / `_right` | 同 | `φ` → (`χ`,`B`) の橋 (2 系で共有) |
| 🎯 `eq_norm_smul_of_normOne_invariant` | 同 | **3 点評価で `χ = χ(1)·N`** |
| `cocycle_diag_eq_norm_smul_of_normOne_invariant` | 同 | その `φ` 版 |
| `cocycle_invariant_W` | `PSU3RootGroupModel` | 余輪体は `μ(W)` で不変 (`centreQuadraticMap_smul_KW` を `hdiagscale` へ) |
| 🎯 `cocycle_diag_eq_norm` | 同 | **`φ(x,x) = φ(1,1)·x^{1+q}`** (`ζ ∈ W^#` から) |

⟹ 書籍が (3)→(4) で暗黙に行う座標の張り替えが、**モデルの `E` と `KW` 作用を
動かさずに**得られた。

### ⚠ 次の一手 — ユニタリ座標を `M.E` 上で持つ

(4) の計算に入るには `Q ≃ {(a,b) ∈ E × E : Tr b = N(a)}` が `M.E` 上で要る。
現在 `RootGroupTwistedCoordinates` / `toTwistedProduct` は `Field n` 専用。2 案:

* **(a)** `RootGroupTwistedCoordinates` を任意の二次拡大 `E` に一般化し
  (`star` → `qFrobenius E 2 m`)、`HermitianRootGroup E m` を新設。
  `RootGroup n` はその特殊化 (≃* を 1 本書く)。特殊化債務の解消にもなる。
* **(b)** `BilinearTwistedProduct φ` 座標のまま書籍の式を翻訳
  (`y = z + u·N(ω̄)`)。新型は不要だが式が汚い。

⟹ **(a) を採る**のが筋 (章末の `G ≅ PSU(3,q)` でも `Field n` 側が要るので、
両方を繋ぐ形にしておく)。

その後: (4) 本体 (p.131 の `(∗∗)` 計算) → (5) (`KW`-軌道 + (H3)) → 章の結論。

## 2026-08-01 (11): 🎯 §3 (4) の舞台が整った — `Q` のユニタリ座標

新型 (`HermitianRootGroup`) は**作らなかった**。`RootGroup` は 632 箇所で使われて
おり型の付け替えは churn が大きすぎるので、**座標関数**として供給した。

| 補題 | 場所 | 内容 |
|---|---|---|
| `frobPow_frobPow` / `norm_mem_frobFixed` / `norm_cocycle` | `Algebra/HermitianCocycle.lean` (新) | 任意の二次拡大 `E` での基本 |
| `hermitianBilin` / `correctedBilin` / `hermitianCocycle` | 同 | `x ȳ + u Tr(x ȳ)` を `F` 値双線型に。`hermitianCocycle_diag` で対角 = ノルム |
| `unitaryCoord` | `Suzuki2Groups/UnitaryCoordinates.lean` (新) | 第 2 座標 `y = z + u a ā` |
| `unitaryCoord_frobTrace` | 同 | **`Tr y = a ā`** |
| 🎯 `unitaryCoord_mul` | 同 | **`(a,y)(c,w) = (a+c, y+w+a c̄)`** = PSU(3,q) の積 |
| `ofUnitary` / `eq_of_unitaryCoord_eq` | 同 | 逆向きと一意性 |
| `exists_mulEquiv_of_diag` | `TwistedProductComparison` | 対角比較の同型を**座標作用込み**で (強化) |
| 🎯 `exists_unitaryModel` | `PSU3RootGroupModel` | **`Q ≃* BilinearTwistedProduct (hermitianCocycle)`**、商座標は `e` 倍 (`E`-線型)、**中心不動** |

⟹ 書籍の `f(ρ̄,y) = (ρ̄/y, 1/y)` (`Tr y = ρ̄^{1+q}`) が **`Q` の上で直接書ける**。
`E`-線型なリスケールなので §2/§3 の等式 (`E` の乗法・`KW` のスカラー作用) が
そのまま生き残る。

### ⚠ 次の一手 = §3 (4) 本体 (p.131)

書くべき命題 (`ω = (ω̄, x)`, `Tr x = ω̄^{1+q}`, `ζ ∈ W^#`, 仮説は §2 から):

> `Tr y = ω̄^{1+q}` なる全ての `y ∈ E` で `f(ω̄,y) = (ω̄/y, 1/y)`。

p.131 の筋 (すべて `E` の計算):
1. (1)+(3) から `a ∈ F^#` に対し `f(ω̄, x+a)^{ζ⁻¹a}(0,a) = f(ω̄,x+a)^{ζ⁻²}(ω̄,x)^{ζ⁻¹}`。
2. (2) より `f(ω̄, x+a) = (ω̄/(a+ζ⁻¹), γ(a))` (`γ(a) ∈ E`)。
3. 第 2 成分を比較して **`(∗∗) (a²+1)γ(a) = x + a + (1+ζ⁻²)/(a+ζ⁻¹)`**
   (`ω̄^{1+q} = ζ+ζ⁻¹` = (3) を使う)。
4. `a = 1` で `x = ζ⁻¹`。すると `(∗∗)` は `(a²+1)γ(a) = (a²+1)/(a+ζ⁻¹)` に化け、
   `a ∈ F − {0,1}` で `γ(a) = 1/(a+ζ⁻¹)`。
5. `y = ζ⁻¹` は `(ω̄,y) = ω` 自身、残る 1 点 (`y = ζ⁻¹+1`) は `ω ↦ ω⁻¹`,
   `ζ ↦ ζ⁻¹` の対称性で潰す (`ζ+1 ≠ ζ⁻¹+1`)。

⚠ 道具立て: `unitaryCoord` / `unitaryCoord_mul` / `ofUnitary` /
`eq_of_unitaryCoord_eq` (座標)、`stepOne_chain` / `stepTwo_linear` / `stepThree`
(§3 (1)-(3))、`exists_unitaryModel` (座標系の供給)。
その後 (5) = p.131 後半 (`KW`-軌道 + (H3) で全 `ρ` へ)。

## 2026-08-01 (12): ユニタリ座標の計算則 6 本

(4)(5) の計算が繰り返し使う道具を先に揃えた (`UnitaryCoordinates.lean` /
`HermitianCocycle.lean`):

| 補題 | 内容 | (4)(5) での役割 |
|---|---|---|
| `unitaryCoord_central` / `_one` | 中心元の座標 = 中心成分 | `(0,a)` の扱い |
| 🎯 `unitaryCoord_mul_central` | **中心元倍 = 座標の平行移動** | `ω s^a` の第 2 座標が `x + a` |
| `unitaryCoord_sq` | `ω² = (0, ω̄^{1+q})` | §3 (3) の形 |
| `unitaryCoord_inv` | **`(a,y)⁻¹ = (a, ȳ)`** (`u^q = u+1` が効く) | `ω ↦ ω⁻¹` の対称性 (最後の 1 点潰し) |
| `unitaryCoord_of_scaled` | **`(a,y)^d = (d a, d^{1+q} y)`** | (5) の `KW`-軌道 |
| `hermitianCocycle_smul` | `φ(dx,dy) = d^{1+q} φ(x,y)` | 上記の余輪体側 |

### ⚠ 次セッションはここから — (4) 本体の配線

**確認済の接続点**:
* §2/§3 の等式は **`M.coord`** (商座標) で書かれている (`stepTwo_linear` 参照)。
  一方 `exists_unitaryModel` の `Ψ` は `Φ` 経由。⟹ **`(Φ ρ).quotient = M.coord …`**
  が要る。これは `exists_mulEquiv_bookCocycle` の `hquot` にあるが
  **`exists_standardModel` は結論に出していない**。
  ⟹ (a) `exists_standardModel` に `hquot` を結論として足す (中で既に得ている) か、
  (b) (4) の命題の仮説に取る。**(a) が筋** (消費者は Ch. IV だけのはず — 要 grep)。
* 書籍 (2) の `a²` と (4) の `a` の食い違いは**パラメータ化の差**:
  `s^a` の中心座標は `μ(a)^d = μ(a)²` (`θ|_F = 1` より)。(4) は中心座標で
  パラメータ化しており、`F` 上 2 乗は全単射なので同値。

その後の筋は前節 (11) の 1.–5. のとおり。

## 2026-08-01 (13): 座標系の接続完了 + (4) 実装前の設計確定

### landing

* **`exists_standardModel` の結論に 2 本追加** (証明内で既に得ていた;
  consumer が無いので破壊的でない):
  * `hquot` — `(Φ e).quotient = M.coord …`。§2/§3 は `M.coord` で書かれているので必須。
  * `hW` — 余輪体は `μ(W)` で不変。
* 🎯 `exists_unitaryModel_coord` — **§3 (4) が働くインタフェース**。仮説は
  `exists_standardModel` の出力 + §3 (3) の `θ = 1` だけ。結論は
  「`Q` のユニタリ座標 + 第 1 座標 = 書籍の `α` の `e` 倍 + 中心不動」。

### ⚠⚠ (4) 実装前に判明した設計事項 — **共役作用を座標に降ろす層が要る**

p.131 の (4) の計算は `f(ω̄,x+a)^{ζ⁻¹a}(0,a) = f(ω̄,x+a)^{ζ⁻²}(ω̄,x)^{ζ⁻¹}` を
**座標で展開**する。すなわち `(x,y)^d = (d x, d^{1+q} y)` (共役 = スカラー作用) が
座標レベルで要る。現状:

| 成分 | 供給 | 状態 |
|---|---|---|
| 商座標 `α(ρ^d) = μ(d)·α(ρ)` | `M.coord_act` | ✅ (§2/§3 が既に使用) |
| 中心座標、`k ∈ K` | `hequiv'` (`ι'(z^k) = μ(k)^d ι'(z)`) | ⚠ `exists_standardModel` が**未露出** (`∃ d', …` の中) |
| 中心座標、`v ∈ W` | `W_centralizes_Q0` (`KCyclic.lean:122`) | ✅ 存在 |
| ユニタリ第 2 座標 `y ↦ N(μ(d))·y` | 上 2 つ + `unitaryCoord_of_scaled` | ⬜ 未 |

⚠ **`N(μ(k)) = μ(k)^{1+q} = μ(k)²`** (`μ(k) ∈ F`) が中心のスケール `μ(k)^d = μ(k)²`
(§3 (3) の `θ|_F = 1` から) と**一致する**ので辻褄が合う。`v ∈ W` 側は
`N(μ(v)) = 1` と中心固定で一致 ✅。

⚠ **`u ∈ inducingIdAuts` の補正について**: `exists_standardModel` は共役作用と
スカラー作用の一致を「`u` 共役の後の**像の一致**」でしか言っていない
(Zassenhaus の段)。`inducingIdAuts` は商・核の両方に恒等に誘導する自己同型
(= `(x,z) ↦ (x, z + λ(x))`) なので、**商座標には影響しないが中心座標をずらす**。
⟹ (4) の第 2 成分の計算に入る前に、
**「共役作用が座標で `(μ(d)x, N(μ(d))z)` になる」を pointwise で確立する層**が要る。
供給源は上表の 2 行目・3 行目 (どちらも `Φ` を通さず `ι'` / 群レベルで書けるので
`u` の補正を経由しない) — すなわち **`hequiv'` を `exists_standardModel` に露出し、
`W_centralizes_Q0` と合わせて `Φ` の中心座標の変換則を直接示す**のが正しい筋。

### ⚠ 次の一手 (この順)

1. `exists_standardModel` に `hequiv'` (中心座標の `K`-スケール) を露出。
2. `Φ` の**中心座標の共役変換則**を確立 (`K` は `μ(k)²` 倍、`W` は不変)。
   ⟹ `unitaryCoord_of_scaled` と合わせて **`(x,y)^d = (μ(d)x, N(μ(d))y)`**。
3. (4) 本体: p.131 の `(∗∗)` → `x = ζ⁻¹` → `γ(a) = 1/(a+ζ⁻¹)` → 残り 1 点。
4. (5): `KW`-軌道 + (H3)。

## 2026-08-01 (14): ⚠ 前節の計画を訂正 — `u` 補正の正しい迂回路

### landing

`exists_standardModel` の結論に `∃ d : ℤ` の下で 2 本追加:
* `Q` 側の中心スケール `(Φ (z^k)).central = μ(k)^d (Φ z).central` (`z ∈ Z(Q)`)
* モデル側 `(Θ kv p).central = μ(kv.1)^d · p.central` (= `hΘc`)

### ⚠⚠ 訂正: 前節 (13) の「`hequiv'` を露出すれば済む」は**誤り**

`hequiv'` は **`z ∈ Z(Q)` にしか効かない**。(4) が要るのは一般の `ρ ∈ Q` の
**第 2 座標**の共役変換則で、それは `Φ` を通した共役作用そのもの。ところが
`exists_standardModel` はそれを「`u ∈ inducingIdAuts` 共役後の**像の一致**」でしか
言っていない。

**正しい迂回路** (机上で確認):
1. **`u` を `Φ` に吸収する**。`Φ' := Φ.trans u` と置くと
   `MulAut.congr Φ' α = conj u (MulAut.congr Φ α)` なので、結論の像の等式が
   そのまま `((MulAut.congr Φ').comp conjQHom).range = Θ.range` になる。
   ⚠ `u ∈ inducingIdAuts` は商にも核にも恒等を誘導するので、
   **`hquot` も中心元の像も `Φ'` で不変** (余輪体 `φ` も同じ)。
2. **像の等式から pointwise へ**: 各 `kv` について
   `(MulAut.congr Φ') (conjQHom kv) = Θ kv'` なる `kv'` が取れる。両辺の**商への
   作用**を比べると `μ(kv') = μ(kv)`、`M.mu` の単射性 (`hmu`) で **`kv' = kv`**。
   ⟹ **`Φ' (d ρ d⁻¹) = Θ kv (Φ' ρ)`** (pointwise)。
3. `Θ kv` の 2 座標は `hΘq` (商 = `μ(kv)` 倍) と `hΘc` (中心 = `μ(kv.1)^d` 倍) で
   既知 ⟹ `unitaryCoord_of_scaled` と合わせて
   **`(x,y)^d = (μ(kv)·x, N(μ(kv))·y)`**。
   ⚠ ここで `N(μ(kv)) = μ(kv)^{1+q} = μ(kv.1)^d` が要る:
   `μ(kv) = μ(k)μ(v)`, `N(μ(v)) = 1` (`mu_W_normOne`), `N(μ(k)) = μ(k)²`
   (`μ(k) ∈ F`)、そして `μ(k)^d = μ(k)²` (§3 (3) の `θ|_F = 1`) で一致する。

⟹ **次の一手 = 上記 1.–3. の層** (`PSU3RootGroupModel.lean` に追加)。
その後 (4) 本体 (p.131) → (5)。

## 2026-08-01 (15): 🎯 共役の pointwise 化 + 🎯🎯 **`φ` はエルミート余輪体そのもの**

### landing

🎯 `Hypothesis.exists_modelEquiv_conj` — **共役作用 = スカラー作用を pointwise に**。
Ch. III §3 は像の一致 (Zassenhaus 段) しか言わないので:
1. **`u` を座標写像に吸収** (`Φ' := Φ ∘ u`; `MulAut.congr Φ' α = u (…) u⁻¹`)。
   `u ∈ inducingIdAuts` は両端に恒等を誘導 ⟹ `Φ'` の商座標は不変・中心も不動。
2. **添字は商作用で決まる** (`μ(kv') = μ(kv)` + `M.mu` 単射) ⟹ `kv' = kv`。
⟹ **`Φ' (dρd⁻¹) = Θ kv (Φ' ρ)`**。`exists_standardModel` に露出済の
`hΘq`/`hΘc` と合わせて 2 座標とも明示スカラー。

### ⚠⚠ さらに追跡して判明 — **`Ξ` 経由は不要だった**

`exists_unitaryModel` の `Ξ` (= `equivOfCommonSquareMap`) は中心座標を
`κ(x)` だけずらすので、**共役作用がエルミート側で厳密なスカラー作用にならない**
(ずれ `λ(x) = κ(μx) + N(μ)κ(x)` は加法的で `inducingIdAuts` の分だけ残る)。
コホモロジー的に消す (奇数位数 + 2-群で `H¹ = 0`) 手もあるが、**その必要は無い**:

🎯🎯 **`φ` は `u` を選び直せばエルミート余輪体と厳密に一致する** (机上で確定):

`c := φ(1,1)`, `D(x,y) := φ(x,y) + c·x y^q` と置く。
* `D` は `F`-双線型で **交代的** (`D(x,x) = φ(x,x) + c N(x) = 0`、`χ = c·N` より)
  ⟹ 標数 2 で**対称**でもある。
* `Tr u₀ = 1` なる `u₀` を取ると `u₀ ∉ F` で `{1, u₀}` は `F`-基底。
  基底の 4 組で突き合わせると
  **`D(x,y) = β·Tr(x y^q)`** (`β := D(1,u₀)`)。
  (`Tr(1·1^q) = 0`, `Tr(1·u₀^q) = Tr u₀ = 1`, `Tr(u₀ u₀^q) = Tr(N u₀) = 0`。)
* `φ` が `F` 値であることから `Tr β = c`。⟹ `u := β/c` は **`Tr u = 1`**。
* ⟹ **`φ(x,y) = c·(x y^q + u·Tr(x y^q)) = hermitianCocycle_u (e x) (e y)`**
  (`e ∈ F`, `e² = c`; `e^{1+q} = e²`)。

⟹ `congrEquiv (e·) id` が**そのまま**同型を与える (`equivOfCommonSquareMap` 不要)。
しかも第 1 座標は `e` 倍・中心は恒等なので、**共役作用がエルミート側でも厳密に
スカラー作用のまま**。(4) の計算が素直に通る。

### ⚠ 次の一手

1. `exists_hermitianCocycle_eq` — 上記の「`φ = c·H_u`」を実装
   (`AnisotropicNormForm.lean` / `HermitianCocycle.lean` 層、~120 行)。
   ⚠ 入力は `χ = c·N` (= `cocycle_diag_eq_norm`) と `F`-双線型性だけ。
2. `exists_unitaryModel` を `congrEquiv` 版に差し替え (対角比較経由を廃止)。
   ⟹ `exists_mulEquiv_of_diag` は他用途に残す。
3. 共役のユニタリ座標表示 `(x,y)^d = (μ(d)x, N(μ(d))y)`
   (`exists_modelEquiv_conj` + `unitaryCoord_of_scaled`;
   `N(μ(kv)) = μ(kv.1)^d` は `mu_W_normOne` + `mu_K_frobFixed` + `θ|_F = 1` から)。
4. (4) 本体 (p.131) → (5)。

## 2026-08-01 (16): 🎯🎯 `exists_hermitianCocycle_eq` landing — セッション区切り

前節 (15) で机上確定した「`φ` は `u` を選び直せばエルミート余輪体と厳密に一致」を
実装完了 (`Algebra/HermitianCocycle.lean`)。

`exists_hermitianCocycle_eq`: `φ` が `F`-双線型 + `φ(x,x) = c·x^{1+q}`
(`c = φ(1,1) ≠ 0`) ⟹ **`∃ u, Tr u = 1 ∧ φ(x,y) = c·(x y^q + u Tr(x y^q))`**。

証明の骨: `D x y := φ(x,y) + c x ȳ` が交代的 (⟹ 標数 2 で対称) →
トレース 1 の `w` で `{1,w}` を基底に取り、両側を展開して `D = β·Tr(x ȳ)` →
`φ` の `F` 値性から `Tr β = c` → `u := β/c`。

### 📊 §3 (4) 基盤の到達点 (このセッション、計 14 コミット)

| 層 | 主結果 | 状態 |
|---|---|---|
| 分類 | `exists_addEquiv_norm_of_anisotropic` (非等方形式 ≅ ノルム形式) | ✅ |
| 鋭い版 | `eq_norm_smul_of_normOne_invariant` / `cocycle_diag_eq_norm` (`χ = χ(1)·N`) | ✅ |
| **厳密版** | **`exists_hermitianCocycle_eq` (`φ = c·H_u`)** | ✅ |
| 捻れ積比較 | `exists_mulEquiv_of_diag` (座標作用込み) | ✅ |
| ユニタリ座標 | `unitaryCoord` + 積則 + 計算則 6 本 | ✅ |
| `Q` への適用 | `exists_unitaryModel(_coord)` | ✅ (要 `congrEquiv` 版へ差し替え) |
| 共役の pointwise 化 | `exists_modelEquiv_conj` | ✅ |
| (4) 本体 | p.131 の `(∗∗)` 計算 | ⬜ |

### ⚠ 次セッションはここから

1. **`exists_unitaryModel` を `congrEquiv` 版に差し替え** — `exists_hermitianCocycle_eq`
   で `u` を選べば `φ (x) (y) = hermitianCocycle_u (e x) (e y)` なので
   `congrEquiv (e·) id` がそのまま同型。⟹ 中心不動 + スカラー作用と可換。
   (対角比較版 `exists_mulEquiv_of_diag` は他用途に残す。)
   ⚠ `hermitianCocycle m hcard hu` の `u` は**この定理が返す `u`** を使うこと。
2. 共役のユニタリ座標表示 `(x,y)^d = (μ(d)x, N(μ(d))y)`
   (`exists_modelEquiv_conj` + `hΘq`/`hΘc` + `unitaryCoord_of_scaled`;
   `N(μ(kv)) = μ(kv.1)^d` は `mu_W_normOne` + `mu_K_frobFixed` + `θ|_F = 1`)。
3. (4) 本体 (p.131) → (5)。

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
- [x] Lemma (`f` が `L` を決める) — **完了** (2026-08-01, `GroupTheory/RankOneBNPairRigidity.lean`)
- [ ] §2 以降の調査 (ページ画像で式を確定) → 段ごとに issue 更新
- [ ] Theorem A の結論への接続

## 参照

* pp. 122-134 = `references/peterfalvi/pdftotext/05.6_pp_122_134_Characterization_of_PSU3_q.txt`
* 上流 = [0167](closed/0167-pf-part2-ch3-s3-model.md) (Ch. III §3)
* Coq 併読 = `coq/theories/PFsection*.v` の該当箇所 (対応表 = `notes/meta/coq_odd_order_reference.md`)

## 2026-08-01 (17): unitary model を `congrEquiv` 化、共役をユニタリ座標へ、(4) の `(∗∗)` 完成

### (a) `exists_unitaryModel` を `congrEquiv` 版に差し替え (完了)

`exists_hermitianCocycle_eq` で `φ x y = c·H_u(x,y)` (`c = φ(1,1)`) が取れるので、
`c = e²` (`e ∈ F`) と置けば `H_u(e x, e y) = e^{1+q} H_u(x,y) = φ x y` ちょうど。
⟹ 比較は素の `congrEquiv (x,w) ↦ (e x, w)`。

対角比較版との差:
* 両座標が明示 (`(Ψ ρ).quotient = e·(Φ ρ).quotient`, **`(Ψ ρ).central = (Φ ρ).central`**)
* 中心が **pointwise** 不動 (以前は `Φ.symm ⟨0,w⟩` の像だけ)
* 商座標がスカラー倍 ⟹ `E`-スカラー作用と可換

`u` は定理側が選ぶので結論が `∃ u, ∃ hu, ∃ e, ∃ Ψ, …` に変わった
(`exists_unitaryModel_coord` も同型に変更、`{u} (hu)` 引数は削除)。
`hbil` (θ=1 版の `F`-双線型性) が新たな入力。

### (b) `centralScale_eq_norm_of_quotientScale` (`UnitaryCoordinates.lean`)

**余輪体の対角がノルムの 0 でない定数倍なら、商座標を `a` 倍する自己同型は
中心座標を `a^{1+q}` 倍する。**

証明は `(1,0)` の平方 1 本: 平方は中心で座標 `φ(1,1)`、その像は中心で座標
`φ(a,a) = φ(1,1)·a^{1+q}`。

⟹ モデル作用 `Θ` の中心スカラーは書籍の `μ(k,1)^d` という**不透明な冪**だったが、
`d` を知らずにノルムと同定できる (`mu_W_normOne` + `mu_K_frobFixed` 経由で
`d = 2` を示す必要が無い)。

### (c) `exists_unitaryModel_conj` — p.131 の共役公式

    (a, y)^{kv} = (μ(kv)·a, μ(kv)^{1+q}·y)

を `Ψ` の両座標について取得 ((a)+(b)+`unitaryCoord_of_scaled`)。

### (d) 段 (4) の算術 — 新 leaf `PSU3InverseFormula.lean`

| 定理 | 内容 |
|---|---|
| `star_of_secondEntry` | 第 2 成分比較 ⟹ `(∗∗) (a²+1)γ(a) = x + a + (1+ζ⁻²)/(a+ζ⁻¹)` |
| `eq_and_inv_of_star` | `(∗∗)` ⟹ `x = ζ⁻¹` かつ `γ(a) = 1/(a+ζ⁻¹)` (`a ∈ F − {0,1}`) |
| `gamma_eq_inv_of_secondEntry` | 上 2 つの合成 (`γ(a) = 1/(x+a)` = 書籍の `1/y`) |

`eq_and_inv_of_star` は `w := ζ⁻¹` について「部分体 `S` の外」しか使わないので
一般の `Subfield E` + `w ∉ S` で述べた (再利用可)。

⚠ **`a = 1` (= `y = ζ⁻¹+1`) は原理的に除外される** — 書籍もそこは
`ω → ω⁻¹`, `ζ → ζ⁻¹` の対称性で回収している (`f(ω⁻¹) = ω^{ζ⁻¹}` ゆえ
`(ω', ζ') = (ω⁻¹, ζ⁻¹)` が §3 の仮説を満たす)。`ζ+1 ≠ ζ⁻¹+1` で被覆完了。

### ⚠ 次セッションはここから (段 (4) の群論部分)

算術は済んだので、残りは**座標公式を段 (1) に流し込む配線**:

1. **`ω s^a` のユニタリ座標が `x + a`** — 中心 `Q₀` の座標写像が `s^a ↦ a`
   (§2 段 (1) の `h(s^a) = a²` と整合するよう `a` は `K` の元の平方)
   であることを確認 (`PSU3CenterCoordinate.lean` を実測すること)。
   ⚠ p.130 の (1)(2) は `a ∈ K` で `a²` が出るが、p.131 は `a ∈ F − {0}` に
   置き換わっている (`s^a = (0, a²)`、平方は標数 2 で全単射)。
2. **段 (1) をユニタリ座標に降ろす** — `exists_unitaryModel_conj` の共役公式 +
   `unitaryCoord_mul` / `unitaryCoord_mul_central` で
   `star_of_secondEntry` の `hchain` を作る。
   ⚠ 共役するスカラーは `ζ⁻¹a` と `ζ⁻²` と `ζ⁻¹`; ノルムはそれぞれ `a²`, `1`, `1`。
3. **段 (2) の第 1 座標**を `stepTwo_linear` から取り出して `f(ω̄, x+a)` の
   商座標を `ω̄/(a+ζ⁻¹)` に固定 (repo の `stepTwo_linear` は
   `(μ(a²) + μ(ζ))·X̄ = ω̄` の形)。
4. `y = ζ⁻¹` (= `a = 0`) の場合を `unitaryCoord_inv` + 共役公式で個別に処理
   (`f(ω) = ω^{-ζ} = (ω̄ζ, ζ)` と `(ω̄/y, 1/y)` の一致)。
5. `ω → ω⁻¹`, `ζ → ζ⁻¹` の対称性で `a = 1` を回収 → 段 (4) 完成 → 段 (5)。

## 2026-08-01 (18): 段 (4) の配線部品が揃った (フルビルド green・lint 0)

(17) の続き。段 (4) を組み立てるための部品を全部落とした。

| 定理 | 所在 | 内容 |
|---|---|---|
| `stepOne_conjQHom` | `PSU3SectionThree` | 段 (1) を `X^{a²ζ}·s^a = X^{ζ²}·ω^ζ` の形に |
| `mu_norm_eq` | `PSU3RootGroupModel` | `μ(k,v)^{1+q} = μ(k,1)²` |
| `unitaryCoord_of_quotient_eq_zero` | `UnitaryCoordinates` | 商座標 0 ⟹ ユニタリ座標 = 中心座標 |
| `unitaryCoord_center` | `PSU3RootGroupModel` | 中心元の `Ψ` ユニタリ座標 = `ν·ι(z)` |
| `secondEntry_of_chain` / `star_of_chain` | `PSU3InverseFormula` | 2 因子等式 ⟹ `(∗∗)` |

### 段 (4) 組み立ての設計図 (辞書つき)

書籍 p.131 の記号 ↔ repo の対応:

| 書籍 | repo |
|---|---|
| `a` (p.131、`F − {0}`) | `Ā := μ(kActor(a²), 1)`  (= `μ(kActor a,1)²`、`mu_kActor_sq`) |
| `ζ⁻¹` | `Z := μ(1, ζ)` |
| `ω̄` | `(Ψ Ω).quotient = e·M.coord(ω)` |
| `x` | `unitaryCoord m u (Ψ Ω)` |
| `γ(a)` | `unitaryCoord m u (Ψ X)`、`X = f(ω s^a)` |
| `s^a = (0,a)` | `unitaryCoord m u (Ψ (s^a)) = ν·ι(s^a) = Ā`  (`ν = ι(s)⁻¹`) |

⚠ **`star_of_secondEntry` / `star_of_chain` の `ζ` には `Z⁻¹` を入れる**
(定理側は `ζ⁻¹` で書いてあるので、書籍の `ζ⁻¹ = Z` に合わせる)。
`hζnorm` は `mu_W_normOne`、`hω : ω̄^{1+q} = ζ + ζ⁻¹` は段 (3) (`stepThree` の
`α = Z + Z⁻¹`) + 余輪体がエルミートゆえ `(Ψω)²` の中心座標が `ω̄^{1+q}`。

4 因子の座標 (`exists_unitaryModel_conj` + `mu_norm_eq`):

| 因子 | 商座標 | ユニタリ座標 |
|---|---|---|
| `L₁ = Ψ(X^{a²ζ})` | `Ā·Z·X̄` | `Ā²·γ` |
| `L₂ = Ψ(s^a)` | `0` | `Ā` |
| `R₁ = Ψ(X^{ζ²})` | `Z²·X̄` | `γ` |
| `R₂ = Ψ(ω^ζ)` | `Z·ω̄` | `x` |

段 (2) (`stepTwo_linear` に `e` を掛ける) が `(Ā + Z)·X̄ = ω̄`、
すなわち `X̄ = ω̄/(Ā+Z)` を与えるので `star_of_chain` の `hR₁q` が埋まる。

### ⚠ 次セッションはここから

1. **`exists_unitaryModel_conj` に `hquot` を足した合成版**を作る
   (段 (2) を `Ψ` の商座標で読むのに要る)。`exists_unitaryModel_coord` と
   `exists_unitaryModel_conj` は入力がほぼ同じなので 1 本に束ねてよい。
2. `ν := ι(s)⁻¹` を入れて `unitaryCoord (Ψ (s^a)) = Ā` を出す
   (`unitaryCoord_center` + `centerCoord_conj` + `mu_K_zpow_eq_sq` + `mu_kActor_sq`)。
3. `stepOne_conjQHom` を `Ψ` で送って `star_of_chain` を適用 → `(∗∗)`。
4. `gamma_eq_inv_of_secondEntry` で `x = Z` と `γ = 1/(x+Ā)` → 段 (4) 本体。
   ⚠ `Ā` は `a ∈ K` を動かすと `F^×` 全体を掃く (`exists_mem_K_mu_sq_inv_eq`
   と同じ論法; 平方は標数 2 で全単射)。
5. `y = Z` (`Ā = 0` に相当、`ω` 自身) と `Ā = 1` の 2 例外を
   `unitaryCoord_inv` / `ω → ω⁻¹, ζ → ζ⁻¹` の対称性で回収 → 段 (5)。

## 2026-08-01 (19): 段 (4) の入力が全部揃った — 残りは組み立て 1 本

(18) の続きで、`star_of_chain` が要求する 4 因子の座標をすべて供給する補題を落とした。

| 定理 | 所在 | 供給する `star_of_chain` の仮説 |
|---|---|---|
| `mu_W_notMem_frobFixed` | `PSU3RootGroupModel` | `hζS` (`ζ⁻¹ ∉ F`) |
| `mu_K_add_mu_W_ne_zero` | `PSU3RootGroupModel` | 分母 `Ā + Z ≠ 0` |
| `centerCoord_conj_eq_mu_sq` | `PSU3RootGroupModel` | `hL₂y` の元 (`c(s^a) = μ(a²)c(s)`) |
| `unitaryCoord_toCenter` | `PSU3RootGroupModel` | `hL₂y` (`ν·c`) |
| `stepTwo_quotient` | `PSU3InverseFormula` | `hR₁q` (`X̄ = ω̄/(Ā+Z)`) |
| `stepThree_quotient_norm` | `PSU3InverseFormula` | `hω` (`ω̄^{1+q} = ν·c(ω²)`) |
| `stepOne_conjQHom` | `PSU3SectionThree` | `heq` |
| `mu_norm_eq` | `PSU3RootGroupModel` | 共役スカラーのノルム |

### 残る組み立て (次セッションの 1 手目)

`stepFour_star`: 上記を全部食わせて `(∗∗)` を出す 1 本。手順:

1. `congrArg Ψ (stepOne_conjQHom …)` + `map_mul` ⟹ `heq : Ψ L₁ * Ψ L₂ = Ψ R₁ * Ψ R₂`。
2. 4 因子の座標を `exists_unitaryModel_conj` の 2 本 + `mu_norm_eq` で計算:
   * `unitaryCoord (Ψ L₁) = μ(kActor ha2,1)²·γ = Ā²γ`
   * `(Ψ L₂).quotient = 0` (`coord_mk_eq_zero_of_mem_Q0` + `hquot` + `hΨq`)
   * `unitaryCoord (Ψ L₂) = ν·c(s^a) = Ā` (`unitaryCoord_toCenter` +
     `centerCoord_conj_eq_mu_sq` + 正規化 `ν·c(s) = 1`)
   * `unitaryCoord (Ψ R₁) = γ`, `(Ψ R₁).quotient = Z²·X̄` (`μ(1,ζ²) = Z²`)
   * `unitaryCoord (Ψ R₂) = x`, `(Ψ R₂).quotient = Z·ω̄`
3. `stepTwo_quotient` で `X̄ = ω̄/(Ā+Z)` を代入 ⟹ `hR₁q` の形
   (`star_of_chain` の `ζ` には `Z⁻¹` を入れる)。
4. `star_of_chain` ⟹ `(∗∗)`。
5. `gamma_eq_inv_of_secondEntry` ⟹ `x = Z`, `γ = 1/(x+Ā)` = 段 (4)。

⚠ `hΘc` を `exists_modelScalarHom` から取るとき、その `d` と
`centerCoord_conj_eq_mu_sq`/`mu_K_zpow_eq_sq` の `d` は同一のものを渡すこと。

### 例外値 (段 (4) の締めと段 (5))

* `Ā = 0` (= `y = Z`, `ω` 自身): `f(ω) = ω^{-ζ} = (ω̄ζ, ζ)` と `(ω̄/y, 1/y)` の一致を
  `unitaryCoord_inv` + 共役公式で直接。
* `Ā = 1` (= `y = Z + 1`): `ω → ω⁻¹`, `ζ → ζ⁻¹` の対称性 (`f(ω⁻¹) = ω^{ζ⁻¹}` ゆえ
  `(ω⁻¹, ζ⁻¹)` が §3 の仮説を満たす) で回収。`ζ + 1 ≠ ζ⁻¹ + 1` で被覆完了。

## 2026-08-01 (20): 🎯🎯 段 (4) 本体 landing

`stepFour_star` / `stepFour` (`PSU3InverseFormula.lean`)。axiom-clean、sorry 0、
lint 0、フルビルド green (4980 jobs)。

### `stepFour_star` — `(∗∗)` の組み立て

段 (1) (`stepOne_conjQHom`) を `Ψ` で送り、4 因子の座標を `star_of_chain` に:

| 因子 | 商座標 | ユニタリ座標 | 根拠 |
|---|---|---|---|
| `Ψ(X^{a²ζ})` | `A·Z·X̄` | `A²·γ` | `hconjy` + `mu_norm_eq` |
| `Ψ(s^a)` | `0` | `A` | `unitaryCoord_toCenter` + `centerCoord_conj_eq_mu_sq` + `ν·c(s)=1` |
| `Ψ(X^{ζ²})` | `Z²ω̄/(A+Z)` | `γ` | `hconjq` + `stepTwo_quotient` |
| `Ψ(ω^ζ)` | `Z·ω̄` | `x` | `hconjq`/`hconjy` |

`A = μ(a²) = μ(kActor(a²),1)`、`Z = μ(1,ζ)` (書籍の `ζ⁻¹`)。

### `stepFour` — 段 (4) 本体

`exists_mem_K_mu_sq_eq` (新規、`exists_mem_K_mu_sq_inv_eq` の逆版) で
`μ(a²)` が `F^×` を掃くことを使い `(∗∗)` を部分体全体へ → `eq_and_inv_of_star`:

* `x = Z`  (書籍の `ω = (ω̄, ζ⁻¹)`)
* `γ(A) = 1/(x + A)`  (`A ∈ F − {0,1}`)

### 設計上の変更

`star_of_secondEntry` 系を書籍の `ζ⁻¹` = **単一文字 `w` (ノルム 1)** で書き直した。
モデルからは `μ(1,ζ)` としてこの形で来るので `ζ⁻¹⁻¹` の書き換えが不要。
`mu_norm_eq` も `kv` 1 個でなく `(k, v)` 2 引数に変更 (`kv.1` が簡約されず
`rw` が刺さらなかったため)。

### ⚠ 次セッションはここから (段 (4) の締め → 段 (5))

1. **`A = 0` (= `ω` 自身)**: `f(ω) = ω^{-ζ}` (仮説 `hf`) をユニタリ座標で読み、
   `(ω̄/y, 1/y)` (`y = Z`) と一致することを示す。
   `unitaryCoord_inv` (`(a,y)⁻¹ = (a,ȳ)`) + `hconjq`/`hconjy` で:
   `ω⁻¹ = (ω̄, Z^q) = (ω̄, Z⁻¹)`、`(ω⁻¹)^ζ = (Z ω̄, Z^{1+q}·Z⁻¹) = (Zω̄, Z⁻¹)`。
   一方 `(ω̄/Z, 1/Z) = (Z⁻¹ω̄, Z⁻¹)`。⚠ **`Zω̄` と `Z⁻¹ω̄` が食い違う** —
   書籍は `ω^{-ζ} = (ω̄,ζ)^ζ` と書いており、`ζ`(書籍) = `Z⁻¹`(repo) なので
   repo では共役スカラーが `Z⁻¹` になるはず。**符号/向きをページ画像で再確認**
   してから実装すること (`conjQHom kv` は `kv⁻¹` 側かもしれない)。
2. **`A = 1`**: `ω → ω⁻¹`, `ζ → ζ⁻¹` で §3 の仮説が保たれること
   (`f(ω⁻¹) = ω^{ζ⁻¹}` = `f_inv_eq`) を使い、`stepFour` をもう一度適用。
   `ζ + 1 ≠ ζ⁻¹ + 1` で被覆完了 (`ζ ≠ ζ⁻¹` は `|W|` 奇数 + `ζ ≠ 1`)。
3. 段 (5) (p.131 下): `KW`-軌道の議論 + §2 段 (8) で全 `ρ ∈ Q − Q₀` に拡張。

## 2026-08-01 (21): 段 (4) 完了 — 元の言葉での `f(ω̄,y) = (ω̄/y, 1/y)`

(20) の続き。段 (4) を**元**の言明まで持っていった。全部 axiom-clean / sorry 0 /
lint 0、フルビルド green (4980 jobs)。

| 定理 | 内容 |
|---|---|
| `stepFour_at_omega` | 除外点 `A = 0` (= `ω` 自身)。仮説 `f(ω) = ζ⁻¹ω⁻¹ζ` から直接 |
| `unitaryCoord_mul_conj` | `ω s^a` のユニタリ座標 = `x + μ(a²)` |
| `eq_or_exists_conj_mul_of_quotient_eq` | ファイバー = `{ω} ∪ {ω s^a : a ∈ K}` |
| `mu_W_ne_inv` | `μ(1,ζ) ≠ μ(1,ζ)⁻¹` (書籍の `ζ+1 ≠ ζ⁻¹+1`) |
| **`stepFour_elem`** | **`(Ψ(f ρ)).quotient = ω̄/y`, `unitaryCoord (Ψ(f ρ)) = 1/y`** |

`stepFour_elem` の除外点は `y = x + 1` の 1 点のみ。

⚠ **向きの確認済み** (前回 note の懸念は不要だった): 書籍の `x^d = d⁻¹ x d` なので
書籍の `ζ` は repo では `ζ⁻¹` 共役、スカラーは `μ(1,ζ)⁻¹`。`conjQHom` (`c x c⁻¹`) と整合。

### ⚠ 次セッションはここから

1. **`ω⁻¹`, `ζ⁻¹` での再実行** — `f(ω⁻¹) = ζ ω ζ⁻¹` (`f_inv_eq`) は
   `(ω', ζ') = (ω⁻¹, ζ⁻¹)` について `f ω' = ζ'⁻¹ ω'⁻¹ ζ'` そのものなので、
   §3 の仮説一式がそのまま満たされる。`stepFour_elem` をもう一度適用し、
   除外点が `x⁻¹ + 1` に移ることを `mu_W_ne_inv` と合わせて
   **ファイバー全体を被覆**する補題にまとめる (= 段 (4) 完結)。
   ⚠ `ω⁻¹` 版の `x'` は `x^q = x⁻¹` (`unitaryCoord_inv` + ノルム 1)。
   ⚠ `stepFour` を再度呼ぶには `hstage3` の `ω⁻¹` 版が要る —
   `(Ψ(ω⁻¹)).quotient = (Ψω).quotient` (標数 2) なので `hstage3` はそのまま使え、
   右辺の `Z + Z⁻¹` は `Z⁻¹ + Z` と可換なだけ。
2. **段 (5)** (p.131 下 — `ρ ∈ Q − Q₀` 全体へ): (H3) で `f(dρ̄, d^{1+q}y) =
   f(ρ̄,y)^{d⁻ᵗ}` を使い、`ρ̄` が `ω̄` の `KW`-軌道にあれば (4) から従う。
   軌道外は §2 段 (8) で `f(ρ)` 側を軌道内に取り直す (p.131 の後半の計算)。
   ⚠ この計算は `(2) of §2` を使う — repo の対応物を先に実測すること。

## 2026-08-01 (22): 段 (4) 完結 + 段 (5) の同変性

### (a) `γ` 添字を廃して点ごとに (refactor)

`(∗∗)` は各 `a` で独立に解けるので、関数 `γ : E → E` を運ぶ必要が無かった。

* `eq_and_inv_of_star` → `eq_of_star_at_one` + `inv_of_star` (各 1 インスタンス)
* `stepFour` → `stepFour_base` (`x = Z`) + `stepFour_pointwise` (各 `a` の値)
* `stepFour_elem` から `γ`/`hγ`/`hγinv` の 3 仮説が消えた
* 未使用の `gamma_eq_inv_of_secondEntry` は削除

### (b) ファイバー全体の被覆 = **段 (4) 完結**

* `quotient_inv_eq` / `unitaryCoord_inv_eq` — 反転は商座標不変・ユニタリ座標 `q` 乗
* **`stepFour_cover`** — `ω` と `ω⁻¹` の 2 回の実行でファイバー全体を被覆
  (漏れる 1 点は基点の座標 +1 で、`x` と `x^q = x⁻¹` は `mu_W_ne_inv` で相異なる)

`ω⁻¹` を基点にできるのは `f_inv_eq` (`f(ω⁻¹) = ζωζ⁻¹`) が `(ω⁻¹,ζ⁻¹)` について
仮説 `f ω' = ζ'⁻¹ω'⁻¹ζ'` そのものだから。

### (c) 段 (5) の同変性

* **`mu_t_twist`**: `μ(k⁻¹,v) = (μ(k,v)^q)⁻¹`。`t` は `K` を反転し `W` を中心化
  するので捻れは `(k,v) ↦ (k⁻¹,v)`、スカラーでは `AZ ↦ A⁻¹Z = ((AZ)^q)⁻¹`。
  ⟹ 書籍 p.131 の指数 `d^{-q}` の正体が確定した。
* **`stepFive_equivariant`**: 逆元公式は `KW`-軌道に沿って伝播する
  (肝は `((d^q)⁻¹)^{1+q} = (d^{1+q})⁻¹`、`d^{q²} = d` による)。

### ⚠ 次セッションはここから (段 (5) の本体)

1. **(H3) を `Ψ` で送る** — `stepFive_equivariant` の `hσq`/`hσy` を供給する層。
   (H3) は `f(x^a) = f(x)^{a^t}` (`RankOneBNPair` の `hThree`)。
   `a = kv ∈ KW` のとき `a^t` は `(k⁻¹, v)` — **`t k t = k⁻¹` (`mul_t_eq_of_mem_KSet`)
   と `t ζ t = ζ` (`conj_t_pow_eq`) から `conjQHom` レベルで示すこと**。
   そのうえで `hconjq`/`hconjy` + `mu_t_twist` で座標に落ちる。
2. **軌道の場合分け** (p.131 下): `ρ̄` が `ω̄` の `KW`-軌道内なら (4)+同変性で終わり。
   軌道外は `ρ` を `ρQ₀` の元に取り替えて §2 段 (8) で `f(ρ)` 側を軌道内に入れ、
   `(ρ̄,x) = f(ω̄',x') = (ω̄'/x', 1/x')` から `ω̄' = ρ̄/x`, `x' = 1/x` を読む。
   ⚠ §2 段 (8) の repo 対応物 (`PSU3OrbitCount`) を先に実測すること。
3. その後 p.131 末の計算 (§2 段 (2) を使う) → 段 (5) 完成 → 段 (6) 以降。

## 2026-08-01 (23): 段 (5) — (H3) の転送・軌道伝播・第 2 ケースの算術

| 定理 | 所在 | 内容 |
|---|---|---|
| `f_conjQHom` | `PSU3InverseFormula` | (H3) を `conjQHom` で: `f(ρ^{(k,v)}) = f(ρ)^{(k⁻¹,v)}` |
| `stepFive_orbit` | 〃 | 逆元公式は `KW`-軌道に沿って伝播 (= p.131 の第 1 ケース完了) |
| `stepFive_secondCase` | 〃 | 第 2 ケースの座標計算 (純算術) |

`f_conjQHom` の肝: `t k t = k⁻¹` は **`KSet` の定義そのもの** (`hk.2`)、
`t v t = v` は `conj_t_pow_eq`。⟹ `KW` 上の `t`-捻れは `(k,v) ↦ (k⁻¹,v)`、
スカラーでは `mu_t_twist` により `d ↦ (d^q)⁻¹`。

`stepFive_secondCase` の内容 (書籍 p.131 最終ディスプレイ):

    a⁻¹ ω̄'/(x' + a⁻¹) = ρ̄/(x+a),   a⁻²/(x' + a⁻¹) + a⁻¹ = 1/(x+a)
      (ω̄' = ρ̄/x, x' = 1/x)

第 2 式で標数 2 (`x + a + x = a`) が効く。

### ⚠ 次セッションはここから (段 (5) の群論側)

1. **§2 段 (8) の repo 対応物を実測** (`PSU3OrbitCount.lean`)。
   書籍: 「`ρ` を `ρQ₀` の元に取り替えれば `f(ρ)` が `ω̄` の `KW`-軌道に入る」。
   軌道の個数 `n = (q+1)/|W|` の議論 (段 (8)) がこれを与える。
2. **§2 段 (2) の repo 対応物**を実測して
   `f(ρ̄, x+a) = f(ω̄', x'+a⁻¹)^{a⁻¹}(0,a⁻¹)` を座標に落とす層を作る
   (`f_mul_conj_distinguishedInvolution` 系が候補)。
3. 1+2+`stepFive_secondCase` で第 2 ケース → `stepFive_orbit` と合わせて段 (5) 完成。
4. その後 p.132 以降 (段 (6)-)。⚠ p.132-134 はまだ**未調査** — ページ画像で
   段の一覧を作るところから。

## 2026-08-01 (24): §2 段 (8)/(2) 実測完了、段 (5) 第 2 ケースの部品

### 実測結果 (辞書)

| 書籍 | repo | 形 |
|---|---|---|
| §2 段 (8) | `PSU3OrbitCount.stepEight` | `orbitOfF` の各ファイバーが `\|W\|` (基点だけ `\|W\|−1`) |
| §2 段 (2) | `PSU3Preliminary.f_mul_conj_distinguishedInvolution` | `f(ω s^a) = f(f(ω) s^{a⁻¹})^{a⁻²} s^{a⁻¹}` (`a ∈ K`) |
| §2 段 (3) | `PSU3Preliminary.f_conj_distinguishedInvolution_mul` | `f(s^a ω) = f(s^{a⁻¹} g(ω))^{h(ω)^t} f(ω)` |

⚠ **§2 段 (2) の指数 `a⁻²` と p.131 の `a⁻¹` は同じもの**: p.131 の助変数は
中心座標 `A = μ(a)²` なので、共役 `x ↦ x^{a⁻²}` は商座標を `μ(a)⁻² = A⁻¹` 倍する。
⟹ p.131 の `f(ρ̄,x+A) = f(ω̄',x'+A⁻¹)^{A⁻¹}(0,A⁻¹)` と一致する
(`stepFive_secondCase` の `a` は書籍の `a` = `A`)。

### 追加した部品

* **`exists_mem_Q0_orbitOfF_eq`** — 段 (8) から「空のファイバーが無い」(`|W| > 1`)
  ⟹ `ρ` を `ρQ₀` 内で取り替えて `f(ρ)` を任意の `KW`-軌道に入れられる
* **`inverseFormula_symm`** — 逆元公式は自己逆 (`f` が対合ゆえ、軌道内に置いた
  `f(ρ)` 側の情報が `ρ` 側の公式に翻る)

### ⚠ 次セッションはここから (段 (5) の第 2 ケース組み立て)

手順 (全部品は揃っている):

1. `exists_mem_Q0_orbitOfF_eq` で `x₀ ∈ Q₀` を取り `ρ' := ρ x₀`
   (商座標は不変なので同じファイバー)。`f(ρ')‾` が `ω̄` の `KW`-軌道内。
2. `f(ρ')` に**第 1 ケース** (`stepFour_cover` + `stepFive_orbit`) を適用。
   `hTwo` (H2, `f∘f = id`) で `f(f(ρ')) = ρ'`。⟹ `inverseFormula_symm` により
   `f(ρ')` の座標が `(ρ̄/x, 1/x)` と確定 (`ρ' = (ρ̄,x)`)。
3. §2 段 (2) (`f_mul_conj_distinguishedInvolution`) を `Ψ` で送り、
   `stepFive_secondCase` に食わせて `f(ρ' s^a) = (ρ̄/(x+A), 1/(x+A))`。
   ⚠ 座標に落とす層は `stepFour_star` の 4 因子計算と同じ作り
   (`hconjq`/`hconjy` + `mu_norm_eq` + `unitaryCoord_mul_conj`)。
4. `ρ'` 自身は 2. で既に片付いている (`A = 0` に相当) ので、
   3 と合わせて `ρ'Q₀` = ファイバー全体を被覆 → 段 (5) 完成。

その後 p.132-134 (段 (6) 以降) は**未調査** — ページ画像で段の一覧を作ることから。

## 2026-08-01 (25): §2 段 (2) をユニタリ座標へ — 段 (5) 第 2 ケースの部品完備

* **`unitaryCoord_mul_of_quotient_eq_zero`** (`UnitaryCoordinates`) — 中心元による
  乗算は座標を足すだけ (商座標の条件で述べたので `Z(Q)` の像に直接使える)
* **`sectionTwoStepTwo_coords`** — §2 段 (2) を `Ψ` で読んだ形:

      (Ψ (f(ω s^{a⁻¹}))).quotient = A · (Ψ (f(f(ω) s^a))).quotient
      unitaryCoord (Ψ (f(ω s^{a⁻¹}))) = A² · unitaryCoord (Ψ (f(f(ω) s^a))) + A
        (A = μ(a²))

  ⚠ 書籍 p.131 の助変数は**左辺のずれ** `μ(a⁻²) = A⁻¹` の方。付け替えの差だけで
  `stepFive_secondCase` とちょうど噛み合う。

### ⚠ 次セッション: 段 (5) 第 2 ケースの最終組み立て

部品は全部揃っている。手順:

1. `exists_mem_Q0_orbitOfF_eq` で `x₀ ∈ Q₀` を取り `ρ' := ρ x₀`
   (`f(ρ')‾` が `ω̄` の `KW`-軌道内)。
2. `f(ρ')` に第 1 ケース (`stepFour_cover` + `stepFive_orbit`) を適用し、
   `hTwo` (H2) と `inverseFormula_symm` で `f(ρ')` の座標 = `(ρ̄/x, 1/x)` を確定。
3. `sectionTwoStepTwo_coords` + `stepFive_secondCase` で
   `f(ρ' s^{a⁻¹}) = (ρ̄/(x+A⁻¹), 1/(x+A⁻¹))`。⚠ `stepFive_secondCase` の `a` に
   `A⁻¹ = μ(a⁻²)` を入れること (書籍の助変数)。
4. 2 で `ρ'` 自身 (`A⁻¹ = 0` に相当) も済んでいるので、`ρ'Q₀` = ファイバー全体を被覆。
   `exists_mem_K_mu_sq_eq` で `A⁻¹` が `F^×` を掃くことを使う。

その後 p.132-134 (段 (6) 以降) は**未調査** — ページ画像で段の一覧を作ることから。

## 2026-08-01 (26): 🔍 p.132 実測 — **§3 は段 (5) で終わり**、以降の構成が判明

### ⚠ 前回までの「段 (6) 以降」という想定は誤り

p.132 をページ画像で確認した結果、Ch. IV の残りは以下の構成:

| 場所 | 内容 |
|---|---|
| §3 段 (5) | p.131 下〜p.132 冒頭で終了 (`for a ∈ F − {0}, which completes the proof.`) |
| **§3 Corollary 1** | `O^{2'}(G) ≅ PSU(3,q)`。特に `V = W` なら `G ≅ PSU(3,q)` or `PGU(3,q)` |
| **§3 Corollary 2** | `G ≅ PSU(3,q)`, `ζ ∈ W^#` ⟹ `∃ ω ∈ Q − Q₀`, `f(ω) = ω^{-ζ}` かつ `h(ω) = ζ³` |
| Remark | Ch. II 場合 (10.2) の別処理 — Theorem A には不要 |
| **§4 (p.132-134)** | **`V ≠ W` の場合**。段 (1), (2), … と続く |

⟹ **§3 に段 (6) は存在しない**。段 (5) の後は Corollary 1/2 → §4。

### Corollary 1 の証明構造 (p.132)

* `G` が命題の仮説を満たせば `Q` と `f` は `q` の指定で決まり、§1 の Lemma で
  `O^{2'}(G) = ⟨Q^x | x ∈ G⟩` が同型を除いて決まる (= `RankOneBNPair` の Lemma、
  **repo では未完** — 「やること」の `Lemma (f が L を決める)` がこれ)
* `V = W` なら §2 の命題で仮説充足。`PGU(3,q)` も同仮説を満たすので
  `O^{2'}(G) ≅ O^{2'}(PGU(3,q)) = PSU(3,q)`
* ⟹ `(q+1)/(q+1,3) ≤ |W|`。等号なら `G ≅ PSU(3,q)`、さもなくば `|W| = q+1` で
  §1 の Lemma により `G ≅ PGU(3,q)`

### Corollary 2 の証明構造 (p.132) — 段 (5) の直後に取れる

`ζ⁻¹ + ζ^{-q} ≠ 0` (⚠ `ζ^q = ζ⁻¹` ゆえ `ζ^{-q} = ζ`、つまり `ζ + ζ⁻¹`) なので
`ω̄ ∈ E − {0}` で `ω̄^{1+q} = ζ + ζ⁻¹` なるものが取れる。すると
`ω = (ω̄, ζ⁻¹) ∈ Q`、`ω⁻¹ = (ω̄, ζ)`、`f(ω) = (ζω̄, ζ) = ω^{-ζ}`。(H5) で `h(ω) = ζ³`。

**repo にある部品**: `mu_W_add_inv_mem_frobFixed` (`ζ+ζ⁻¹ ∈ F`) /
`mu_W_add_inv_ne_zero` (`≠ 0`) / `frobeniusEquiv ↥F 2` の全射性 (平方根、
`F` 上ノルム = 平方) / `unitaryCoord_inv_eq` / `unitaryCoord_frobTrace`。
⟹ **段 (5) さえ閉じれば Corollary 2 はすぐ**。

### 今セッションの追加

* `stepFive_secondCase_compose` — §2 段 (2) の座標形と既知の逆元公式を合成して
  `ρ s^{a⁻¹} = (ρ̄, x + A⁻¹)` での公式を出す算術 (⚠ 書籍の助変数は `A⁻¹`)

### ⚠ 次セッションの順序

1. 段 (5) 第 2 ケースの群論組み立て ((25) の 4 手)。
2. **Corollary 2** (上記のとおり短い)。
3. `RankOneBNPair` の Lemma (`f` が `L` を決める) — Corollary 1 の前提。
   issue 冒頭「やること」の未チェック項目。
4. Corollary 1 → §4 (p.132-134、段 (1) から)。⚠ §4 は Ch. I §3 Prop 1(c)、
   Ch. I §2 Prop 3、Ch. II (11) を引く — repo の対応物を先に実測すること。

## 2026-08-01 (27): Corollary 2 の両端が揃った

| 定理 | 内容 |
|---|---|
| `exists_normPreimage_of_mem_W` | `ζ ∈ W^#` ⟹ `∃ r ≠ 0`, `Tr μ(ζ) = r·r^q` (基点 `ω̄` の構成) |
| `f_eq_conj_inv_of_inverseFormula` | 座標から `f(ω) = ζ⁻¹ω⁻¹ζ` を読み取る (`stepFour_at_omega` の逆) |
| `stepFive_secondCase_compose` | §2 段 (2) の座標形 + 既知の公式 ⟹ `ρ s^{a⁻¹}` での公式 |

⟹ **Corollary 2 は「段 (5) を `ω = ofUnitary r μ(ζ)` に当てる」だけ**になった:

1. `exists_normPreimage_of_mem_W` で `r` を取り `ω := ofUnitary m M.card hu r μ(ζ) h`
   (`Ψ.symm` で `↥hyp.Q` に戻す)。商座標 `r`、ユニタリ座標 `μ(ζ)`。
2. 段 (5) で `f(ω)` の座標 = `(r/μ(ζ), 1/μ(ζ))`。
3. `f_eq_conj_inv_of_inverseFormula` (`hx` は 1. から) で `f(ω) = ζ⁻¹ω⁻¹ζ = ω^{-ζ}`。
4. `h(ω) = ζ³` は (H5) から — repo の `h_eq_zpow_three` (`PSU3SectionThree`) が
   まさにこれ (`f ω = ζ⁻¹ω⁻¹ζ` から `h ω = ζ³`)。⚠ 実測済み・再利用可。
5. `ω ∉ Q₀` は商座標 `r ≠ 0` から。

### ⚠ 次セッションの順序 (更新)

1. **Corollary 2** (上記 5 手、部品は全部 landing 済)。
2. 段 (5) 第 2 ケースの群論組み立て ((25) の 4 手)。
3. `RankOneBNPair` の Lemma (`f` が `L` を決める) → Corollary 1。
4. §4 (p.132-134)。

## 2026-08-01 (28): 🎯 §3 Corollary 2 landing + ファイル分割

**`corollaryTwo`** (p.132): 各 `ζ ∈ W^#` に `f(ω) = ω^{-ζ}` かつ `h(ω) = ζ³` なる
`ω ∈ Q − Q₀` が在る。元は探すのでなく `ζ` から**作る** —
`exists_normPreimage_of_mem_W` → `ofUnitary (ω̄, μ(ζ))` → 段 (5) →
`f_eq_conj_inv_of_inverseFormula`。`h(ω) = ζ³` は既存 `h_eq_zpow_three`。
⚠ 段 (5) は仮説 `hfive` として受けている (第 2 ケースの組み立てが未了のため)。

**分割**: `PSU3InverseFormula.lean` が 1433 行に達したので兄弟 prefix-split。

* `PSU3StarEquation.lean` (246 行) — 純 `E` の算術 (`(∗∗)` とその帰結)
* `PSU3InverseFormula.lean` (1231 行) — 群論側 (段 (4)・段 (5)・Corollary 2)

`OddOrder.lean` に新 leaf を配線済。module 名不変ゆえ下流 import は無変更。

### ⚠ 次セッションはここから

1. **段 (5) 第 2 ケースの群論組み立て** — 部品は全部揃っている ((25) の 4 手)。
   これが閉じれば `corollaryTwo` の `hfive` が外れて Corollary 2 が無条件になる。
2. `RankOneBNPair` の Lemma (`f` が `L` を決める) → **Corollary 1**。
   ⚠ issue 冒頭「やること」の未チェック項目。§1 の Lemma。
3. **§4** (p.132-134、`V ≠ W` の場合)。段 (1)(2)… ⚠ Ch. I §3 Prop 1(c) /
   Ch. I §2 Prop 3 / Ch. II (11) を引くので repo 対応物の実測が先。

## 2026-08-01 (29): 段 (5) 第 2 ケース — 座標が揃えば締まる形まで

* **`mu_kActor_sq_inv`** — `μ((a⁻¹)²) = μ(a²)⁻¹` (第 2 ケースはファイバー上を
  `s^{a⁻¹}` で動くが §2 (2) は `a²` で共役するので助変数が互いに逆)
* **`stepFive_secondCase_at`** — 座標が揃った状態での締め:
  §2 (2) の座標形 + `f(ρ)s^a` での逆元公式 + `ρ s^{a⁻¹}` の座標
  ⟹ `ρ s^{a⁻¹}` での逆元公式

### 段 (5) 第 2 ケースの残り (**純粋に配線のみ**)

`stepFive_secondCase_at` の 6 仮説を供給する層を書くだけ。供給元は全部 landing 済:

| 仮説 | 供給元 |
|---|---|
| `hLq`, `hLy` | `sectionTwoStepTwo_coords` |
| `hRq`, `hRy` | 第 1 ケース (`stepFour_cover`/`stepFive_orbit`) を `f(ρ)s^a` に + `inverseFormula_symm` + `unitaryCoord_mul_conj` |
| `hρ'q`, `hρ'y` | `unitaryCoord_mul_conj` (`a := a⁻¹`) + `mu_kActor_sq_inv` |
| `hA`, `hx`, `hxA` | `Units.ne_zero` / `x = μ(ζ)` は unit / `mu_K_add_mu_W_ne_zero` 型 |
| 軌道に入れる自由度 | `exists_mem_Q0_orbitOfF_eq` |
| `f∘f = id` | `hTwo` (`RankOneBNPair`) |

⚠ この配線層は仮説 30 本規模になる (`stepFour_star` と同じ質)。
**新 leaf に切ること** — `PSU3InverseFormula.lean` は既に 1270 行。

### ⚠ 次セッションの順序 (更新)

1. 段 (5) 第 2 ケースの配線 (新 leaf `PSU3StepFive.lean` 等)。
   閉じれば `corollaryTwo` の `hfive` が外れる。
2. `RankOneBNPair` の Lemma (`f` が `L` を決める) → Corollary 1。
3. §4 (p.132-134)。

## 2026-08-01 (30): 🎯 段 (5) 第 2 ケースの配線 landing

新 leaf **`PSU3StepFive.lean`** (196 行、`OddOrder.lean` に配線済)。

**`stepFive_secondCase_elem`**: 第 1 ケース (`hsolved` = `f(ρ)` のファイバー上で
成り立つ逆元公式) から `ρ s^{a⁻¹}` での公式を出す。

1. `hsolved` を `f(ρ)` 自身に → (H2) `f(f ρ) = ρ` + `inverseFormula_symm` で
   `f(ρ) = (ρ̄/x, 1/x)` 確定
2. `hsolved` を `f(ρ)s^a` に → §2 (2) の内側の `f` (座標は `unitaryCoord_mul_conj`)
3. `sectionTwoStepTwo_coords` + `stepFive_secondCase_at` で締め

**`unitaryCoord_ne_zero`** (`UnitaryCoordinates`): 商座標 ≠ 0 ⟹ ユニタリ座標 ≠ 0。

⟹ `a` が `K` を動けば `ρ s^{a⁻¹}` は `ρ` 自身を除くファイバー全体を掃き、
`ρ` 自身は 1. の時点で片付いている。**段 (5) の数学は完了**。

### ⚠ 次セッションはここから

1. **段 (5) の最終梱包** — 第 1 ケース (`stepFour_cover` + `stepFive_orbit`) と
   第 2 ケース (`stepFive_secondCase_elem`) を場合分けで束ね、
   「全 `ρ ∈ Q − Q₀` で `f(ρ) = (ρ̄/y, 1/y)`」の 1 本にする。
   ⚠ 場合分けの述語は「`ρ̄` が `μ(KW)` の軌道 `[ω̄]` に居るか」
   (`orbitOfF`/`QuotientGroup.mk` のレベル)。軌道内なら
   `exists_conjQHom_quotient_eq_of_coset_eq` (`PSU3OrbitCount`) で `KW`-共役に、
   軌道外なら `exists_mem_Q0_orbitOfF_eq` で `ρQ₀` 内に取り替え。
   これが閉じれば `corollaryTwo` の `hfive` が外れる。
2. `RankOneBNPair` の Lemma (`f` が `L` を決める) → **Corollary 1**。
3. **§4** (p.132-134、`V ≠ W`)。⚠ Ch. I §3 Prop 1(c) / Ch. I §2 Prop 3 /
   Ch. II (11) の repo 対応物を先に実測。

## 2026-08-01 (31): 段 (5) 最終梱包の部品 + 全結果の axiom 監査

新結果はすべて **axiom-clean** を確認 (`propext`/`Classical.choice`/`Quot.sound` のみ):
`stepFour_elem` / `stepFour_cover` / `stepFive_orbit` / `stepFive_secondCase_elem` /
`corollaryTwo`。

追加した梱包部品 (`PSU3StepFive.lean`):

* **`exists_mem_K_conjQHom_eq`** — 任意の `kv` は `K` の明示元での `conjQHom`
  (`actualKActor` = `conjQByK` の像)。軌道条件が出す抽象的 `kv` を
  `k ∈ G` を名指しする `stepFive_orbit` に繋ぐ橋。
* **`exists_conjQHom_eq_of_quotient_smul`** — `ρ` の商座標が `ω` の `μ(kv)` 倍なら
  `ρ = (ω のファイバー内の元)^{kv}`。証明は `σ := conjQHom kv⁻¹ ρ` を取るだけ。

### ⚠ 段 (5) 最終梱包の残り (次セッション)

述語 `P ρ := 「f(ρ) の座標が (ρ̄/y, 1/y)」` として:

1. **軌道内**: `(Ψρ).quotient = μ(kv)·(Ψω).quotient` なら
   `exists_conjQHom_eq_of_quotient_smul` で `ρ = σ^{kv}` (σ は ω のファイバー)、
   `stepFour_cover` で `P σ`、`exists_mem_K_conjQHom_eq` + `stepFive_orbit` で `P ρ`。
2. **軌道外**: `exists_mem_Q0_orbitOfF_eq` で `x₀ ∈ Q₀` を取り `ρ' := ρ x₀`。
   `f(ρ')` は軌道内なので 1. により `f(ρ')` のファイバー全体で `P`。
   `stepFive_secondCase_elem` で `ρ'` のファイバー = `ρ` のファイバーに移す。
3. 場合分けの述語は `E^× ⧸ μ(KW)` の等式。`orbitOfF`/`baseUnit`/`fUnit`
   (`PSU3OrbitCount`) の API を使う。⚠ **これらの API を先に実測すること**。

閉じれば `corollaryTwo` の `hfive` が外れ、**§3 が完成**する。

## 2026-08-01 (32): 段 (5) 最終梱包の実装メモ (着手前の実測結果)

`PSU3OrbitCount` の API を実測した:

| 名前 | 中身 |
|---|---|
| `baseUnit M hZ hωQ hωQ0 : M.Eˣ` | `M.coord (mk ω)` を unit にしたもの (`baseUnit_val` は `rfl`) |
| `fUnit M hZ H hC2 hωQ hωQ0 x : M.Eˣ` | `M.coord (mk (f (ω x)))` (`fUnit_val` は `rfl`) |
| `orbitOfF … x` | `QuotientGroup.mk (fUnit … x)` in `M.Eˣ ⧸ range M.mu` |

軌道条件「`ρ̄` が `ω̄` の `KW`-軌道」= `QuotientGroup.mk (baseUnit … hρQ hρQ0)
= QuotientGroup.mk (baseUnit … hωQ hωQ0)`。`QuotientGroup.eq.mp` で
`∃ kv, μ(kv) = baseUnit(ρ)⁻¹ · baseUnit(ω)` ⟹ `ρ̄ = μ(kv⁻¹)·ω̄`。
`(Ψρ).quotient = e·baseUnit(ρ)` なので `e ≠ 0` を消せば座標の関係に落ちる。

### ⚠ 実装で引っかかる点 (先に把握しておくこと)

1. **`subst hkveq` は使えない** — `exists_mem_K_conjQHom_eq` が返す
   `hkveq : (kActor hk, kv.2) = kv` は右辺 `kv` が左辺にも現れる (`kv.2`) ので
   `subst` が通らない。`rw [← hkveq] at hkv` のように**項の側だけ**書き換える。
2. **`conjQHom_kActor_apply_val` は W 成分が `⟨v, hv⟩` の形を要求** —
   `kv.2 : ↥hyp.W` をそのまま渡せない。`⟨(kv.2 : G), kv.2.2⟩ = kv.2` は `rfl` なので
   `have hw : (⟨(kv.2 : G), kv.2.2⟩ : ↥hyp.W) = kv.2 := rfl` を挟む。
3. `stepFive_orbit` は `σ ≠ 1`・`unitaryCoord (Ψ σ) ≠ 0` と、
   `k*v*σ*(k*v)⁻¹` と その `f` の所属証明を要る。前者 2 つは
   `unitaryCoord_ne_zero` と商座標 ≠ 0 から出る。

### 梱包の骨 (次セッション)

```
軌道内: exists_conjQHom_eq_of_quotient_smul → σ (ω のファイバー)
        → stepFour_cover で P σ → exists_mem_K_conjQHom_eq + stepFive_orbit → P ρ
軌道外: exists_mem_Q0_orbitOfF_eq → x₀, ρ' := ρ x₀ (f(ρ') が軌道内)
        → 上で f(ρ') のファイバー全体に P → stepFive_secondCase_elem → P ρ
```

## 2026-08-01 (33): 段 (5) 第 1 ケースの梱包 landing

**`stepFive_of_mem_orbit`**: `ρ` の商座標が `ω` の `μ(kv)` 倍なら逆元公式が `ρ` で
成り立つ (書籍 p.131「`ρ̄` が `ω̄` の `KW`-軌道に居れば (5) は (4) から従う」)。

`exists_conjQHom_eq_of_quotient_smul` で `ρ = σ^{kv}` に分解 → `hcover`
(= `stepFour_cover`) で σ → `exists_mem_K_conjQHom_eq` + `stepFive_orbit` で ρ。

⚠ **実装の要点** (次に似た配線をするとき): `conjQHom kv σ = ⟨ρ,_⟩` から
群レベルの `k·v·σ·(k·v)⁻¹ = ρ` を取り出し、結論の書き換えは**部分型の元として**
(`Subtype.ext` で `⟨k·v·σ·(k·v)⁻¹, _⟩ = ⟨ρ, _⟩`) 行う。所属証明が式に依存するので
式の中で `rw` すると motive が壊れる。

⚠ 罠 2 (前記の「`⟨v,hv⟩` vs `kv.2`」) は**問題にならなかった** — Lean 4 の構造体
eta により `⟨(kv.2 : G), kv.2.2⟩` と `kv.2` は defeq で、
`conjQHom_kActor_apply_val hkK kv.2.2` がそのまま通る。

### ⚠ 段 (5) の残り: 場合分け 1 本

```
∀ ρ ∈ Q − Q₀:
  by_cases 「(Ψρ).quotient が (Ψω).quotient の μ(KW)-倍か」
  · yes → stepFive_of_mem_orbit
  · no  → exists_mem_Q0_orbitOfF_eq で x₀, ρ' := ρ x₀ (f(ρ') が軌道内)
          → stepFive_of_mem_orbit を f(ρ') のファイバーに
          → stepFive_secondCase_elem で ρ へ
```

場合分けの述語は `∃ kv, (Ψρ).quotient = μ(kv) * (Ψω).quotient`
(`Classical.em` で分岐。`orbitOfF` の商群を経由しなくても直接書ける)。
⚠ 「no」の側で `exists_mem_Q0_orbitOfF_eq` が返す軌道の等式を上の形に翻訳する層が要る
(`baseUnit`/`fUnit` は `M.coord`、`Ψ` の商座標はその `e` 倍)。

## 2026-08-01 (34): 段 (5) 両ケースがファイバー単位に揃った

**`stepFive_secondCase_fibre`**: `stepFive_secondCase_elem` (1 つの `a` ごと) を
`eq_or_exists_conj_mul_of_quotient_eq` (ファイバー = `{ρ} ∪ {ρ s^a}`) と合わせて
ファイバー全体へ。`s^a = s^{(a⁻¹)⁻¹}` の付け替えだけ。

現状 (`PSU3StepFive.lean` 364 行):

| 定理 | 入力 | 出力 |
|---|---|---|
| `stepFive_of_mem_orbit` | `stepFour_cover` + `(Ψρ).quotient = μ(kv)·(Ψω).quotient` | `ρ` での公式 |
| `stepFive_secondCase_elem` | `f(ρ)` のファイバーでの公式 | `ρ s^{a⁻¹}` での公式 |
| `stepFive_secondCase_fibre` | 上 + 基点 | `ρ` のファイバー全体での公式 |

### ⚠ 段 (5) の残り: 場合分け 1 本 (これで §3 完成)

```
∀ ρ ∈ Q, (Ψρ).quotient ≠ 0 → 公式 at ρ
  by_cases horb : ∃ kv, (Ψρ).quotient = μ(kv) * (Ψω).quotient
  · exact stepFive_of_mem_orbit … horb.choose_spec
  · -- exists_mem_Q0_orbitOfF_eq で x₀ ∈ Q₀ を取り ρ' := ρ x₀
    -- f(ρ') が軌道内 ⟹ stepFive_of_mem_orbit で f(ρ') のファイバー全体
    -- ⟹ stepFive_secondCase_elem + stepFive_secondCase_fibre で ρ' のファイバー
    -- ρ は ρ' と同じファイバー (x₀ ∈ Q₀) なので終わり
```

⚠ 「no」の側の翻訳: `exists_mem_Q0_orbitOfF_eq` は
`orbitOfF … x = QuotientGroup.mk (baseUnit … hωQ hωQ0)` を返す。
`orbitOfF … x = QuotientGroup.mk (fUnit … x)` で `fUnit` は
`M.coord (mk (f (ρ x)))` なので、`QuotientGroup.eq` を剥がして
`∃ kv, μ(kv) = fUnit⁻¹ · baseUnit` を得、`(Ψ·).quotient = e · M.coord(·)` で
座標の等式に翻訳する。⚠ 向き (kv か kv⁻¹ か) に注意。

## 2026-08-01 (35): 🎯🎯 段 (5) 完成 → **§3 が段 (4) の上で完結**

### `stepFive` — 段 (5) 本体 (p.131)

`ρ ∈ Q − Q₀` すべてで `f(ρ̄, y) = (ρ̄/y, 1/y)`。書籍どおり 2 ケース:

* **軌道内** — 判定述語は `∃ kv, (Ψρ).quotient = μ(kv)·(Ψω).quotient`。
  軌道条件が**商座標だけに依存する**のが効いて、`key` として括り出せる
  (`stepFive_of_mem_orbit` を任意の点に当てる形)。
* **軌道外** — `exists_mem_Q0_orbitOfF_eq` で `x ∈ Q₀` を取り `ρ x` に移る。
  `orbitOfF = mk (fUnit)` と `mk (baseUnit)` の等式を `QuotientGroup.eq` で剥がし、
  `hΨq`+`hquot` (どちらも `M.coord` に落ちる) で座標の関係
  `(Ψ f(ρx)).quotient = μ(kv⁻¹)·(Ψω).quotient` に翻訳。
  ⟹ `f(ρx)` のファイバー**全体**が `key` に乗る = `hsolved`。
  `inverseFormula_symm` で `ρx` 自身の公式 (= `hbase`)、
  `stepFive_secondCase_elem` で各 `a ∈ K` の `hstep`、
  `stepFive_secondCase_fibre` でファイバー全体、`ρ` はそこに居る。

### `corollaryTwo_of_stepFour` — Corollary 2 が無条件に

`corollaryTwo` の `hfive` を `stepFive` で塞いだ。残る入力は段 (4) の被覆
`hcover` (1 点 `ω₀ ∈ Q − Q₀` のファイバー上の逆元公式) と §2 の standing data のみ。

両者とも `#print axioms` = propext / Classical.choice / Quot.sound。
`PSU3StepFive.lean` 630 行、leaf build green・警告 0。

### ⚠ 実装メモ (次に似た配線をするとき)

1. `hΨq`+`hquot` で `(Ψ ⟨τ,_⟩).quotient = e * ↑(fUnit …)` を出すとき、
   `rw [hΨq, hquot, fUnit_val]` の後に**明示の `rfl` が要る** —
   `QuotientGroup.mk'` と `mk` の差は `rw` 末尾の自動 rfl (reducible) では閉じない。
2. `M.Eˣ` は `CommGroup` なので `mu_kv` の移項は `mul_comm` + `inv_mul_cancel_left`
   で済む (値レベルに落として `field_simp` する必要は無い)。
3. `exists_mem_Q0_orbitOfF_eq` は「**`ρ` を基点に**した軌道写像が `ω` の軌道を
   取る `x`」を返す (基点が `ρ` 側なのを取り違えない)。

### ⚠ 次セッションはここから

1. **`RankOneBNPair` の Lemma (`f` が `L` を決める)** — issue 冒頭「やること」の
   未チェック項目。§1 の Lemma で、**Corollary 1 の前提**。⟹ 上流優先でこれが次。
2. **Corollary 1** (p.132) — `O^{2'}(G) ≅ PSU(3,q)`。1. の上に乗る。
3. **§4** (p.132-134、`V ≠ W` の場合)。段 (1)(2)… ⚠ Ch. I §3 Prop 1(c) /
   Ch. I §2 Prop 3 / Ch. II (11) を引くので repo 対応物の実測が先。

## 2026-08-01 (36): 🎯 §1 の Lemma (`f` が `L` を決める) landing

新 leaf **`OddOrder/GroupTheory/RankOneBNPairRigidity.lean`** (366 行、警告 0)。
書籍 p.123 の Lemma を、既存の置換モデルを準同型にまとめて形式化した。

| 結果 | 内容 |
|---|---|
| `permHom : L →* Equiv.Perm (Option ↥Q)` | `MulAction.toPermHom L (L ⧸ M)` を `coordsEquiv` 経由で読んだもの |
| `permHom_ker` | `= M.normalCore` (忠実性 = `Subgroup.normalCore_eq_ker`) |
| `permHom_range_eq` | `L = ⟨M,t⟩` ⟹ 像 = ⟨`t` の置換, `M` の置換たち⟩ |
| `permHom_map_conjQ_eq` | `⟨Q^x⟩ = ⟨Q,Q^t⟩` ⟹ 像 = ⟨`Q` の置換, その `t`-共役⟩ |
| `mulEquivOfPermMatch` / `conjQMulEquivOfPermMatch` | 生成元対応 ⟹ `L ≃* L'` / `⟨Q^x⟩ ≃* ⟨Q'^x⟩` |
| `mAct` (+`qPart`/`dPart`/`mAct_eq`) | `Setup.split` の `Q`-成分を名付けた `M` の点集合 `Q` への作用 |
| **`mulEquivOfData`** | 書籍の言葉: `εQ` が基点と `f` を、`θ : M ≃* M'` が `mAct` を保てば `L ≃* L'` |

### ⚠ 実装メモ

1. `Equiv.optionCongr_symm` は **`optionCongr e.symm = (optionCongr e).symm`** の向き。
   `(optionCongr e).symm` を潰すには **`rw [← Equiv.optionCongr_symm]`**。
2. `Equiv.Perm` の等式に `ext o` を使うと `Option.ext` まで降りて `↔` が出る
   (`... = some a ↔ ... = some a`)。**`refine Equiv.ext fun o => ?_`** を使う。
3. `Equiv.permCongrHom` は `MulEquiv`。`⇑↑e` (MonoidHom 経由) と `⇑e` は
   syntactic に別物なので `Subgroup.map` 後は **`simp only [MonoidHom.coe_coe]`** で揃える。
   `Subgroup.map_closure` は存在せず **`MonoidHom.map_closure`**。
4. `MonoidHom.ker_mulEquiv_comp` は `(↑iso).comp f` の形を要求し
   `iso.toMonoidHom.comp f` と合わない → `permHom_ker` は `MulEquiv.map_eq_one_iff` で直に書いた。

### ⚠ 次セッションはここから

1. **Corollary 1** (p.132) — `O^{2'}(G) ≅ PSU(3,q)`、`V = W` なら
   `G ≅ PSU(3,q)` or `PGU(3,q)`。⚠ 先に実測すること:
   `GroupTheory/SpecificGroups/ProjectiveUnitary/*` に何があるか
   (PSU(3,q) の構成・位数・`O^{2'}`・PGU との関係)。
2. **§4** (p.132-134、`V ≠ W` の場合)。段 (1)(2)… ⚠ Ch. I §3 Prop 1(c) /
   Ch. I §2 Prop 3 / Ch. II (11) を引くので repo 対応物の実測が先。

## 2026-08-01 (37): Corollary 1 の前半 (p.132 実測つき)

p.132 のページ画像で Corollary 1 / Corollary 2 / Remark / §4 冒頭を確定した。

**Corollary 1** (p.132):
> 命題の仮説の下で `O^{2'}(G) ≅ PSU(3,q)`。特に `V = W` なら
> `G ≅ PSU(3,q)` または `PGU(3,q)`。
>
> 証明: `G` が仮説を満たせば `Q` と `f` は `q` の指定で決まり、§1 の Lemma で
> `O^{2'}(G) = ⟨Q^x | x ∈ G⟩` が同型を除いて決まる。`V = W` なら §2 の命題で
> 仮説充足。`PGU(3,q)` も同仮説を満たすので `O^{2'}(G) ≅ O^{2'}(PGU(3,q)) = PSU(3,q)`。
> ゆえ `(q+1)/(q+1,3) ≤ |W|`。等号なら `G ≅ PSU(3,q)`、さもなくば `|W| = q+1` で
> §1 の Lemma により `G ≅ PGU(3,q)`。

### 今セッションで landing した前半 2 部品

| 定理 | 内容 |
|---|---|
| `Hypothesis.f_eq_of_inverseFormula` | 段 (5) の公式を満たす写像は `Q − Q₀` 上一意 (`eq_of_unitaryCoord_eq`)。= 「`f` は座標だけの関数」 |
| `RankOneBNPair.mAct_of_mem_Q` | `Q` は点集合に**右移動**で作用する (`q x⁻¹` の `D`-成分 = 1) |
| `RankOneBNPair.permCongrHom_permHom_mem_Q` / `permCongr_image_Q` | 群同型 `Q ≃* Q'` が `Q` の置換たちを対応させる |
| **`RankOneBNPair.conjQMulEquivOfData`** | `f` を絡める群同型 `Q ≃* Q'` ⟹ `⟨Q^x⟩ ≃* ⟨Q'^x⟩` (Lemma 前半の書籍形) |

### ⚠ Corollary 1 の残り (規模の実測)

残るのは**具体群側**で、repo の現状は:

* `O^{2'}` — repo/mathlib に一般の `O^{π}` は無い (`AxiomsCheck` の docstring に
  `residual_eq_normalClosure` の言及があるのみ)。Theorem A の結論構造
  (`CentralizerInductionBridge.TheoremAConclusion`) は「奇数指数の正規部分群 `L`
  + 具体モデルとの同型」で、これが書籍の `O^{2'}(G)` に当たる。
* PSU(3,q) の具体モデル = `ProjectiveUnitary.standardPermGroup n`
  (`GeneratedAction.lean`)。`PSU3InductionTarget` が `L ≃* standardPermGroup n` +
  作用の同変全単射を要求する形で既にある (4053 行、13 leaf)。
* **PGU(3,q) は repo に無い** (`grep PGU` は `StandardGenerators.lean` の
  コメント 1 箇所のみ)。Corollary 1 の第 2 段は
  「`PGU(3,q)` が同じ仮説を満たす」= `Hypothesis G Ω` の具体インスタンス構成を要し、
  これは新規の大きな infra。

⟹ **次の 2 択** (どちらも上流優先に反しない):
  (a) `f` の `Q₀^#` 上の決定 = §2 (1) (`f(s^a) = g(s^a) = s^{a⁻¹}`, `h(s^a) = a²`)。
      これが入れば `conjQMulEquivOfData` の `hεf` が `Q` 全体で供給でき、
      Corollary 1 前半が完全に閉じる。⚠ (C2) の repo 対応物 (`hC2` は
      `t s t = s t s`) から書籍の `tst = s*s` をどう読むか、p.123 の画像で要確認。
  (b) §4 (p.132-134、`V ≠ W`) に進む。⚠ Ch. I §3 Prop 1(c) / Ch. I §2 Prop 3 /
      Ch. II (11) を引くので repo 対応物の実測が先。

文書順では (a) が先 (§2 (1) は §3 より上流)。

## 2026-08-01 (38): §4 の前提を実測 — **全部そろっている (§4 は unblocked)**

`grep` で確認 (自分で実行):

| §4 が引くもの | repo での所在 | 状態 |
|---|---|---|
| Ch. I §3 Prop 1(c) | `CentralizerTrichotomy` / `CentralizerInductionBridge` (AxiomsCheck に 8 節) | ✅ |
| Ch. I §2 Prop 3 | `exists_semilinear_equiv` (AxiomsCheck 9127) | ✅ |
| Ch. II (11) | `FirstCase/StepEleven.lean` + `StepElevenComplement.lean` | ✅ |
| §3 Corollary 2 | `corollaryTwo_of_stepFour` (本 issue、今日) | ✅ |
| §3 Corollary 1 | **未** (PGU(3,q) が repo に無い) — §4 の**最終行**だけが引く | ⚠ |

⚠ §2 (1) は既に形式化済だった (`PSU3Preliminary.lean`):
`fgh_at_distinguishedInvolution` (`f(s)=g(s)=s`, `h(s)=1`; `hC2` が既に canonical
分解 `s·1·t·s` になっているのを読むだけ) と
`fgh_at_conj_distinguishedInvolution` (= (1) 本体、(H3) + `a^t = a⁻¹` で輸送)。
(37) の「次は (a) §2 (1)」は**不要**だった。

### §4 の構成 (pp.132-134、実測)

前置き: `D` が素数位数 `p` の部分群 `P` で `C_{Q/Q₀}(P) ≠ 1` なるものを持つと仮定
してよい。`C_Q(P) ≠ 1` ⟹ `P` は `Ω` に 3 不動点 ⟹ `D` 内で `V` の部分群に共役。
`P ⊂ V` としてよい。`W` は `Q/Q₀` に固定点自由 ⟹ `P ∩ W = 1`。

| 段 | 内容 |
|---|---|
| (1) | `U = O^{2'}(C_G(P))` とすると `U/(P ∩ U) ≅ PSU(3,ℓ)`、`q = ℓ^p`、`ℓ > 2` |
| (2) | `∃ ω ∈ Q−Q₀, ζ ∈ W^#, η ∈ P`: `η` が `ω`,`ζ` を中心化し `f(ω) = ω^{-ζ}`, `h(ω) = ζ³η⁻¹` (**§3 Cor 2 を使う**) |
| (3) | `f(ω s^a) = f(ω^{ζ a⁻¹})^{a⁻²} ζ^{a⁻¹}` 型の漸化式 (§2 (2) から) |
| (4)-(6) | `μ` (= `η` の誘導する `E` の体自己同型) つきの座標方程式 |
| (7)-(9) | 線形結合で `a²μ + b² ≠ 0` と分数式 |
| (10) | `(ζ+ζ⁻¹+X^μ)X = (ζ+ζ⁻¹+X^{-2})…` for `X ∈ F − {0, a^{2r}}` |
| 締め | `X` を `X+1` にずらして引くと `X^μ = X` ⟹ `μ = 1` ⟹ `η ∈ W` ⟹ §3 Cor 1 |

⚠ (3)-(10) は OCR が壊れているので**ページ画像 (p.133/134) で式を確定**すること。

### ⚠ 次セッションはここから

1. **締めの体論補題** (§4 の最後): 「有限体の環自己同型が高々 `|S|` 個の元を除いて
   固定するなら、`(|F| − |S|)² > |F|` の下で恒等」。書籍は `μ` の奇位数を使うが、
   固定部分体が真ならば `|Fix|² ≤ |F|` (拡大次数 ≥ 2) で一般に出る方が強く簡単。
   ⟹ **自己完結・unblocked・再利用可**。repo の `natCard_frobFixedSubfield`
   (`Algebra/QuadraticFrobenius.lean`) が近所。
2. §4 段 (1)(2) — (2) は `corollaryTwo_of_stepFour` にそのまま乗る。
3. Corollary 1 第 2 段 = PGU(3,q) infra (大きい、別立て)。

## 2026-08-01 (39): §4 の締めの体論補題 landing

`OddOrder/Algebra/FixedPointDensity.lean` (105 行、警告 0、axiom-clean)。

書籍 p.134 の最終段は「`μ` は 3 元を除いて固定 + `μ` は奇位数 ⟹ `μ = 1`
(`μ ≠ 1` なら `|F| > 8`)」だが、**奇位数の迂回は不要**だった:

> 加法写像の固定点は**既に部分群**なので、真部分群なら群の半分を取りこぼす。
> ⟹ **半分超を固定すれば恒等**。位数の仮定も乗法構造も要らない。

| 定理 | 内容 |
|---|---|
| `fixedAddSubgroup` | 加法写像の固定点を `AddSubgroup` として |
| `eq_id_of_fixes_compl` | `2\|S\| < \|A\|` かつ `S` の外で固定 ⟹ 恒等 |
| `RingEquiv.eq_refl_of_fixes_compl` | 環自己同型版 |

道具は Lagrange (`AddSubgroup.card_mul_index`) と `index_eq_one` だけ。
書籍の状況 (`|S| = 3`) では仮説が `6 < q` すなわち `q ≥ 8` になり、
書籍が挙げる境界と一致する。

⚠ 名前の実測: `Set.ncard_coe_finset` (× `ncard_coe_Finset`)、
`Nat.card_coe_set_eq` (× `Set.Nat.card_coe_set_eq`)。

### ⚠ 次セッションはここから

1. **§4 段 (1)(2)** — (2) は `corollaryTwo_of_stepFour` にそのまま乗る。
   (1) は `U = O^{2'}(C_G(P))` と Ch. I §3 Prop 1(c) (repo にあり)。
   ⚠ `O^{2'}` は repo/mathlib に無い — Theorem A の結論構造
   (`TheoremAConclusion`: 奇数指数の正規部分群) が対応物なので、
   まずそこと突き合わせること。
2. **§4 段 (3)-(10)** の座標計算。⚠ OCR 崩壊のため **p.133/134 のページ画像**で
   式を確定してから着手 (`references/peterfalvi/pages/peterfalvi-p133.png`,
   `-p134.png` に取得済)。締めは 1. の `eq_id_of_fixes_compl` に落ちる。
3. Corollary 1 第 2 段 = PGU(3,q) infra (大きい、別立て)。

## 2026-08-01 (40): §4 の算術 (5)-(10) landing — p.133/134 実測つき

ページ画像で式を確定した (OCR は完全に崩壊していた)。**書籍の式 (実測)**:

* 前提: `ω² = (0,α)`。`a ∈ K` で `a ≠ α^{-τ}`、`b ∈ K` で `b^{1+θ} = α + a^{-(1+θ)}`。
* (3) `f(ωs^a)‾ = f(ω^{-ζ}s^{a⁻¹})‾^{a^{-2}} = ζ a^{-2} f(ωs^b)‾`
* (4) `a² f(ωs^a)‾ = ζ⁻¹ (f(ωs^a)‾)^η + ω̄`
* (5) `ζ f(ωs^b)‾ = a^{-2μ} (f(ωs^b)‾)^η + ω̄`
* (6) `b² f(ωs^b)‾ = ζ⁻¹ (f(ωs^b)‾)^η + ω̄`
* (7) `f(ωs^b)‾ = (a^{2μ}+ζ)/(ζ(a^{2μ}+b²)) · ω̄`
* (8) `(f(ωs^b)‾)^η = (b²+ζ)/(b²a^{-2μ}+1) · ω̄`
* (9) `(ζ⁻¹+a^{-2μ})^μ/(1+b²a^{-2μ})^μ = (b²+ζ)/(1+b²a^{-2μ})`
* `λ = (ζ⁻¹+a^{-2μ²})/(b²+ζ) ∈ F`、`λζ² + (λb²+a^{-2μ²})ζ + 1 = 0`。
  `ζ^{1+q}=1` かつ `ζ ∉ F` ⟹ `λ = 1` かつ `b² + a^{-2μ²} = ζ + ζ⁻¹`。
* (10) `(ζ+ζ⁻¹+X^μ)X = (ζ+ζ⁻¹+X^{μ²})X^μ`  (`X ∈ F − {0, α^{2τ}}`)
* 締め: (10) を `X+1` で書いて引くと **`X^{μ²} = X`** (⚠ `X^μ = X` ではない)。
  ⟹ `μ = 1` ⟹ `η ∈ W`、`h(ω) ∈ W` ⟹ §3 Corollary 1 で終了。

### landing した部品 (`PSU3SectionFourArithmetic.lean`、168 行、警告 0)

| 定理 | 内容 |
|---|---|
| `sectionFour_solve` | (5)(6) を `X = f(ωs^b)‾`, `Y = X^η`, `A = a^{2μ}`, `B = b²`, `c = ζ` の**2 未知数連立 1 次**と見て `Y` を消去。逆元なし形 |
| `sectionFour_seven` / `_eight` | (7)/(8)。⚠ (8) は分子分母に `a^{2μ}` を掛けて逆元を消した同値形 |
| `sectionFour_eq_of_add_eq_zero` | 「suitable linear combinations … `a^{2μ}+b² ≠ 0`」の中身: 分母が 0 なら `a^{2μ} = ζ` |
| `sectionFour_fixed_of_shift` | 締めの引き算。`μ` が環写像ゆえ 2 次項が全消え ⟹ **標数の仮定すら不要** |
| `sectionFour_sq_eq_id` | (10) が `T` の外で使えれば `2\|T\| < \|F\|` で `μ² = id` |

⚠ 例外集合は `X` 側と `X+1` 側の両方が要るので 4 元 (書籍は `1` を落としている)。
§4 では `q = ℓ^p`、`ℓ > 2`、`p` 奇素数 ⟹ `q ≥ 64` なので `2·4 < q` は余裕。

### ⚠ 次セッションはここから

1. **`μ² = 1` かつ `μ` 奇位数 ⟹ `μ = 1`** — 書籍が奇位数を使う唯一の箇所。
   `orderOf μ ∣ 2` と `∣ p` (奇素数) から `orderOf μ = 1`。小さい群論補題。
2. **(4) ⟹ (5)** と (9) ⟹ `λ = 1` の算術 — 残る純算術。
   ⚠ `λ = 1` は `ζ^{1+q} = 1` と `ζ ∉ F` から `λζ² + (λb²+a^{-2μ²})ζ + 1 = 0`
   を解く議論。`ζ` が `F` 上 2 次で、その最小多項式が `ζ² + (ζ+ζ⁻¹)ζ + 1` である
   ことを使う (norm = 1)。
3. **§4 段 (1)(2)** の群論。(2) は `corollaryTwo_of_stepFour` に乗る。
   ⚠ (訂正: 下記 (43) 参照 — `O^{2'}` = `Subgroup.primeComplementResidual 2`。repo にある)
4. Corollary 1 第 2 段 = PGU(3,q) infra (大きい、別立て)。

## 2026-08-01 (41): §4 の λ = 1 と μ² = 1 ⟹ μ = 1 landing

`PSU3SectionFourArithmetic.lean` 242 行 (警告 0)。p.134 の残る 2 論法:

| 定理 | 内容 |
|---|---|
| `eq_zero_of_add_mul_eq_zero` | `ζ ∉ F` ⟹ `1`,`ζ` は `F` 上独立 |
| `sq_add_traceCoeff_mul_add_one` | `ζ² + (ζ+ζ⁻¹)ζ + 1 = 0` |
| `sectionFour_lambda_eq_one` | `λζ²+(λβ+α)ζ+1 = 0` ⟹ `λ = 1` かつ `β+α = s` |
| `eq_one_of_sq_eq_one_of_odd_pow` | `x²=1` かつ `x^n=1` (`n` 奇) ⟹ `x=1` |

⚠ **書籍より要らない仮定が 2 つあった**:
1. `ζ² + (ζ+ζ⁻¹)ζ + 1 = 0` は標数 2 では**恒等式**。書籍は `ζ^{1+q} = 1` を根拠に
   挙げるが、`(ζ+ζ⁻¹)ζ = ζ²+1` で相殺するので要るのは `ζ ≠ 0` だけ。
2. shift trick は標数の仮定すら要らない (前 tick)。
⟹ `ζ^{1+q} = 1` が実際に効くのは `ζ + ζ⁻¹ ∈ F` (= `s ∈ F`) の部分だけ。

`eq_one_of_sq_eq_one_of_odd_pow` の axiom は `propext` のみ。

### §4 の純算術は**これで出そろった**

(5)(6)⟹(7)(8) / 分母 ≠ 0 / (10) の shift / `μ²=id` / `λ=1` / `μ²=1`+奇位数⟹`μ=1`。
残るのは**群論側と (9) の導出**:

### ⚠ 次セッションはここから

1. **(9) の導出** — (7)(8) から (9) を出す部分。⚠ ここは `η` が `ζ` を中心化する
   (段 (2)) ので `ζ^μ = ζ`、`a,b ∈ K ⊆ F` 等の**群論的事実**を使う。
   (7)(8) を `μ` で送って比べるだけのはずだが、`(·)^η` と `(·)^μ` の関係
   (App. I Prop 2 = `η` が `Q/Q₀ ≅ E` に semilinear に作用) を先に repo で実測すること。
2. **§4 段 (1)(2)** の群論。(2) は `corollaryTwo_of_stepFour` に乗る。
   ⚠ (訂正: 下記 (43) 参照 — `O^{2'}` = `Subgroup.primeComplementResidual 2`。repo にある)
3. Corollary 1 第 2 段 = PGU(3,q) infra (大きい、別立て)。

## 2026-08-01 (42): §4 (9) landing — 算術と群論の境界が確定

`PSU3SectionFourArithmetic.lean` 304 行 (警告 0、axiom-clean)。

分子分母を `A = a^{2μ}` で割ると (7)(8) は書籍の表示形になり、**(9) の両辺に同じ
分母 `1 + b²a^{-2μ}` が現れる**:

| 定理 | 内容 |
|---|---|
| `one_add_mul_inv_ne_zero` | `1 + b²a^{-2μ} = (a^{2μ}+b²)a^{-2μ} ≠ 0` |
| `sectionFour_seven_book` | `X = (ζ⁻¹ + a^{-2μ})/(1 + b²a^{-2μ}) · ω̄` |
| `sectionFour_eight_book` | `Y = (b² + ζ)/(1 + b²a^{-2μ}) · ω̄` |
| `sectionFour_nine` | (9) 本体 (`ω̄ ≠ 0` で割るだけ) |

⚠ **(9) の群論的入力を仮説 `hsemi : Y = Z * w` に切り出した**。中身は
「`η` は `E = Q/Q₀` に `μ`-semilinear に作用し (App. I Prop 2)、`ω̄` を固定する
(段 (2) が `ω` を中心化する `η` を選ぶ)」で、`Z` = (7) のスカラーの `μ`-像。
⟹ **§4 の算術部分と群論部分の境界がここで切れた**。

### 前提の実測 (自分で grep)

| 書籍 | repo | 状態 |
|---|---|---|
| App. I Prop 2 (semilinear) | `Peterfalvi/Appendices/SemilinearField.lean` (2(a)(b) とも複数定理) | ✅ |
| Ch. I §2 Prop 3 | `Suzuki/SemilinearRealization.lean` の `exists_semilinear_equiv` | ✅ |

### ⚠ 次セッションはここから

**§4 で残るのは群論側だけ**:

1. **段 (1)** — `U = O^{2'}(C_G(P))`、`U/(P∩U) ≅ PSU(3,ℓ)`、`q = ℓ^p`、`ℓ > 2`。
   ⚠ `O^{2'}` は repo に無い。`TheoremAConclusion` (奇数指数の正規部分群 + 具体モデル)
   が対応物なので、まずそこと突き合わせる。Ch. I §3 Prop 1(c) は repo にあり。
2. **段 (2)** — `∃ ω,ζ,η`: `η` が `ω`,`ζ` を中心化、`f(ω) = ω^{-ζ}`、`h(ω) = ζ³η⁻¹`。
   `corollaryTwo_of_stepFour` にそのまま乗る (`U` 側で使う)。
3. **段 (3)(4)** — §2 (2)(3) を `ω`,`s^a` に当てて座標へ。既存の
   `sectionTwoStepTwo_coords` 等が近所。
4. **(5)(6) の供給** — (3)(4) と semilinearity から。ここまで来れば
   `sectionFour_solve` 以降は全部 landing 済で §4 が閉じる。
5. Corollary 1 第 2 段 = PGU(3,q) infra (大きい、別立て)。

## 2026-08-01 (43): ⚠ 訂正 — `O^{2'}` は repo にある + `⟨Q^x⟩` との橋

**(37)(39)(41)(42) に書いた「`O^{2'}` は repo/mathlib に無い」は誤りだった**。
`Subgroup.primeComplementResidual p G` (`GroupTheory/PrimeComplementResidual.lean`)
がまさに `O^{p'}`:

* 定義 = `⨆ P : Sylow p G, ↑P` (Sylow p の生成する部分群)
* `primeComplementResidual_normal` / `_index_coprime` / `_le_of_coprime_index`
  ⟹ 指数が `p` と互いに素な**最小の**正規部分群
* `primeComplementResidual_eq_normalClosure` — 任意の Sylow p の正規閉包
* docstring 自身が「`p = 2` の場合が prime-complement residual 記法」と明記

⚠ 教訓: [[verify-port-state-by-number-not-coq-name]] のとおり「repo に無い」は
**着手前に必ず実測**する。今回は `grep "O^{2'}"` が AxiomsCheck の docstring 1 件しか
出さず (記法が違うだけ)、それを「無い」と読んでしまった。**概念名 (`residual`,
`normalClosure`, `Sylow`) でも grep すること**。

### 追加した橋 (`RankOneBNPairRigidity.lean`)

| 定理 | 内容 |
|---|---|
| `closure_iUnion_conj_eq_normalClosure` | `⟨H^x \| x ∈ L⟩ = normalClosure H` |
| `closure_iUnion_conj_eq_primeComplementResidual` | `Q` が Sylow p ⟹ `⟨Q^x⟩ = O^{p'}(L)` |

⟹ §1 の Lemma (`conjQMulEquivOfData`) の対象が、書籍 Corollary 1 (p.132) の
`O^{2'}(G) = ⟨Q^x | x ∈ G⟩` とそのまま繋がった。

### ⚠ 次セッションはここから

1. **§4 段 (1)** — `U = O^{2'}(C_G(P))` (= `primeComplementResidual 2 ↥(C_G(P))`)、
   `U/(P∩U) ≅ PSU(3,ℓ)`。Ch. I §3 Prop 1(c) は repo にあり。
   ⚠ 先に §4 の standing hypothesis (`P ≤ V` 素数位数 `p`、`C_{Q/Q₀}(P) ≠ 1`) を
   どう置くか決める。
2. §4 段 (2)(3)(4) と (5)(6) の供給 → `sectionFour_solve` 以降は landing 済。
3. Corollary 1 第 2 段 = PGU(3,q) infra。

## 2026-08-01 (44): §4 段 (1) の部品 2 つが既に repo にあった + Artin を一般化

**実測**: `GaloisCentralizer.lean` (403 行) が §4 段 (1) の 2 つの引用をすでに持つ:

| 書籍 (p.132 段 (1)) | repo |
|---|---|
| 「`Z(U) ⊂ C_V(C_{Q₀}(P))` ゆえ Galois の定理で `Z(U) ⊂ PW`」 | `centralizer_V_centralizer_Q0 (hPV : P ≤ V) : C_V(C_{Q₀}(P)) = P ⊔ W` ✅ |
| 「`\|C_{Q₀}(P)\| = ℓ` ゆえ `q = ℓ^p` (`P` が `Q₀` に体自己同型として作用)」 | `natCard_Q0_eq_pow` (下記で一般化) ✅ |

⚠ 前者は書籍が `⊂ PW` と書くところをそのまま `= P ⊔ W` で持っている
(書籍の Ch. III §1 版 `= P` は `W = 1` の特殊化)。

### `natCard_Q0_eq_pow` — Artin の次数公式を一般化

旧 `natCard_Q0_eq_pow_of_W_eq_bot` は `W = ⊥` を要求していたが、**§4 は `V ≠ W` の
場合なので `W ≠ 1`** で届かなかった。実際に必要なのは faithful だけで、`W` は
`V` の `Q₀` への作用の核だから **`X ⊓ W = ⊥`** で十分:

* `natCard_Q0_eq_pow (hXV : X ≤ V) (hXW : X ⊓ W = ⊥) : |Q₀| = |C_{Q₀}(X)|^{|X|}`
* 証明で `W = ⊥` を使っていたのは `|B| = |X|` の **1 箇所だけ**で、`σ` の全域単射を
  `X.subgroupOf V` への制限の単射性に置き換えれば済んだ
  ([[generalize-by-measuring-which-carrier-fields-are-used]] のとおり)。
* `_of_W_eq_bot` は 1 行の特殊化として残した (consumer = `StructureOfH/WNeBot.lean`)。

⟹ §4 段 (1) の「`q = ℓ^p`」がそのまま使える (`P ∩ W = 1` は §4 前置きが与える)。

### ⚠ 次セッションはここから

段 (1) の残りは:
1. `U = O^{2'}(C_G(P))` = `primeComplementResidual 2 ↥(C_G(P))` を置く。
2. Ch. I §3 Prop 1(c) を `C_G(P)` に当てて `U/Z(U) ≅ PSU(3,ℓ)`
   (`CentralizerTrichotomy` / `CentralizerInductionBridge` 群、要 API 実測)。
   前提は「(C1) で 2-rank ≥ 2」「`st` の位数 3」「`C_Q(P)` が exponent 4」。
3. `Z(U) ⊆ P`: `Z(U) ⊆ C_V(C_{Q₀}(P)) = P ⊔ W` (上記) と
   「`PZ(U)` が `C_Q(P) ⊄ Q₀` を中心化 ⟹ `PZ(U) ∩ W = 1`」。
⟹ **1. と 3. は既存部品でほぼ書ける**。2. が本体。

## 2026-08-01 (45): §4 段 (1) の分岐選択 landing + ⚠ 書籍 2 条件の役割が判明

`Hypothesis.nonempty_psu3Data_of_orderOf_eq_three` (`CentralizerTrichotomy.lean`)。

### ⚠ 「`st` の位数 3」だけでは PSU 枝は決まらない

repo の分岐データを実測すると:

| 枝 | `orderOf (s·t)` | `C_Q(X)` の構造 |
|---|---|---|
| PSL(2,ℓ) | **3** | `cQ_isElementaryAbelian` (exponent 2) |
| Sz(ℓ) | **5** | `cQ_isSuzuki2Group` |
| PSU(3,ℓ) | **3** | `cQ_isSuzuki2Group` |

⟹ 位数 3 が排除するのは **Suzuki だけ**。PSL2 を排除するのは書籍のもう一方の条件
「`C_Q(P)` が exponent 4」で、PSL2 枝の `cQ_isElementaryAbelian` と矛盾する。
**書籍の 2 条件はちょうど 2 枝を 1 つずつ潰しており、どちらも省けない**。

### 実測できた段 (1) の部品 (全部 repo にある)

| 書籍 | repo |
|---|---|
| `U = O^{2'}(C_G(P))` | `Subgroup.primeComplementResidual 2 C` — `CentralizerCommonData.residual_eq_normalClosure` が既にこの形 |
| Ch. I §3 Prop 1(c) | `centralizer_trichotomy_of_induction` (3 枝 + 共通データ) |
| `U/Z(U) ≅ PSU(3,ℓ)` | `CentralizerPSUData.residualQuotientEquiv` (`(O^{2'}(C) ⧸ Z(·)) ≃* standardPermGroup n`) |
| 枝の同定 | **今回の `nonempty_psu3Data_of_orderOf_eq_three`** |
| `q = ℓ^p` | `natCard_Q0_eq_pow` (前 tick で一般化) |
| `Z(U) ⊂ PW` (Galois) | `centralizer_V_centralizer_Q0` |

⚠ `CentralizerPSUData` は `Type` なので `∃` でなく `Nonempty (Σ' …)` で返す
(既存 `centralizer_trichotomy_of_induction` の流儀)。

### ⚠ 次セッションはここから

1. **§4 の standing hypothesis を置く** — `P ≤ V` 素数位数 `p`、`C_{Q/Q₀}(P) ≠ 1`、
   `P ∩ W = 1`、`C_Q(P)` exponent 4。これが決まれば段 (1) は上の 6 部品の配線。
   ⚠ `C_Q(P)` exponent 4 / 2-rank ≥ 2 / `st` 位数 3 がどこから来るかを先に実測する
   ((C1)(C2) の repo 対応物)。
2. 段 (2) — `corollaryTwo_of_stepFour` を `U` 側に当てる。
3. 段 (3)(4) → (5)(6) の供給 → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (46): §4 段 (1) の入力 3 つの出どころを実測

段 (1) を配線するのに要る 3 つの仮説がどこから来るかを追った。

### (a) 2-rank ≥ 2 (書籍「By (C1)」)

`centralizer_trichotomy_of_induction` の仮説
`hA3 : ∃ E : Subgroup (centralizer X), Nat.card E = 4 ∧ ∀ x ∈ E, x² = 1`
**がそのまま 2-rank ≥ 2** (Klein 四元群)。⟹ (C1) の役割はこれを供給すること。
`Basic.lean` の (A3) / `CentralizerQuotient.centralizerQuotient_twoRankGeTwo` も近所。

### (b) `st` の位数 3 (書籍「(C2)」)

repo では `hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3` として
`exists_standardModel` 等が既に受け取っている。`hC2 : t·s·t = s·t·s` と同値
(`PSU3Preliminary.lean` ヘッダ参照)。

### (c) `C_Q(P)` が exponent 4 → `¬ IsElementaryAbelian 2 C_Q(P)`

⚠ **これだけ repo に無く、導出が要る**。書籍は §4 前置きの `C_{Q/Q₀}(P) ≠ 1` から
出している。導出鎖 (全部部品は在る):

1. `|P|` 奇素数、`Q` は 2-群 ⟹ 互いに素。`Q₀ ⊴ Q` は `P`-不変。
2. **Glauberman の補題** = `OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient`
   (「`X`-固定な剰余類は `X`-固定な代表を持つ」、`GroupTheory/CoprimeFixedPoints.lean`
   に再輸出) ⟹ `C_{Q/Q₀}(P) = C_Q(P)Q₀/Q₀`。
3. ⟹ `C_{Q/Q₀}(P) ≠ 1` から `∃ x ∈ C_Q(P)`, `x ∉ Q₀`。
4. `Q₀ = Z(Q)` かつ `Ω₁(Q) ≤ Q₀` (`ActualCenter.lean` の
   `center_Q_eq_Q0_subgroupOf_of_sq_eq_one` / `LemmaFiveSetup.centerEqQ0` 周り)
   ⟹ `x² ≠ 1` ⟹ `¬ IsElementaryAbelian 2 C_Q(P)`。

⟹ 段 (1) の分岐選択 (`nonempty_psu3Data_of_orderOf_eq_three`) にそのまま入る。

### ⚠ 次セッションはここから

1. **(c) の導出を書く** — 上の 4 手。⚠ 4. の `Ω₁(Q) ≤ Q₀` が repo でどの補題か
   (`sqFibre` 周り?) を先に実測すること。ここが段 (1) の唯一の未形式化入力。
2. §4 の standing hypothesis 構造を置いて段 (1) を配線。
3. 段 (2) — `corollaryTwo_of_stepFour` を `U` 側に。
4. 段 (3)(4) → (5)(6) の供給 → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (47): §4 段 (1) の入力 (c) — 導出鎖の部品が**全部そろった**

(46) で「(c) だけ repo に無い」と書いたが、導出に要る補題を全部特定できた:

| 手 | 内容 | repo の補題 |
|---|---|---|
| 1 | `\|P\|` 奇素数 / `Q` は 2-群 ⟹ 互いに素、`Q₀ ⊴ Q` は `P`-不変 | (仮説から) |
| 2 | Glauberman: `X`-固定剰余類は `X`-固定代表を持つ | `OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient` (`GroupTheory/CoprimeFixedPoints.lean` が再輸出) |
| 3 | ⟹ `C_{Q/Q₀}(P) = C_Q(P)Q₀/Q₀`、よって `C_{Q/Q₀}(P) ≠ 1` から `∃ x ∈ C_Q(P) − Q₀` | 2. の帰結 |
| 4 | `Q` は Suzuki 2-群 ⟹ **対合はすべて中心的** | `OddOrder.Higman.Suzuki2Groups.involutions_subset_center` (`Higman/Suzuki2Groups/CenterInvolutions.lean:66`) |
| 5 | `Z(Q) = Q₀` | `LemmaFiveSetup.centerEqQ0` / `ActualCenter.center_Q_eq_Q0_subgroupOf_of_sq_eq_one` |
| 6 | ⟹ `x ∉ Q₀` ゆえ `x² ≠ 1` ⟹ `¬ IsElementaryAbelian 2 C_Q(P)` | 4.+5. |

⟹ **§4 段 (1) は既存部品の配線のみ**になった (新しい数学は要らない)。
必要なのは §4 の standing hypothesis を置くことと、上の 6 手 + (45) の分岐選択 +
(44) の Artin/Galois を繋ぐこと。

⚠ 4. は `Higman/` 側 (Suzuki 2-群の一般論) にある — `Peterfalvi/Appendices/Suzuki/`
だけ grep していると見つからない。[[grep-concept-names-not-book-notation]] の通り
**概念名 (`involutions`, `center`) で横断 grep すること**。

### ⚠ 次セッションはここから

1. **§4 の standing hypothesis 構造**を置く (`SectionFourSetup` 的なもの):
   `P ≤ V`、`Nat.card P = p` 素数、`p` 奇、`C_{Q/Q₀}(P) ≠ 1`、`P ⊓ W = ⊥`。
2. (c) の導出 (上の 6 手) → `nonempty_psu3Data_of_orderOf_eq_three` に入力。
3. 段 (1) 残り: `q = ℓ^p` (`natCard_Q0_eq_pow`) と `Z(U) ⊆ P`
   (`centralizer_V_centralizer_Q0` + 「`PZ(U)` が `C_Q(P) ⊄ Q₀` を中心化」)。
4. 段 (2) — `corollaryTwo_of_stepFour` を `U` 側に。
5. 段 (3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (48): §4 段 (1) の exponent 判別子 landing

`PSU3SectionFourSetup.lean` (新 leaf、97 行、警告 0、axiom-clean)。
(47) の導出鎖の手 4-6 を実装:

| 定理 | 内容 |
|---|---|
| `sq_ne_one_of_not_mem_Q0` | **`Q` の対合は `Q₀` に居る** (Suzuki 2-群の対合は中心的 + `Z(Q) = Q₀`) ⟹ `Q − Q₀` の元は 1 に平方しない |
| `not_isElementaryAbelian_cQ_of_not_mem_Q0` | `C_Q(X)` が `Q − Q₀` と交われば elementary abelian でない = `nonempty_psu3Data_of_orderOf_eq_three` の仮説そのもの |

⟹ **段 (1) の 3 入力のうち未形式化だったものが埋まった**。

### 段 (1) の残り

1. **Glauberman の手 (2)(3)**: `C_{Q/Q₀}(P) ≠ 1` ⟹ `∃ x ∈ C_Q(P) − Q₀`。
   部品 = `GroupTheory.CoprimeFixedPoints.map_fixedSubgroup_eq_fixedSubgroup_quotient`
   (`C_H(X)` の像 = `C_{H/N}(X)`、Isaacs Cor 3.28 経由)。
   ⚠ `P` の `Q` への共役作用を `φ : ↥P →* MulAut ↥Q` として組む plumbing が要る。
2. §4 の standing hypothesis 構造 + 段 (1) 本体の配線
   (`natCard_Q0_eq_pow` で `q = ℓ^p`、`centralizer_V_centralizer_Q0` で `Z(U) ⊆ PW`)。
3. 段 (2)(3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (49): 🎯 §4 段 (1) の Glauberman ステップ landing

`exists_fixed_not_mem_Q0` (`PSU3SectionFourSetup.lean`) — `Q/Q₀` の非自明な
`P`-固定類は `P`-固定な代表を持ち、その代表は `Q₀` の外に居る。
道具は `GroupTheory.CoprimeFixedPoints.map_fixedSubgroup_eq_fixedSubgroup_quotient`
(Isaacs Cor 3.28 経由)。

⟹ **段 (1) の exponent 判別子が §4 の standing hypothesis から完全に供給される**:

```
C_{Q/Q₀}(P) ≠ 1
  → exists_fixed_not_mem_Q0            (Glauberman、今回)
  → not_isElementaryAbelian_cQ_of_not_mem_Q0   (48)
  → nonempty_psu3Data_of_orderOf_eq_three      (45)  ⟹ PSU(3,ℓ) 枝
```

⚠ 実装の罠: `d x d⁻¹ = u·x` (`u = d x d⁻¹ x⁻¹`) への書き換えを素の `rw` でやると
`u` の中の `d x d⁻¹` も一緒に潰れて goal が壊れる (`x d x d⁻¹ x d x⁻¹ d⁻¹ x⁻¹ = x`
のような形になる)。**`set u := …` で先に抽象化してから `rw`** する。
`u·x = x·u` は `Q₀ ≤ Z(Q)` の中心性 (`hZ`) から。

### §4 段 (1) の現状

| 部品 | 状態 |
|---|---|
| `U = O^{2'}(C_G(P))` | ✅ `primeComplementResidual 2 C` |
| Ch. I §3 Prop 1(c) | ✅ `centralizer_trichotomy_of_induction` |
| 枝の同定 (位数 3 + exponent) | ✅ `nonempty_psu3Data_of_orderOf_eq_three` |
| exponent 判別子の供給 | ✅ (48) + (49) |
| `U/Z(U) ≅ PSU(3,ℓ)` | ✅ `CentralizerPSUData.residualQuotientEquiv` |
| `q = ℓ^p` | ✅ `natCard_Q0_eq_pow` |
| `Z(U) ⊂ PW` (Galois) | ✅ `centralizer_V_centralizer_Q0` |
| **`Z(U) ⊆ P`** | ⚠ 残り: 「`PZ(U)` が `C_Q(P) ⊄ Q₀` を中心化 ⟹ `PZ(U) ∩ W = 1`」 |

### ⚠ 次セッションはここから

1. `Z(U) ⊆ P` の詰め (`PZ(U) ∩ W = 1`)。⚠ 「`W` が `Q/Q₀` に固定点自由に作用」
   (§4 前置きが `P ∩ W = 1` に使うのと同じ事実) を repo で実測すること。
2. §4 の standing hypothesis 構造を置いて段 (1) を組み上げる。
3. 段 (2)(3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (50): (Q/Q₀)^# の固定点自由性を `V = W` から外した

⚠ **§4 は `V ≠ W` の場合なので、既存の `eq_one_of_conj_eq_mul_Q0_of_mem_D` は
そのままでは使えなかった** (仮説に `hVW : V = W` を持つ)。これは §4 前置きの
`P ∩ W = 1` と段 (1) の `P Z(U) ∩ W = 1` の両方に要る事実。

証明を読むと `hVW` は `c⁻¹` を `k·v` (`k ∈ K`, `v ∈ W`) に分解するためだけに
使われており、以降は分解しか見ていない。⟹ 分解を仮説に上げて一般化:

| 定理 | 内容 |
|---|---|
| `eq_one_of_conj_eq_mul_Q0_of_decomp` | `c⁻¹ = k·v` を仮説に取る本体 |
| `eq_one_of_conj_eq_mul_Q0_of_mem_D` | `V = W` から分解を得る 2 行 (signature 不変) |
| **`eq_one_of_conj_eq_mul_Q0_of_mem_W`** | `W` の元は `k = 1` で既に分解済 ⟹ `V = W` 不要 |

⟹ §4 (`V ≠ W`) でも `W` の固定点自由性が使える。

⚠ 教訓 (2 回目): 既存補題が使えないと思ったら**まず証明を読んで、どの仮説が
どこで効いているかを実測する**。今回も (44) の Artin 一般化と同じで、
効いていたのは 1 箇所だけだった。[[generalize-by-measuring-which-carrier-fields-are-used]]

### ⚠ 次セッションはここから

1. `Z(U) ⊆ P`: `Z(U) ≤ C_V(C_{Q₀}(P)) = P ⊔ W` (Galois) と
   「`P Z(U)` が `C_Q(P) ⊄ Q₀` を中心化 ⟹ `P Z(U) ∩ W = 1`」
   (今回の `eq_one_of_conj_eq_mul_Q0_of_mem_W`) を繋ぐ。
2. §4 の standing hypothesis 構造を置いて段 (1) を組み上げる。
3. 段 (2)(3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (51): 🎯 §4 段 (1) の `Z(U) ⊆ P` 部品 landing

書籍 p.132 段 (1) の締めの残り 2 手 (`PSU3SectionFourSetup.lean`):

| 定理 | 内容 |
|---|---|
| `inf_W_eq_bot_of_centralizes` | `Q − Q₀` の元を中心化する部分群は `W` と自明に交わる (前 tick の `_of_mem_W` 版から) |
| `eq_of_mem_mul_of_inf_eq_bot` | Dedekind: `P W` に分解する元からなり `W` と自明に交わる部分群は `P` |

⚠ **部分群束は一般には modular でない** — mathlib の `IsModularLattice (Subgroup ·)` は
**可換群**用 (`Algebra/Group/Subgroup/Order.lean`)。`S ≤ P ⊔ W` から直接 `S ≤ P` は
出せないので、`P ⊔ W = P W` の分解を仮説に取る形にした (実際にそれを与えるのは
「`W` が `V` で正規」)。

### 段 (1) の部品は**これで全部そろった**

| 書籍の主張 | repo |
|---|---|
| `U = O^{2'}(C_G(P))` | `primeComplementResidual 2 C` |
| Ch. I §3 Prop 1(c) | `centralizer_trichotomy_of_induction` |
| 2-rank ≥ 2 (C1) | 同定理の `hA3` |
| `st` 位数 3 (C2) | `hst` |
| `C_Q(P)` exponent 4 | `exists_fixed_not_mem_Q0` → `not_isElementaryAbelian_cQ_of_not_mem_Q0` |
| 枝の同定 | `nonempty_psu3Data_of_orderOf_eq_three` |
| `U/Z(U) ≅ PSU(3,ℓ)` | `CentralizerPSUData.residualQuotientEquiv` |
| `q = ℓ^p` | `natCard_Q0_eq_pow` |
| `Z(U) ⊂ PW` (Galois) | `centralizer_V_centralizer_Q0` |
| `PZ(U) ∩ W = 1` | `inf_W_eq_bot_of_centralizes` |
| `Z(U) ⊆ P` | `eq_of_mem_mul_of_inf_eq_bot` |

### ⚠ 次セッションはここから

1. **§4 の standing hypothesis 構造を置いて段 (1) を組み上げる** (残りは配線のみ)。
   構造の中身: `P ≤ V`、`Nat.card P` = 奇素数 `p`、`C_{Q/Q₀}(P) ≠ 1` (= `∃ x ∈ Q−Q₀`
   でクラスが `P`-固定)、`P ⊓ W = ⊥`、`Q` が Suzuki 2-群、`Z(Q) = Q₀`、`μ` 単射、
   `orderOf (s·t) = 3`。
2. 段 (2)(3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。
3. Corollary 1 第 2 段 = PGU(3,q) infra (大きい、別立て)。

## 2026-08-01 (52): 🎯 §4 の standing hypothesis 構造 landing

`Hypothesis.SectionFourSetup` (`PSU3SectionFourSetup.lean` 346 行):

| フィールド | 書籍 |
|---|---|
| `P ≤ V` | 「`D` 内で共役して `P ⊂ V` としてよい」 |
| `P ⊓ W = ⊥` | 「`W` は `Q/Q₀` に固定点自由ゆえ `P ∩ W = 1`」 |
| `cardP` 奇素数 + `card_P` | 「素数位数 `p` の部分群 `P`」 |
| `x ∈ Q − Q₀` + `x_class_fixed` | `C_{Q/Q₀}(P) ≠ 1` (商作用を組まずに綴る) |

派生 (`SectionFourSetup` namespace):
* `P_le_D`
* `exists_fixed_not_mem_Q0` — Glauberman を §4 の `P` に当てる
* **`not_isElementaryAbelian_cQ`** — 段 (1) の exponent 判別子を standing hypothesis
  から直接出す ⟹ `nonempty_psu3Data_of_orderOf_eq_three` にそのまま渡せる

### ⚠ 次セッションはここから

1. **段 (1) の結論を組む**: `centralizer_trichotomy_of_induction` の
   `CentralizerTrichotomyData` を取り、`nonempty_psu3Data_of_orderOf_eq_three` で
   psu3 枝に落とし、`natCard_Q0_eq_pow` で `q = ℓ^p`、
   `centralizer_V_centralizer_Q0` + `inf_W_eq_bot_of_centralizes` +
   `eq_of_mem_mul_of_inf_eq_bot` で `Z(U) ⊆ P`。
   ⚠ `Z(U)` は `↥U` の部分群なので `G` に戻すのに `U.subtype` で map が要る。
   `PZ(U)` の `P W` 分解 (Dedekind の仮説) をどこから取るかも要検討
   (`W ⊴ V` + `P, Z(U) ≤ V`)。
2. 段 (2)(3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (53): 🎯 §4 段 (1) の結論 2 本を standing hypothesis から

| 定理 | 書籍 (p.132 段 (1)) |
|---|---|
| `SectionFourSetup.natCard_Q0_eq_pow_cardP` | 「`\|C_{Q₀}(P)\| = ℓ` ゆえ `q = ℓ^p`」 |
| `SectionFourSetup.eq_P_of_centralizes` | 「`PZ(U)` が `C_Q(P) ⊄ Q₀` を中心化 ⟹ `Z(U) ⊂ P`」 |

⚠ 前者で **(44) の Artin 一般化がそのまま効いた** — 旧 `_of_W_eq_bot` 版は
`V ≠ W` の §4 には届かず、必要な faithful 性はちょうど setup の
`P ⊓ W = ⊥` フィールドだった。

⟹ **段 (1) の 3 結論 (枝 = PSU(3,ℓ) / `q = ℓ^p` / `Z(U) ⊆ P`) がすべて
standing hypothesis から出る形になった**。

### ⚠ 次セッションはここから

1. 段 (1) を 1 本の定理に梱包する (任意) か、段 (2) に進む。
   ⚠ 梱包するなら `Z(U)` を `↥U` から `G` に戻す map (`U.subtype`) と
   `PZ(U)` の `P W` 分解 (Galois の `Z(U) ⊆ P ⊔ W` + `W ⊴ V`) の 2 点が要る。
   これらは配線であって新しい数学ではない。
2. **段 (2)** — `∃ ω ∈ Q−Q₀, ζ ∈ W^#, η ∈ P`: `η` が `ω`,`ζ` を中心化し
   `f(ω) = ω^{-ζ}`、`h(ω) = ζ³η⁻¹`。`corollaryTwo_of_stepFour` を `U` 側に当てる。
3. 段 (3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (54): §4 段 (2) の「canonical form の一意性」部品

`RankOneBNPair.IsFGH.eq_of_le` — 同じ `t` を持ち `Q' ≤ Q`, `D' ≤ D` の小さい setup の
三つ組 `f₁,g₁,h₁` は、外側の `f,g,h` と `Q'^#` 上で一致する。

⚠ **証明は 4 行**だった: 小さい setup の定義式
`t x t = g₁(x) h₁(x) t f₁(x)` は因子が `Q`,`D`,`Q` に居るので**外側にとっても
canonical 分解**であり、`fgh_eq_of_canonical` (分解の一意性) がそのまま同定する。
書籍 p.133 段 (2) の「By the uniqueness of the canonical form of an element of `G − H`」
がまさにこれ。

### §4 段 (2) の残り (p.133)

| 主張 | 状態 |
|---|---|
| `(V ∩ U)/(P ∩ U)` が `C_{Q₀}(P)` を中心化 (PSU(3,ℓ) の構造から) | ⚠ 未 |
| Galois ⟹ `V ∩ U ⊂ PW`、`U ⊂ C_G(P)` ⟹ `V ∩ U ⊂ P × C_W(P)` | 部品あり (`centralizer_V_centralizer_Q0`) |
| `\|(V∩U)/(P∩U)\| = (ℓ+1)/(ℓ+1,3) ≠ 1` (`ℓ > 2`) | ⚠ 未 (PSU(3,ℓ) の位数計算) |
| `U` 側で §3 Cor 2 を使う | ✅ `corollaryTwo_of_stepFour` (要 `U` 側 Hypothesis の構成) |
| `f(ω) = f₁(ω)`, `h(ω) = h₁(ω)` | ✅ **今回の `IsFGH.eq_of_le`** |

### ⚠ 次セッションはここから

1. `V ∩ U ⊂ P × C_W(P)` の部分 — `centralizer_V_centralizer_Q0` +
   「`U ⊆ C_G(P)`」から。⚠ `U = O^{2'}(C_G(P)) ≤ C_G(P)` は
   `primeComplementResidual` が `C_G(P)` の部分群なので自明。
2. `(ℓ+1)/(ℓ+1,3) ≠ 1` — `ProjectiveUnitary` 側の位数計算を実測すること。
3. `U` 側の `Hypothesis` 構成 (§3 Cor 2 を当てるため)。⚠ ここが段 (2) の本体。

## 2026-08-01 (55): §4 段 (2) の `V ∩ U ⊆ P × C_W(P)` landing

| 定理 | 書籍 (p.133 段 (2)) |
|---|---|
| `inf_le_sup_W_of_centralizes` | 「Galois の定理で `V ∩ U ⊂ PW`」 |
| `inf_le_sup_centralizer_W` | 「`U ⊂ C_G(P)` ゆえ `V ∩ U ⊂ P × C_W(P)`」 |

後者の要点: `v = p·w` と書くと `w = p⁻¹v` が `P` を中心化する。`v` が中心化するのは
`U ⊆ C_G(P)` から、`p` が中心化するのは **`P` が素数位数ゆえ可換**だから
(`isCyclic_of_prime_card` + `IsCyclic.commGroup` を `letI` で入れる)。

### 段 (2) の残り

| 主張 | 状態 |
|---|---|
| `(V ∩ U)/(P ∩ U)` が `C_{Q₀}(P)` を中心化 (PSU(3,ℓ) 構造) | ⚠ 未 (上記 2 定理の仮説) |
| `V ∩ U ⊂ PW` / `⊂ P × C_W(P)` | ✅ 今回 |
| `\|(V∩U)/(P∩U)\| = (ℓ+1)/(ℓ+1,3) ≠ 1` | ⚠ 未 (PSU(3,ℓ) の位数計算) |
| `U` 側で §3 Cor 2 | ⚠ `U` 側 `Hypothesis` の構成が要る |
| `f(ω) = f₁(ω)`, `h(ω) = h₁(ω)` | ✅ `IsFGH.eq_of_le` (54) |

### ⚠ 次セッションはここから

1. `ProjectiveUnitary` 側で `(ℓ+1)/(ℓ+1,3)` 相当の位数計算が在るか実測する
   (`Bruhat.lean` / `TorusCentralizer.lean` / `Simplicity.lean` 付近)。
2. `U` 側の `Hypothesis` 構成 — 段 (2) の本体。⚠ `CentralizerQuotient.lean` の
   `centralizerQuotientHypothesis` が「`C_G(X)` の faithful 商に (A1)-(A3) を
   与える」構成なので、まずそれが `U` にも使えるか実測すること。

## 2026-08-01 (56): 🔍 段 (2) の `(ℓ+1)/(ℓ+1,3) ≠ 1` は**位数計算でなく存在で足りる**

書籍 p.133 段 (2) は
> Furthermore, `|(V∩U)/(P∩U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` since `ℓ > 2`.
> Let `ζ₁ ∈ (V∩U) − (P∩U)` …

と書くが、**この位数が使われるのは「`(V∩U) − (P∩U)` が空でない」ことだけ**。
⟹ 正確な位数 `(ℓ+1)/(ℓ+1,3)` を計算する必要はなく、**存在命題で足りる**。

そして model 側にちょうどその形の定理がある:

* `ProjectiveUnitary.exists_ne_one_mem_psuTorus_torusWeight_eq_one (n) (hn : 1 < n)`
  — `∃ c, c ∈ PSUTorusParameter n ∧ c ≠ 1 ∧ torusWeight c = 1`
  (`TorusCentralizer.lean:76`)。`1 < n` すなわち `ℓ = 2ⁿ ≥ 4` は書籍の `ℓ > 2` と一致。
  証明の骨: `(F_{ℓ²})ˣ` は位数 `ℓ²−1 = (ℓ−1)(ℓ+1)` の巡回群なので位数ちょうど
  `ℓ+1` の元 `t` を持ち、`c = t^{2ℓ−1}` が行列式 1 のトーラスに入り `c ≠ 1`。

⟹ 段 (2) で要るのは「この存在を `V ∩ U` の言葉に翻訳する」ことで、
`(ℓ+1)/(ℓ+1,3)` の計算は**不要**。

### 段 (2) の残り (更新)

| 主張 | 状態 |
|---|---|
| `(V ∩ U)/(P ∩ U)` が `C_{Q₀}(P)` を中心化 | ⚠ 未 (PSU(3,ℓ) 構造) |
| `V ∩ U ⊂ PW` / `⊂ P × C_W(P)` | ✅ (55) |
| `(V∩U) − (P∩U) ≠ ∅` | ⚠ **存在で足りる** — model 側に `exists_ne_one_mem_psuTorus_torusWeight_eq_one` |
| `U` 側で §3 Cor 2 | ⚠ `U` 側 `Hypothesis` の構成 (段 (2) の本体) |
| `f(ω) = f₁(ω)`, `h(ω) = h₁(ω)` | ✅ (54) |

### ⚠ 次セッションはここから

1. **`U` 側の `Hypothesis` 構成** — 段 (2) の本体。`CentralizerQuotient.lean` の
   `centralizerQuotientHypothesis` が「`C_G(X)` の faithful 商に (A1)-(A3) を与える」
   構成なので、まずそれが `U = O^{2'}(C_G(P))` にも使えるか実測する。
2. 上の 2 つの PSU(3,ℓ) 構造事実 (中心化 / トーラス元の存在) を `V ∩ U` の言葉へ翻訳。
3. 段 (3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (57): 🔍 段 (2) の `U` 側 `Hypothesis` — repo の構成は `C_G(X)/N` 上

実測結果 (`CentralizerQuotient.lean`):

* `centralizerQuotientHypothesis (hXV : X ≤ V) (hA3) :
   Hypothesis (centralizerActionQuotient hyp X) ↥(MulAction.fixedPoints X Ω)`
  — これは **`C_G(X)` の faithful 商 `C_G(X)/N`** 上の `Hypothesis`
  (`N = (C_H(X)).normalCore`)。**`U = O^{2'}(C_G(P))` 上のものではない**。
* 一方 `result.L = primeComplementResidual 2 (centralizerActionQuotient hyp X)` で、
  `CentralizerPSUData.residualQuotientEquiv` は
  `(O^{2'}(C_G(X)) ⧸ Z(·)) ≃* standardPermGroup n`。

⟹ **設計上の帰結**: 書籍は「`U`, `U ∩ H`, `t` に関する `f₁, h₁`」と literal に書くが、
repo で自然なのは **`C_G(P)/N` 上の `Hypothesis` に §3 Cor 2 を当てて `U` へ落とす**
経路。`U` 上に `Hypothesis` を新規構成するより、既存の
`centralizerQuotientHypothesis` を使う方が整合する。

⚠ ただし `IsFGH.eq_of_le` (54) は「同じ `t` を持つ**部分群**の三つ組は外側と一致」
なので、`U ≤ G` の形でそのまま使える。商に移ると `t` の像を追う必要があるので、
**どちらの経路を採るかは段 (2) 実装時の設計判断**。判断材料:
  * 商経路: `Hypothesis` は既存。`t` の像・`Q` の像の対応を追う手間。
  * `U` 直接経路: `IsFGH.eq_of_le` がそのまま効く。`U` 上の `Hypothesis`
    (A1)-(A3) を新規に構成する手間 (`centralizerHypothesisA1` が近い?)。

### ⚠ 次セッションはここから

1. 上の 2 経路を比べて段 (2) の設計を決める。⚠ `centralizerHypothesisA1`
   (`CentralizerQuotient.lean:343` の手前) が `C_G(X)` **そのもの**上の (A1) を
   与えているか実測すること — もしそうなら `U` 直接経路が安い。
2. PSU(3,ℓ) 構造事実 2 つ (中心化 / トーラス元の存在 = (56)) を `V ∩ U` の言葉へ。
3. 段 (3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

### 本セッション (2026-08-01) の総括

§3 完成 → §1 Lemma → §4 の算術全部 → §4 段 (1) の全部品 → 段 (2) の 3 部品、
という順で進んだ。landing した主なもの:

* `stepFive` / `corollaryTwo_of_stepFour` (§3 完成)
* `RankOneBNPairRigidity.lean` (§1 Lemma 一式) + `closure_iUnion_conj_eq_primeComplementResidual`
* `FixedPointDensity.lean` + `PSU3SectionFourArithmetic.lean` (§4 の純算術全部)
* `nonempty_psu3Data_of_orderOf_eq_three` (枝の同定)
* `PSU3SectionFourSetup.lean` (§4 standing hypothesis + 段 (1) の 3 結論 + 段 (2) の 2 部品)
* 一般化 2 件: `natCard_Q0_eq_pow` (Artin, `W = ⊥` → `X ⊓ W = ⊥`) /
  `eq_one_of_conj_eq_mul_Q0_of_mem_W` (固定点自由性, `V = W` 不要版)
* `IsFGH.eq_of_le` (canonical form の一意性)

⚠ 訂正 1 件: `O^{2'}` は repo にある (`primeComplementResidual`)。

## 2026-08-01 (58): 段 (2) の経路判定 — **商経路が正しい** (書籍の `U/(P∩U)` と一致)

`centralizerHypothesisA1 (hXV : X ≤ V) :
 HypothesisA1 ↥(Subgroup.centralizer (X : Set G)) ↥(fixedPoints X Ω)`
は **`C_G(X)` そのもの**の上の (A1) で、しかも `htC : hyp.t ∈ C` — **同じ対合 `t`**
が `C_G(X)` に居る (`CentralizerInduction.lean:246`)。`t` は 2-元なので
`t ∈ O^{2'}(C_G(P)) = U` でもある。

⟹ `IsFGH.eq_of_le` (54) は `Q' = C_Q(P)`, `D' = C_D(P)` でそのまま効く。

⚠ **しかし (A2) (忠実性) は `C_G(X)` 自身では成り立たない** — repo が
`C_G(X)/N` (`N = (C_H(X)).normalCore`) に移るのはまさにそのため。
§3 Cor 2 (`corollaryTwo_of_stepFour`) は完全な `Hypothesis` を要求するので、
`U` 上に直接は載らない。

⟹ **書籍の `U/(P∩U) ≅ PSU(3,ℓ)` という書き方自体が商を取っている**ことに注意。
repo の `centralizerActionQuotient` と `result.L` がその商に対応する。
**段 (2) の正しい経路は商経路** (`C_G(P)/N` 上の `Hypothesis` に §3 Cor 2 を当て、
得た `ω̄` を `U` に持ち上げる)。`IsFGH.eq_of_le` は持ち上げ後の
「`f(ω) = f₁(ω)`」に使う。

### ⚠ 次セッションの具体手順 (段 (2))

1. `centralizerQuotientHypothesis s4.P_le_V hA3` で `C_G(P)/N` 上の `Hypothesis` を得る。
2. そこに `corollaryTwo_of_stepFour` を当てて `ω̄ ∈ Q̄ − Q̄₀` と
   `f̄(ω̄) = ζ̄⁻¹ω̄⁻¹ζ̄`、`h̄(ω̄) = ζ̄³` を得る。
   ⚠ 段 (4) の被覆 `hcover` をその `Hypothesis` に対して供給する必要がある
   (= §3 が `C_G(P)/N` 側でも成り立つこと)。ここが段 (2) の実質。
3. 商から `U` への持ち上げ: `N ≤ C_H(P)` の元だけずれるので、書籍の
   `f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)` / `h₁(ω) ∈ ζ₁³(P ∩ U)` という**剰余類の形**に対応する。
4. `IsFGH.eq_of_le` で `f₁ → f`、`h₁ → h`。

## 2026-08-01 (59): §4 — `t ∈ U` landing

書籍 p.133 段 (2) が `f₁`, `h₁` を「`U`, `U ∩ H`, `t` に関して」取ることの正当性:

| 定理 | 内容 |
|---|---|
| `SectionFourSetup.t_mem_centralizer` | `t` は `P ≤ V` を中心化 (`commute_t_of_mem_V`) |
| `SectionFourSetup.t_mem_primeComplementResidual` | `t` は対合 ⟹ 2-元 ⟹ `C_G(P)` の Sylow 2 に含まれる ⟹ `U` に居る |

⚠ `IsPGroup 2 ↥(zpowers t)` は **位数経由**が素直 (`orderOf t ∣ 2` →
`Nat.card_zpowers` + `IsPGroup.of_card`)。zpow の指数計算に降りると `zpow_mul` の
向きで詰まる。

### ⚠ 次セッションはここから

1. **段 (2) の本体** — (58) の 4 手順:
   (a) `centralizerQuotientHypothesis s4.P_le_V hA3` で `C_G(P)/N` 上の `Hypothesis`
   (b) そこに `corollaryTwo_of_stepFour` を当てる ⟸ **`hcover` の供給が実質**
   (c) 商から `U` への持ち上げ (書籍の `f₁(ω) ∈ ω^{-ζ₁}(P∩U)` = 剰余類の形)
   (d) `IsFGH.eq_of_le` で `f₁ → f`、`h₁ → h`
2. PSU(3,ℓ) 構造事実 2 つ (中心化 / トーラス元の存在 = (56)) を `V ∩ U` の言葉へ。
3. 段 (3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (60): 段 (2)(b) の `hcover` — §3 の段 (4) 鎖は**汎用**、残りは配線

`hcover` (= `corollaryTwo_of_stepFour` が要る「段 (4) の被覆」) を商 `Hypothesis` に
供給する道筋を実測した。§3 の段 (4) は `PSU3InverseFormula.lean` の 5 段鎖:

| 定理 | 行 | 役割 |
|---|---|---|
| `stepFour_star` | 163 | `(∗∗)` の組み立て |
| `stepFour_base` | 312 | `γ(a) = 1/(a+w)` |
| `stepFour_pointwise` | 378 | 点ごとの逆元公式 |
| `stepFour_at_omega` | 451 | `ω` での公式 |
| `stepFour_cover` | 867 | ファイバー被覆 = **`hcover` そのもの** |

**5 段とも `(hyp : Hypothesis G Ω)` と standing data のみに依存する汎用定理**で、
ambient `G` に固有の仮定は無い。⟹ **商 `Hypothesis` にもそのまま適用できる**。

⟹ 段 (2)(b) の実質は「商 `qhyp` に対する §2/§3 の standing data を揃える」配線:
`exists_standardModel` (Ch. III §3 Prop) を `qhyp` に当てて `φ`,`Φ`,`Θ`,`hquot`,`d`,
`hequiv` … を得て、上の鎖に流す。⚠ `exists_standardModel` 自身が
`hst` (`|s·t| = 3`) / `hm` / `hQ0card` / `hcardQ` / `inductionHypothesis` / `x₀` を
要求するので、それらを `qhyp` について供給するのが前段。

⟹ **新しい数学は無く、多量の仮説スレッディング**。fresh context で一気にやるのが吉。

### ⚠ 次セッションの推奨手順

1. `qhyp := centralizerQuotientHypothesis s4.P_le_V hA3` を置く。
2. `qhyp` に対する `exists_standardModel` の 6 前提を供給する
   (`hst` は `orderOf (s·t) = 3` の商版 — `orderOf_distinguishedInvolution_mul_t_of_*`
   群が既に商と ambient を往復しているので、そこから取れるはず。要実測)。
3. 段 (4) 鎖 → `hcover` → `corollaryTwo_of_stepFour` で `ω̄` を得る。
4. 商から `U` へ持ち上げ、`IsFGH.eq_of_le` で `f₁ → f`。

## 2026-08-01 (61): 商 `qhyp` の `hst` は**既にある** — 段 (2)(b) の前提を個別に追う

`exists_standardModel` が `qhyp` に要求する 6 前提の出どころを追った。

### `hst` (= `orderOf (s·t) = 3`) — ✅ 既存

`orderOf_distinguishedInvolution_mul_t_of_psu3Target (hyp) (L) (hLnormal) (hLodd)
 (data : PSU3InductionTarget L) : orderOf (hyp.distinguishedInvolution * hyp.t) = 3`
(`CentralizerPSUDistinguished.lean:161`) は **任意の `hyp`** について述べられている。
⟹ `hyp := qhyp`, `L := result.L`, `data` = 枝選択 (45) の出力、で
**`qhyp` の `hst` がそのまま出る**。

⟹ 依存の向きは:
```
ambient の orderOf (s·t) = 3  +  exponent 判別子 (48)(49)
  → nonempty_psu3Data_of_orderOf_eq_three (45)   [枝選択]
  → PSU3InductionTarget data
  → orderOf_distinguishedInvolution_mul_t_of_psu3Target  [qhyp の hst]
  → exists_standardModel for qhyp
  → §3 の段 (4) 鎖 (60)  → hcover  → corollaryTwo_of_stepFour
```

### 残る 5 前提 (`qhyp` について)

| 前提 | 見込みの出どころ |
|---|---|
| `hm : m ≠ 0` | `data.one_lt_n` (`PSU3InductionTarget` のフィールド) |
| `hQ0card : \|Q₀\| = 2^m` | `CentralizerPSUData.natCard_cQ0_eq_baseField` 周り (要実測) |
| `hcardQ : \|Q\| = \|Q₀\|³` | 同上 / PSU(3,q) の Sylow 2 の位数 |
| `inductionHypothesis` | 商は `G` より小さい (`card_centralizerActionQuotient_lt`) ので ambient の帰納法仮説から継承できるはず (要実測) |
| `x₀ ∈ Z(Q̄)`, `x₀ ≠ 1` | `exists_involution_mem_center_Q` (`QStructure.lean:220`) の商版 |

⟹ **すべて既存資産の射程内**。段 (2)(b) は依然として配線だが、行き先が全部特定できた。

### ⚠ 次セッションはここから

上の表の 5 前提を 1 つずつ実測して埋め、`exists_standardModel` for `qhyp` を組む。
その後は (60) の鎖で `hcover` → `corollaryTwo_of_stepFour` → 段 (2) が閉じる。

## 2026-08-01 (62): 🔍 `CentralizerPSUData` が `exists_standardModel` の前提を**ほぼ全部持っていた**

`CentralizerPSUData` (`CentralizerTrichotomy.lean:144-175`) の全フィールドを実測:

| フィールド | 内容 | §4 での用途 |
|---|---|---|
| `residualQuotientEquiv` | `(O^{2'}(C) ⧸ Z(·)) ≃* ProjectiveUnitary.standardPermGroup n` | 段 (1) の `U/Z(U) ≅ PSU(3,ℓ)` |
| `cQEquivRoot` | `C_Q(X) ≃* ProjectiveUnitary.RootGroup n` | PSU(3,ℓ) 構造事実の供給元 |
| `distinguishedProduct_order` | `orderOf (s·t) = 3` | 枝選択の確認 |
| **`cQ_isSuzuki2Group`** | `IsSuzuki2Group ↥(C_Q(X))` | ⟹ `sq_ne_one_of_not_mem_Q0` の `hQsuz` |
| **`natCard_cQ0_eq_baseField`** | `\|C_{Q₀}(X)\| = \|BaseField n\|` (= `2^n`) | ⟹ `hQ0card` |
| **`natCard_cQ_eq_cQ0_cube`** | `\|C_Q(X)\| = \|C_{Q₀}(X)\|³` | ⟹ `hcardQ` |
| `natCard_cQ_eq_baseField_cube` | `\|C_Q(X)\| = \|BaseField n\|³` | 同上の別形 |

⟹ **`exists_standardModel` が要る 6 前提のうち 4 つ (`hst`, `hm`, `hQ0card`,
`hcardQ`) が枝データから直接出る**。残りは `inductionHypothesis` の継承と `x₀`。

⚠ 1 点だけ翻訳が要る: これらは `C_Q(X)` / `C_{Q₀}(X)` (= `hyp.Q.subgroupOf C` 等)
についての主張で、商 `qhyp.Q` そのものではない。`N ≤ C_D(X)` かつ `Q ⊓ D = 1` なので
`C_Q(X) → C_G(X)/N` は単射のはずで、位数はそのまま移る (**要実測**)。

### 段 (2)(b) の前提表 (最終形)

| 前提 | 出どころ | 状態 |
|---|---|---|
| `hst` | `orderOf_distinguishedInvolution_mul_t_of_psu3Target` (61) | ✅ |
| `hm : n ≠ 0` | `data.one_lt_n` | ✅ |
| `hQ0card` | `natCard_cQ0_eq_baseField` + `\|BaseField n\| = 2^n` | ✅ (要位数補題) |
| `hcardQ` | `natCard_cQ_eq_cQ0_cube` | ✅ |
| `inductionHypothesis` | `card_centralizerActionQuotient_lt` から継承 | ⚠ 要実測 |
| `x₀` | `exists_involution_mem_center_Q` の商版 | ⚠ 要実測 |
| `C_Q(X) ≅ qhyp.Q` の位数移送 | `centralizerQuotientHypothesisA1` の構成 | ⚠ 要実測 |

### ⚠ 次セッションはここから

上表の ⚠ 3 つを実測して埋め、`exists_standardModel` for `qhyp` を組む。
そこから先は (60) の鎖で段 (2) が閉じる。

## 2026-08-01 (63): 帰納法仮説の商への継承 landing + 残り 2 点の実測

`theoremAInductionBelow_centralizerActionQuotient` — `TheoremAInductionBelow G Ω` は
`G` より小さい群**すべて**を量化するので、商が `G` より小さいことから 2 行で継承。
⚠ `TheoremAInductionBelow` は `CentralizerInductionBridge.lean` 定義で
`CentralizerQuotient.lean` からは見えない → §4 の leaf に置いた。

### 残り 2 点の実測結果

* **`x₀`**: `exists_involution_mem_center_Q` (`QStructure.lean:220`) は
  `∃ u ∈ Q, u² = 1 ∧ u ≠ 1 ∧ ∀ v ∈ Q, u v = v u` を**任意の `hyp`** について与える。
  ⟹ `qhyp` にそのまま適用できる。`exists_standardModel` が要る
  `x₀ : ↥(center Q)`, `x₀ ≠ 1` はこれから作れる。✅
* **`C_Q(X)` ↔ `qhyp.Q` の移送**: `centralizer_cQ_isPGroup_of_quotient hXV
  (hQbar : IsPGroup 2 qhyp.Q) : IsPGroup 2 ↥(hyp.Q.subgroupOf C)`
  (`CentralizerInductionBridge.lean:185`) が既に**商 → 中心化群**方向の移送を持つ。
  位数版が要るならこの近所を辿る。⚠ 唯一残る要実測点。

### 段 (2)(b) の前提表 (最終)

| 前提 | 状態 |
|---|---|
| `hst` | ✅ `orderOf_distinguishedInvolution_mul_t_of_psu3Target` |
| `hm` | ✅ `data.one_lt_n` |
| `hQ0card` / `hcardQ` | ✅ `CentralizerPSUData` のフィールド (要位数移送) |
| `inductionHypothesis` | ✅ **今回** |
| `x₀` | ✅ `exists_involution_mem_center_Q` (汎用) |
| `C_Q(X) ↔ qhyp.Q` 位数移送 | ⚠ 唯一の要実測点 |

⟹ **段 (2)(b) の前提はほぼ全部埋まった**。次は位数移送を確認して
`exists_standardModel` for `qhyp` を組み、(60) の鎖で段 (2) を閉じる。

## 2026-08-01 (64): 🔍 位数移送 — `Q` 版はあり、**`Q₀` 版が唯一の隙間**

* `centralizerQQuotientEquiv (hXV : X ≤ V) :
   ↥(hyp.Q.subgroupOf C) ≃* ↥(centralizerQuotientHypothesisA1 hXV).Q`
  (`CentralizerInductionBridge.lean:148`) — **`C_Q(X) ≃* Q̄` の明示同型**が既にある。
  理由は「`𝒩(C_G(X)) ≤ C_D(X)` かつ `C_Q(X) ∩ C_D(X) = 1`」。
  ⟹ `hcardQ` に要る位数移送はこれで済む (`Nat.card_congr`)。

* ⚠ **`Q₀` 版は無い**。`hQ0card` は `Nat.card ↥qhyp.Q0 = 2^m` を要求するが、
  `CentralizerPSUData.natCard_cQ0_eq_baseField` が与えるのは
  `Nat.card ↥(hyp.Q0.subgroupOf C)`。⟹ **`centralizerQ0QuotientEquiv` が要る**。

  証明は `centralizerQQuotientEquiv` の写経でよいはず: `Q₀ ≤ Q` なので
  `C_{Q₀}(X) ∩ C_D(X) ≤ C_Q(X) ∩ C_D(X) = 1`、単射性は同じ議論。全射性は
  `qhyp.Q0` の定義次第 (`HypothesisA1.Q0` がどう構成されているか要確認)。

⟹ **段 (2)(b) の前提で残るのはこれ 1 つだけ**。

### ⚠ 次セッションはここから

1. **`centralizerQ0QuotientEquiv` を書く** (`centralizerQQuotientEquiv` の写経、
   `CentralizerInductionBridge.lean` に置く)。⚠ 先に `HypothesisA1.Q0` /
   `centralizerQuotientHypothesisA1` の `Q0` フィールドがどう定義されているか実測。
2. `exists_standardModel` for `qhyp` を組む (前提はこれで全部そろう)。
3. (60) の段 (4) 鎖 → `hcover` → `corollaryTwo_of_stepFour` → 段 (2) が閉じる。
4. 段 (3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済。

## 2026-08-01 (65): 🔍 `Q₀` は**導出定義** — `Q₀` 版同型は `Q` 版の制限で出る

`Hypothesis.Q0` は構造フィールドではなく **導出定義** (`QStructure.lean:293`):

```
def Q0 : Subgroup G where carrier := {x | x ^ 2 = 1 ∧ x ∈ hyp.H}
```
(= `(H ∩ I) ∪ {1}`、`H` の対合たち + 単位元。書籍 p.103 の標準記法)

⟹ `qhyp.Q0 = {x̄ | x̄² = 1 ∧ x̄ ∈ qhyp.H}` も自動的にこの形。

⟹ **`centralizerQ0QuotientEquiv` は `centralizerQQuotientEquiv` の制限で出る**:
`C_Q(X) ≃* Q̄` は単射なので `x² = 1 ↔ x̄² = 1` が両方向で成り立ち、あとは
`x ∈ C_H(X) ↔ x̄ ∈ qhyp.H` の対応が要るだけ。**新しい幾何は不要**。

⚠ 次に実測すべきは `centralizerQuotientHypothesisA1` の `H` フィールドが
`C_H(X)` の像として定義されているか (`HypothesisA1.quotientOfKernel` の構成)。
そこが確認できれば `Q₀` 版はほぼ機械的に書ける。

### 段 (2)(b) の残り (最終形)

**唯一**: `centralizerQ0QuotientEquiv` (= `C_{Q₀}(X) ≃* Q̄₀`)。
これが入れば `exists_standardModel` for `qhyp` の 6 前提が全部そろい、
(60) の段 (4) 鎖で `hcover` → `corollaryTwo_of_stepFour` → 段 (2) が閉じる。

### ⚠ 次セッションはここから

1. `HypothesisA1.quotientOfKernel` の `H` フィールドを実測。
2. `centralizerQ0QuotientEquiv` を書く。
3. `exists_standardModel` for `qhyp` → 段 (4) 鎖 → 段 (2)。

## 2026-08-01 (66): 🔍 `H` の対応も既存 — 段 (2)(b) の材料が**全部名指しできた**

`HypothesisA1.quotientOfKernel` (`CentralizerQuotient.lean:125`) の構成を実測:

* `H := h.H.map π` (`π = QuotientGroup.mk' N`) — **`H̄` は `H` の像**
* 構成の中に `mem_H_of_mk_mem (a) (ha : π a ∈ Hbar) : a ∈ h.H` があり、
  根拠は `Subgroup.comap_map_eq_self hkerH` (`π.ker = N ≤ H`)。
  ⟹ **`x ∈ C_H(X) ↔ x̄ ∈ H̄` が両方向で取れる** (→ は `Subgroup.mem_map`)。
* 同様に `Q := h.Q.map π`、`D := h.D.map π`。

⟹ `centralizerQ0QuotientEquiv` の材料が全部そろった:
  * `x² = 1 ↔ x̄² = 1` — `centralizerQQuotientEquiv` の単射性
  * `x ∈ C_H(X) ↔ x̄ ∈ H̄` — 上記
  * `Q₀` の定義 `{x | x² = 1 ∧ x ∈ H}` (65)

### 段 (2)(b) の材料表 (完成)

| 前提 | 出どころ | 状態 |
|---|---|---|
| `hst` | `orderOf_distinguishedInvolution_mul_t_of_psu3Target` | ✅ |
| `hm` | `data.one_lt_n` | ✅ |
| `hcardQ` | `CentralizerPSUData.natCard_cQ_eq_cQ0_cube` + `centralizerQQuotientEquiv` | ✅ |
| `hQ0card` | `natCard_cQ0_eq_baseField` + **`centralizerQ0QuotientEquiv` (未実装)** | ⚠ |
| `inductionHypothesis` | `theoremAInductionBelow_centralizerActionQuotient` (63) | ✅ |
| `x₀` | `exists_involution_mem_center_Q` (汎用) | ✅ |

⟹ **未実装は `centralizerQ0QuotientEquiv` ただ 1 つ**で、その材料も全部特定済み。

### ⚠ 次セッションはここから (実装フェーズ)

1. `centralizerQ0QuotientEquiv : ↥(hyp.Q0.subgroupOf C) ≃* ↥(qhyp.Q0)` を書く
   (`CentralizerInductionBridge.lean`、`centralizerQQuotientEquiv` の隣)。
2. `exists_standardModel` for `qhyp` を組む。
3. §3 段 (4) 鎖 (60) → `hcover` → `corollaryTwo_of_stepFour` → **段 (2) が閉じる**。
4. 段 (3)(4) → (5)(6) → `sectionFour_solve` 以降は landing 済 ⟹ **§4 完成**。

## 2026-08-01 (67): ⚠ `Q₀` 版同型は**単なる制限ではない** — 全射性に奇位数論法が要る

`centralizerQQuotientEquiv` の証明 (`CentralizerInductionBridge.lean:148-180`) は
`Q_L ≃* Q_L.map pi` を `MonoidHom.subgroupMap` + 単射性
(`Q_L ⊓ D_L = ⊥` と `N ≤ D_L` から) + 全射性 (自動) で作る。

`Q₀` 版で**単射性は同じ**でよい (`Q0_L ≤ Q_L` なので `Q0_L ⊓ D_L = ⊥`)。
⚠ **問題は目標側**: 欲しいのは `↥Q0_L ≃* ↥qhyp.Q0` だが、上の構成が与えるのは
`↥Q0_L ≃* ↥(Q0_L.map pi)`。そして

* `Q0_L.map pi ≤ qhyp.Q0` — 易しい (`x² = 1 ⟹ x̄² = 1`、`x ∈ H ⟹ x̄ ∈ H̄`)
* `qhyp.Q0 ≤ Q0_L.map pi` — ⚠ **非自明**。`x̄² = 1` かつ `x̄ ∈ H̄` から
  `x ∈ C_H(X)` は取れる (`comap_map_eq_self`) が、`x² ∈ N` であって `x² = 1` ではない。

### 全射性の正しい論法 (次セッション用)

`N ≤ C_D(X)` で **`D` は奇位数**なので `|N|` は奇数。`x` の位数を `2^a·m`
(`m` 奇) と書き `y := x^m` とすると:
* `x̄² = 1` かつ `m` 奇 ⟹ `x̄^m = x̄`、よって `π y = x̄`
* `y² = x^{2m}` は 2-元で、`x̄² = 1` から `x^{2m} ∈ N`。`N` 奇位数ゆえ `x^{2m} = 1`
⟹ `y ∈ Q0_L` かつ `π y = x̄`。∎

⟹ **`centralizerQ0QuotientEquiv` は写経ではなく、この奇位数論法を要する**
(単射性だけ `Q` 版から借りる)。⚠ 「`Q₀` 版は `Q` 版の制限で出る」と書いた (65) は
**単射性についてのみ正しく、全射性については誤り**だった。

### ⚠ 次セッションはここから

1. `|N|` が奇数であることを repo で実測 (`N ≤ C_D(X)`、`D` 奇位数 =
   `hyp.odd_card_D` 系)。
2. 上の 2-part 論法で `qhyp.Q0 = Q0_L.map pi` を示す。
3. `centralizerQ0QuotientEquiv` → `exists_standardModel` for `qhyp` →
   段 (4) 鎖 → `hcover` → 段 (2)。

## 2026-08-01 (68): `|N|` 奇数の根拠 — `Hypothesis.D_odd` は**構造フィールド**

`D_odd : Odd (Nat.card D)` は `Hypothesis` の**構造フィールド** (`Basic.lean:161`)。
`N ≤ hyp.D.subgroupOf L` (`centralizerQQuotientEquiv` の `hNleD`) なので
`|N| ∣ |D|` で `|N|` は奇数。⟹ (67) の 2-part 論法がそのまま走る。

### `centralizerQ0QuotientEquiv` の材料 (完成)

| 部分 | 根拠 |
|---|---|
| 単射性 | `Q0_L ≤ Q_L` + `Q_L ⊓ D_L = ⊥` (`Q` 版と同じ) |
| `Q0_L.map π ≤ qhyp.Q0` | `x² = 1 ⟹ x̄² = 1`、`Subgroup.mem_map` |
| `qhyp.Q0 ≤ Q0_L.map π` | `comap_map_eq_self` で `x ∈ C_H(X)` を取り、`|N|` 奇 (`D_odd`) から `y := x^m` (`m` = `x` の位数の奇部分) が `y² = 1`、`π y = x̄` |

⟹ **材料は全部そろった。次セッションは実装のみ**。

### 本セッション (2026-08-01) の最終状態

**landing した Lean 成果** (すべてフルビルド green・lint 純ゼロ・axiom-clean):

1. §3 完成 — `stepFive` / `corollaryTwo_of_stepFour`
2. §1 の Lemma 一式 — `RankOneBNPairRigidity.lean` (新 leaf) +
   `closure_iUnion_conj_eq_primeComplementResidual` + `IsFGH.eq_of_le`
3. §4 の純算術**全部** — `FixedPointDensity.lean` + `PSU3SectionFourArithmetic.lean`
   ((5)(6)⟹(7)(8) / 分母≠0 / (9) / shift trick / `μ²=id` / `λ=1` / 奇位数)
4. §4 段 (1) — `nonempty_psu3Data_of_orderOf_eq_three` (枝選択) +
   `PSU3SectionFourSetup.lean` (standing hypothesis + 3 結論 + Glauberman)
5. §4 段 (2) の部品 — `V ∩ U ⊆ P × C_W(P)` / `t ∈ U` /
   `theoremAInductionBelow_centralizerActionQuotient`
6. 一般化 2 件 — `natCard_Q0_eq_pow` (Artin) / `eq_one_of_conj_eq_mul_Q0_of_mem_W`

**残り**: `centralizerQ0QuotientEquiv` 1 本 → `exists_standardModel` for `qhyp` →
段 (4) 鎖 → `hcover` → 段 (2) → 段 (3)-(10) は landing 済 ⟹ **§4 完成**。

⚠ 訂正 2 件を記録済: `O^{2'}` は repo にある (43) / `Q₀` 版同型は制限では出ない (67)。

## 2026-08-01 (69): 🎯 奇位数核を通した対合の持ち上げ landing

`exists_sq_eq_one_of_odd_kernel` — `|N|` 奇なら `L/N` の対合は `L` の対合に持ち上がる。
(67) で特定した `Q₀` 版同型の**全射性の crux**がこれで埋まった。

証明: `x̄ = π x` を取ると `x² ∈ N`、`d := orderOf (x²)` は `|N|` を割り奇数。
`y := x^d` が `y² = (x²)^d = 1` かつ `ȳ = x̄^d = x̄`。

⚠ 実装メモ: `set d := …` すると `obtain ⟨k, rfl⟩` が subst できない (let 束縛)。
`orderOf …` を直書きして `obtain ⟨k, hk⟩; rw [hk]`。
`Odd (a*b) → Odd a` は `(Nat.odd_mul.mp ·).1`。

### `centralizerQ0QuotientEquiv` の残り

| 部分 | 状態 |
|---|---|
| 単射性 | ✅ `Q` 版の議論をそのまま (`Q0_L ≤ Q_L` + `Q_L ⊓ D_L = ⊥`) |
| `Q0_L.map π ≤ qhyp.Q0` | ✅ 易しい方向 |
| `qhyp.Q0 ≤ Q0_L.map π` | ✅ **今回の `exists_sq_eq_one_of_odd_kernel`** + `comap_map_eq_self` |
| 組み立て | ⚠ 残り (`|N|` 奇は `D_odd` から、`hNleD` は `Q` 版の証明中にある) |

⟹ **数学は全部埋まった。残るのは組み立てのみ**。

### ⚠ 次セッションはここから

1. `centralizerQ0QuotientEquiv` を組む (材料は上表)。
2. `exists_standardModel` for `qhyp` → 段 (4) 鎖 → `hcover` → 段 (2)。
3. 段 (3)-(10) は landing 済 ⟹ **§4 完成**。

## 2026-08-01 (70): 🎯 `Q₀` 版の全射性が集合レベルで閉じた

`map_involutionSet_eq_of_odd_kernel` — 核 `N ≤ H` 奇位数なら
`π '' {x | x² = 1 ∧ x ∈ H} = {z | z² = 1 ∧ z ∈ H.map π}`。

`Q₀` は導出部分群 `{x | x² = 1 ∧ x ∈ H}` (65) なので、これが
`centralizerQQuotientEquiv` の `Q₀` 版の**集合レベルの中身**そのもの。

⚠ そのために (69) の補題を**逆像を保つ形**に強化した:
`exists_pow_sq_eq_one_of_odd_kernel` は「与えられた逆像 `x` の**奇冪**で置き換え
られる」と言うので `x ∈ H ⟹ x^d ∈ H` が保たれる。素の版は 3 行の系。
⚠ 最初の版 (逆像を `mk'_surjective` で勝手に取る) では `y ∈ H` が言えず、
`⊇` の証明が通らなかった — **持ち上げ補題は逆像を引数に取る形で書くべき**。

### `centralizerQ0QuotientEquiv` の残り

数学は全部済み。残るのは `qhyp.Q0` の定義展開と `Subgroup` レベルへの持ち上げ:
* `qhyp.H = (C_H(X)).map π` (`HypothesisA1.quotientOfKernel` の `H := h.H.map π`)
* `qhyp.Q0 = {z | z² = 1 ∧ z ∈ qhyp.H}` (導出定義)
* ⟹ 上の集合等式が `(Q0_L).map π = qhyp.Q0` を与える (`Subgroup.ext` + `coe`)
* 単射性は `Q` 版と同じ ⟹ `MulEquiv.ofBijective`

### ⚠ 次セッションはここから

1. 上の 4 点で `centralizerQ0QuotientEquiv` を組む。
2. `exists_standardModel` for `qhyp` → 段 (4) 鎖 → `hcover` → 段 (2)。
3. 段 (3)-(10) は landing 済 ⟹ **§4 完成**。

## 2026-08-01 (71): 🎯 `centralizerQ0QuotientEquiv` landing + 段 (2)(b) の材料が**全部埋まった**

### landing した Lean (すべて `PSU3SectionFourSetup.lean`、leaf build green)

| 定理 | 内容 |
|---|---|
| `coe_Q0_subgroupOf_centralizer` | `C_{Q₀}(X)` を「`C_H(X)` の対合部分群」の形へ |
| `map_centralizer_Q0_eq_quotient_Q0` | `(C_{Q₀}(X)).map π = Q̄₀` (全射性 = (70) の集合等式) |
| **`centralizerQ0QuotientEquiv`** | `C_{Q₀}(X) ≃* Q̄₀` — (67)〜(70) の crux |
| `natCard_quotient_Q0_eq` / `natCard_quotient_Q_eq` | 位数移送 (Q₀ 版 / Q 版) |
| `natCard_quotient_Q0_eq_pow` | `hQ0card` = `\|Q̄₀\| = 2ⁿ` |
| `natCard_quotient_Q_eq_Q0_cube` | `hcardQ` = `\|Q̄\| = \|Q̄₀\|³` |
| `isSuzuki2Group_quotient_Q` | `hQsuz` を `C_Q(X)` から `Q̄` へ移送 |
| `exists_center_Q_ne_one` | `x₀ : Z(Q)`, `x₀ ≠ 1` (汎用) |
| **`psu3Numerics_and_standingData_centralizerQuotient`** | 上記を枝データから一括で組む |

⚠ 実装メモ: 単射性は `Q₀ ≤ Q` で `Q` 版に帰着するが、**全射性は写経では出ない**
((67) の訂正どおり)。`Q̄₀` は `C_{Q₀}(X)` の像として定義されているのでなく
`H̄` の**対合部分群**なので、`map_involutionSet_eq_of_odd_kernel` (70) が要る。

### 🔍 ⚠ 重要な実測訂正: §2/§3 の standing data には **producer が在る**

(60) は「`exists_standardModel` が要る 6 前提」を追っていたが、`exists_standardModel`
自身が section variable として `s : hyp.LemmaFiveSetup m` と `M : hyp.QuotientFieldModel m`
を取る。これらは repo 全体で**仮説としてしか現れない**ので一時「producer 無し =
§2/§3 は standing data に条件付き」と読んだが、**誤り**:

| producer | 場所 | 前提 |
|---|---|---|
| `lemmaFiveSetup_of_orderThree_of_mem_W` | `TypeBFromW.lean:254` | `w ∈ W#`, `hst`, `hQsuz`, `hm`, `hQ0card`, `hcardQ`, `ih` |
| `nonempty_quotientFieldModel_of_orderThree` | `QuotientKWField.lean:397` | 同上 + `s : LemmaFiveSetup m` |

⟹ **`hst`/`hQsuz`/`hm`/`hQ0card`/`hcardQ`/`ih` + `w ∈ W#` から standing data 一式が出る**。
`psu3Numerics_and_standingData_centralizerQuotient` はこの鎖を商 `qhyp` について
一括で通したもの。

### 🎯 段 (2) の残り = **`W̄ ≠ 1` ただ 1 つ**

書籍 p.133 段 (2) の証明 (原文):

> By the structure of `PSU(3,ℓ)`, `(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`. Thus, by
> the theorem of Galois, `V ∩ U ⊆ P W` and, since `U ⊆ C_G(P)`, `V ∩ U ⊆ P × C_W(P)`.
> **Furthermore, `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` since `ℓ > 2`.**
> Let `ζ₁ ∈ (V ∩ U) − (P ∩ U)` and `ζ ∈ C_W(P)` be such that `ζ₁ ∈ ζP`.
> If `f₁` and `h₁` denote the mappings `f` and `h` relative to `U`, `U ∩ H` and `t`,
> then, by Corollary 2 of the proposition of §3, there is an element `ω ∈ (Q − Q₀) ∩ U`
> such that `f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)` and `h₁(ω) ∈ ζ₁³(P ∩ U)`. By the uniqueness of the
> canonical form of an element of `G − H`, `f(ω) = f₁(ω) = ω^{-ζ₁} = ω^{-ζ}` and
> `h(ω) = h₁(ω) ∈ ζ³ …`.

⟹ 対応表:

| 書籍の段 | repo |
|---|---|
| `(V∩U)/(P∩U)` が `C_{Q₀}(P)` を中心化 ⟹ `V ∩ U ⊆ PW` | `inf_le_sup_W_of_centralizes` ✅ |
| `V ∩ U ⊆ P × C_W(P)` | `inf_le_sup_centralizer_W` ✅ |
| **`\|(V∩U)/(P∩U)\| = (ℓ+1)/(ℓ+1,3) ≠ 1`** | ⚠ **未** — PSU(3,ℓ) トーラス構造事実 |
| §3 Cor 2 を `U` (= 商) に当てる | `psu3Numerics_and_standingData_centralizerQuotient` + `exists_standardModel` + (60) の段 (4) 鎖 ✅材料 |
| canonical form の一意性で `f₁ → f` | `IsFGH.eq_of_le` ✅ |

⚠ また `corollaryTwo_of_stepFour` は `hVW : V = W` を要求するが、**商側ではこれが
定理**になる: `V ∩ U ⊆ P × C_W(P)` を `P` で割ると `V̄ ≤ W̄` (`inf_le_sup_centralizer_W`
がその材料)。逆は `W ≤ V` (`W_le_V`) から。

### ⚠ 次セッションはここから

1. **PSU(3,ℓ) のトーラス構造事実** — `|(V∩U)/(P∩U)| = (ℓ+1)/(ℓ+1,3) > 1` (`ℓ > 2`)。
   供給元は `CentralizerPSUData.residualQuotientEquiv` (= `U/Z(U) ≃* standardPermGroup n`)
   と `ProjectiveUnitary` の標準モデル。これが `w ∈ W̄`, `w ≠ 1` を与える。
2. `qhyp.V = qhyp.W` を `inf_le_sup_centralizer_W` + `W_le_V` から。
3. `exists_standardModel` for `qhyp` → (60) の段 (4) 鎖 → `hcover` →
   `corollaryTwo_of_stepFour` → `ω̄`。
4. 商から `U` へ持ち上げ + `IsFGH.eq_of_le` ⟹ **段 (2) が閉じる**。
5. 段 (3)-(10) は landing 済 ⟹ **§4 完成**。

## 2026-08-01 (72): 🎯 段 (2) の PSU(3,ℓ) 構造事実は **2 つに整理された**

`V = W` の中身を特定して、書籍の 2 つの「by the structure of PSU(3,ℓ)」を
同一の対象についての主張にまとめた。

### `V = W` ⟺ `V ≤ C(Q₀)` (landing)

* `W_eq_centralizer_involutions_H` (`CentralizerStructure.lean:241`) は
  `W = D ⊓ C({x | x² = 1 ∧ x ≠ 1 ∧ x ∈ H})`。
* `Q₀ = {x | x² = 1 ∧ x ∈ H}` は同じ集合 + `1` で、`1` は誰でも中心化する
  ⟹ **`W_eq_inf_centralizer_Q0` : `W = D ⊓ C(Q₀)`**。
* `W ≤ V` (`W_le_V`) と `V ≤ D` (`V_le_D`) は自明なので
  ⟹ **`V_eq_W_iff_le_centralizer_Q0` : `V = W ↔ V ≤ C(Q₀)`**。

⚠ 別ルートの確認: `ker_conjQ0 : conjQ0.ker = W.subgroupOf D` (`KCyclic.lean:96`)
も同じことを言っている (`W` = `D` のうち `Q₀` に自明に作用するもの)。

### ⟹ 段 (2) の残りは商 `qhyp` についての **2 つ**だけ

| # | 主張 | 用途 | 書籍の根拠 |
|---|---|---|---|
| **(A)** | `V̄ ≤ C(Q̄₀)` | `hVW : qhyp.V = qhyp.W` (§3 の全 endpoint が担ぐ) | 「`(V∩U)/(P∩U)` centralizes `C_{Q₀}(P)`」 |
| **(B)** | `V̄ ≠ 1` | `ζ ∈ W̄#` (= `w ∈ W̄`, `w ≠ 1`) | 「`\|(V∩U)/(P∩U)\| = (ℓ+1)/(ℓ+1,3) ≠ 1` since `ℓ > 2`」 |

(A) が入れば `V̄ = W̄` なので (B) の `V̄ ≠ 1` がそのまま `W̄ ≠ 1` を与える。
⟹ **(A) と (B) の 2 本で `psu3Numerics_and_standingData_centralizerQuotient` の
最後の入力が埋まり、§2/§3 が商で走る**。

### 数学的な中身 (PSU(3,q) の標準モデルで)

`D̄` = トーラス (位数 `(q²−1)/d`)、`t̄` = Weyl 対合、`V̄ = C_{D̄}(t̄)` = ノルム 1 部分
(位数 `(q+1)/d`)、`Q̄₀ = Z(Q̄)`。トーラス元 `a` は `Q̄₀` を**ノルム `a^{1+q}` 倍**で
スケールするので、ノルム 1 の元は `Q̄₀` に自明に作用する = **(A)**。
(B) は model 側に既存: `ProjectiveUnitary.exists_ne_one_mem_psuTorus_torusWeight_eq_one`
(`TorusCentralizer.lean:76`、`1 < n` すなわち `ℓ = 2ⁿ ≥ 4` = 書籍の `ℓ > 2`) (56)。

⚠ 必要なのは **`hyp` 側の `D`/`V`/`Q₀` と標準モデルの辞書**。
`CentralizerPSUDistinguished.lean` は `|st| = 3` のためだけの transport (553 行) で、
`D`/`V`/`W` についての辞書は**持っていない** (実測: `hyp.D`/`hyp.V`/`hyp.W` の登場は
`hXV : X ≤ hyp.V` の 1 箇所のみ)。

### ⚠ 次セッションはここから

1. **PSU(3,ℓ) 辞書**: `L̄ ≃* standardPermGroup n` (枝データ) の下で
   `H̄ ⊓ L̄ = N_{L̄}(Q̄)` = Borel、`D̄ ⊓ L̄` = トーラス、を対応づける。
   材料: `normalizer_Q_eq_H` (`Basic.lean:610`)、`D_def : D = H ⊓ H^t`、
   `CentralizerPSUDistinguished.lean` の Sylow 共役 + 根群位置合わせの骨格。
2. (A) `V̄ ≤ C(Q̄₀)` — ノルム 1 のトーラス元が根群の中心に自明に作用すること。
3. (B) `V̄ ≠ 1` — `exists_ne_one_mem_psuTorus_torusWeight_eq_one` を辞書で移送。
4. → `psu3Numerics_and_standingData_centralizerQuotient` の最後の入力が埋まる
   → `exists_standardModel` for `qhyp` → (60) の段 (4) 鎖 → `corollaryTwo_of_stepFour`。
5. 商から `U` へ持ち上げ + `IsFGH.eq_of_le` ⟹ **段 (2) が閉じる**。段 (3)-(10) は
   landing 済 ⟹ **§4 完成**。

## 2026-08-01 (73): 🎯 §4 の `W ≠ 1` は**既存資産から出た** — Ch. III §1 Prop (p.117)

`CentralizerPSUData.false_of_W_eq_bot` (`StructureOfH/PSUCentre.lean:211`) は
Ch. III §1 Proposition (p.117) 「`F/Z(F)` は `PSU(3,ℓ)` に同型でない」の形式化で、
中身は「**Ch. I §3 Prop 1(c) の PSU(3,ℓ) 枝は `W = 1` と両立しない**」。

⟹ §4 段 (1) はまさにその枝なので `W_ne_bot_of_psu3_branch : hyp.W ≠ ⊥` が
枝データから 4 行で出た (landing 済)。

⚠ `PSU3SectionFourSetup.lean` に `StructureOfH.PSUCentre` の import を追加
(循環なし、jobs 4599 → 4602)。

### 段 (2) の残り (更新)

書籍 p.133 の `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` を repo に落とすと:

| 部分 | 状態 |
|---|---|
| ambient `W ≠ 1` | ✅ **今回** (`W_ne_bot_of_psu3_branch`) |
| `C_W(P) ≠ 1` | ⚠ 未 |
| 商で `ζ̄ = π ζ₁ ≠ 1` (= `ζ₁ ∉ N`) | ⚠ 未 |
| (A) `V̄ ≤ C(Q̄₀)` (= `hVW`) | ⚠ 未 |

⚠ `C_W(P) ≠ 1` は **coprime 作用の一般論では出ない** (奇位数 `W` に位数 `p` の `P` が
不動点自由に作用しうる)。`P ⊓ W = 1` (`SectionFourSetup` フィールド) も効かない。
⟹ 書籍どおり **PSU(3,ℓ) の構造**を使うしかない: `(V∩U)/(P∩U)` が `U/(P∩U) ≅ PSU(3,ℓ)`
の中でノルム 1 トーラス (位数 `(ℓ+1)/(ℓ+1,3) > 1`) に対応すること。

### 使えそうな model 側資産 (実測)

* `ProjectiveUnitary.exists_ne_one_odd_centralizing_involutions_of_sylowTwo (n) (1 < n)
   (S : Sylow 2 (standardPermGroup n))` (`TorusCentralizer.lean:200`)
  — **任意の** Sylow 2 に対し「`≠ 1`・奇位数・その全対合を中心化する `g`」を与える。
* `PSUCentre.lean` の `CentralizerPSUData.exists_mem_residual_commute_Q0` が
  **その transport の完全な手本** (Sylow.mapEquiv で標準モデルへ移し、`Z(F)` を
  跨ぐ commutator を `commute_of_commutatorElement_mem_of_coprime_natCard` で潰す)。

⟹ 次の単位は「この transport を `C_W(P) ≠ 1` / `V̄ ≤ C(Q̄₀)` の形で作り直す」こと。
`exists_mem_residual_commute_Q0` は既に「`x ∈ F` が `C_{Q₀}(X)` を中心化」を与えるので、
**`x` が `D` に入る (⟹ `x ∈ W`)** ことを言えれば `C_W(P) ≠ 1` に届く可能性が高い
(`false_of_W_eq_bot` の証明が `x ∈ C_G(s) ≤ H`、`x = q v` (`q ∈ Q`, `v ∈ V`) まで
やっているので、そこを `W = ⊥` 無しで走らせられるか実測する)。

### ⚠ 次セッションはここから

1. `false_of_W_eq_bot` の証明本体 (`PSUCentre.lean:211-` 以降) を読み、`W = ⊥` を
   使わない部分 (`x = q v` 分解まで) を切り出せるか実測する。
2. 切り出せれば `v ∈ V` が `C_{Q₀}(X)` を中心化 ⟹ `v ∈ W ⊓ C_G(X)` で
   **`C_W(P) ≠ 1` が出る**見込み。
3. (A) `V̄ ≤ C(Q̄₀)` — 同じ辞書で。
4. → `psu3Numerics_and_standingData_centralizerQuotient` の最後の入力
   → `exists_standardModel` for `qhyp` → 段 (4) 鎖 → `corollaryTwo_of_stepFour`。

## 2026-08-01 (74): 🎯 `C_W(P) ≠ 1` landing — 段 (2) の `ζ ∈ W#` が出た

`SectionFourSetup.exists_ne_one_mem_W_centralizer :
 ∃ w ∈ hyp.W, w ≠ 1 ∧ w ∈ Subgroup.centralizer (s4.P : Set G)`

⚠ **(56) の読みが正しかった**: 位数 `(ℓ+1)/(ℓ+1,3)` の計算は**一切要らない**。
PSU(3,ℓ) からの入力は Ch. III §1 の `exists_mem_residual_commute_Q0` 1 本だけ
(「`U/Z(U)` で非自明・奇位数、かつ `C_{Q₀}(P)` を中心化する `x ∈ U` が在る」)。

### 証明の骨 (5 段)

1. `x` は distinguished involution `s` を中心化 (`s ∈ C_{Q₀}(P)`) ⟹
   `x ∈ C_G(s) ≤ H` (`centralizer_le_H_of_mem_Q`) ⟹
   `x = q v` (`q ∈ Q`, `v ∈ V`; `exists_mem_Q_mem_V_of_mem_H_of_commute_distinguishedInvolution`)
2. **新補題 `mem_centralizer_of_qv_decomposition`** — `q`, `v` とも `P` を中心化。
   `C_H(s) = QV` は `Q ⊓ V ≤ Q ⊓ D = ⊥` により**一意分解**。`a ∈ X ≤ V` は
   `Q` を正規化 (`a ∈ H`) し、`V = C_D(t)` も正規化する (`a` は `t` を中心化)。
   ⟹ `x = q v` を `a` で共役すると第二の分解になり、一意性で `q^a = q`, `v^a = v`。
3. Galois の定理 `centralizer_V_centralizer_Q0` で `v ∈ P ⊔ W`
   (`v` が `C_{Q₀}(P)` を中心化することは `x` の性質 + `Q0_le_centralizer_Q` から)
4. **新補題 `D_le_normalizer_W`** (`W ⊴ D` = `KCyclic.lean:141` の instance から) +
   `Subgroup.coe_mul_of_left_le_normalizer_right` ⟹ `P ⊔ W = P·W` ⟹ `v = p ζ`
5. `ζ = p⁻¹ v ∈ C_G(P)` (`P` は可換ゆえ `P ≤ C_G(P)`、`v ∈ C_G(P)` は段 2)。
   `ζ = 1` なら `v ∈ P` が `U` の中心に入り `x` の像 = 2-元 `q` の像 ⟹
   非自明・奇位数と矛盾 (`false_of_W_eq_bot` 末尾と同じ parity 論法)。

### 段 (2) の残り (更新)

| 主張 | 状態 |
|---|---|
| ambient `W ≠ 1` | ✅ (73) |
| **`C_W(P) ≠ 1`** | ✅ **今回** |
| 商で `ζ̄ ≠ 1` (= `ζ ∉ N`) | ⚠ 未 |
| (A) `V̄ ≤ C(Q̄₀)` (= `hVW : qhyp.V = qhyp.W`) | ⚠ 未 |
| §2/§3 の standing data (商) | ✅ (71) |
| §3 の段 (4) 鎖 → `corollaryTwo_of_stepFour` | ⚠ 配線 |
| 商 → `U` 持ち上げ + `IsFGH.eq_of_le` | ⚠ 未 |

### ⚠ 次セッションはここから

1. **`ζ ∉ N`** — `N = (C_H(P)).normalCore` は `C_D(P)` に含まれる (`hNleD`) 奇位数核。
   `ζ ∈ C_W(P) ≤ C_D(P)` なので `ζ ∈ N` はありえなくはない ⟹ 要検討。
   ⚠ 代替: `qhyp.W` の元を直接作るのでなく、`ζ` の像が `qhyp.W` に落ちることを
   `W = D ⊓ C(Q₀)` (72) 経由で示し、非自明性は別途 (例えば `|W̄|` の下界) で取る。
2. **(A) `V̄ ≤ C(Q̄₀)`** — `V_eq_W_iff_le_centralizer_Q0` (72) で `hVW` に化ける。
   材料は段 2 と同じ「`V ∩ U` の元は `P × C_W(P)` に入る」= `inf_le_sup_centralizer_W`
   で、その `hcent`/`hfac` を今回の `mem_centralizer_of_qv_decomposition` +
   `D_le_normalizer_W` で作れる可能性が高い (要実測)。
3. → `psu3Numerics_and_standingData_centralizerQuotient` の最後の入力
   → `exists_standardModel` for `qhyp` → 段 (4) 鎖 → `corollaryTwo_of_stepFour`。

## 2026-08-01 (75): 🎯 §2/§3 が商の中で走る — 段 (2)(b) の前提が**全部**埋まった

`SectionFourSetup.standingData_centralizerQuotient` — §4 の ambient 仮説
(`M`, `hZ`, `hmu`, `hQsuz`, `hCop`, `hSolv`, `hP`, `hA3`, `hord`, `ih`) だけから、
商 `qhyp` について

* `n ≠ 0` / `|Q̄₀| = 2ⁿ` / `|Q̄| = |Q̄₀|³` / `|s̄t̄| = 3` / `Q̄` は Suzuki 2-群
* `Nonempty (qhyp.LemmaFiveSetup n)` / `Nonempty (qhyp.QuotientFieldModel n)`

を**商についての残余仮説なしで**供給する。

### 最後の隙間 `1 ≠ w ∈ W̄` の埋め方 (2 段)

1. `exists_ne_one_mem_W_centralizer` (74) — ambient で `C_W(P) ≠ 1`。
2. **`exists_ne_one_mem_quotient_W`** — その `ζ` が商で生き残る:
   * `ζ̄ ∈ W̄`: `W = D ⊓ C(Q₀)` (72) が**両側で**使え、`Q̄₀` は `C_{Q₀}(P)` の像 (71)。
   * `ζ̄ ≠ 1`: 核 `𝒩(C_G(P)) = C_D(P) ⊓ C(C_Q(P))`
     (`normalCore_cH_eq_centralizer_cQ`) は `C_Q(P)` を**丸ごと**中心化する。
     そこには段 (1) の `P`-固定な `ω ∈ Q − Q₀` が居るので、`ζ ∈ N` なら `ζ` が
     `Q/Q₀` の非自明元を固定する ⟹ 固定点自由性
     (`eq_one_of_conj_eq_mul_Q0_of_mem_W`) より `ζ = 1`、矛盾。

⟹ 段 (2)(b) は `exists_standardModel` for `qhyp` を**呼ぶだけ**になった。

## 2026-08-01 (76): 🔍 残る構造事実 (A) `V̄ = W̄` の正確な所在

`exists_standardModel` は `hVW` を**要求しない**が、`stepFive` /
`corollaryTwo_of_stepFour` は要求する (`D = KW` を `exists_mem_K_mem_W_mul hVW` で
使うため)。⟹ 段 (2) を閉じるには商について `hVW : qhyp.V = qhyp.W` が要る。

### `qhyp.V = π(V ⊓ C)` — coprime 作用で降りる (未実装だが道は明確)

`t` は `D` を正規化し (`D = H ⊓ H^t` ⟹ `D^t = D`)、`t ∈ C = C_G(P)` なので
`C_D(P)` も正規化する。核 `N ⊴ C` は `C_D(P)` に含まれ**奇位数**、`|⟨t⟩| = 2`。
⟹ coprime 作用の固定点定理 (Isaacs Cor 3.28 =
`OddOrder.GroupTheory.map_fixedSubgroup_eq_fixedSubgroup_quotient`,
`CoprimeFixedPoints.lean:61`、**本 leaf は既に import 済**) で
`C_{D̄}(t̄) = π(C_{C_D(P)}(t)) = π(V ⊓ C)`。

### ⚠ 残る本体は PSU(3,ℓ) の辞書 — 迂回できないことを確認した

`V_eq_W_iff_le_centralizer_Q0` (72) より `hVW` ⟺ `V̄ ≤ C(Q̄₀)` ⟺
(上の降下と Galois の定理より) **`V ⊓ U ≤ C(C_{Q₀}(P))`**、すなわち書籍の
「`(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`」そのもの。

⚠ **(74) の `C_W(P) ≠ 1` の論法は流用できない**。あれは PSU 計算が与える
**特定の** `x` から出発して `v` を作る向きで、逆向き (「`V ∩ U` の**全**元が
`C_{Q₀}(P)` を中心化する」) は言えない。体で見ると:
* `D/W ↪ ΓL₁(q) = F_q^× ⋊ Gal`、`P` は次数 `p` の Frobenius、`C_{Q₀}(P) = F_ℓ`
  (`q = ℓ^p`)。
* `C_{V̄}(P̄) = (V̄ ∩ F_ℓ^×) × P̄` なので、書籍の主張は
  **`V̄ ∩ F_ℓ^× = 1`** と同値。これは `V ∩ U` が `PSU(3,ℓ)` の**ノルム 1 トーラス**で
  あること (トーラス元は `Z(Q)` をノルム倍でスケールする) から出る。
⟹ ambient の一般論では出ず、**PSU(3,ℓ) の標準モデルへの transport が必須**。

### 次に要る model 側の事実 (2 本)

1. `standardPermGroup n` で「Weyl 対合 `t` を中心化するトーラス元は
   standard root subgroup の対合を中心化する」。
   ⚠ `TorusCentralizer.lean:151`
   `exists_ne_one_mem_psuTorus_scalePoint_eq_of_sq_eq_one` が**特定の 1 元**について
   同じことを言っているので、その証明中に汎用形
   (`torusWeight c = 1 → ∀ v, v² = 1 → psuTorusScaleHom n c v = v`) が在るはず。要実測。
2. `V ⊓ U` が (`residualQuotientEquiv` の下で) トーラスの `C(t̄)` に対応すること。
   手本 = `PSUCentre.lean` の `exists_mem_residual_commute_Q0`
   (Sylow.mapEquiv + `Z(F)` を跨ぐ commutator の coprime 潰し)。

### ⚠ 次セッションはここから

1. `TorusCentralizer.lean:151` 周辺を読み、汎用形の有無を実測する。
2. `V ⊓ U` → トーラスの辞書を作る (`PSUCentre.lean` を手本に)。
3. `hVW : qhyp.V = qhyp.W` を組む (上の降下 + Galois + (72))。
4. → `exists_standardModel` for `qhyp` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour`
   → 商から `U` へ持ち上げ + `IsFGH.eq_of_le` ⟹ **段 (2) が閉じる**。

## 2026-08-01 (77): (A) の model 側の中身を一般化 — `scalePoint_eq_of_torusWeight_eq_one`

`exists_ne_one_mem_psuTorus_scalePoint_eq_of_sq_eq_one` の証明本体は「特定の `c`」に
依存せず `torusWeight c = 1` だけを使っていた ⟹ 全ノルム 1 パラメータの一般形
`scalePoint_eq_of_torusWeight_eq_one` に切り出し、既存定理はその系にした
(`TorusCentralizer.lean`、フルビルド green・lint 純ゼロ)。

これが (A)「`(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`」の model 側の中身
(トーラスは `Z(Q)` = `Ω₁(S₀)` にノルム倍で作用するので、ノルム 1 なら自明作用)。

### (A) の残り = 群側の辞書 2 本

| # | 主張 | 手本 |
|---|---|---|
| (A1) | `V ⊓ U` の像が `standardPermGroup n` のトーラスに入る | `PSUCentre.lean` の `exists_mem_residual_commute_Q0` (Sylow.mapEquiv + `Z(F)` 跨ぎ commutator の coprime 潰し) |
| (A2) | `t` を中心化するトーラス元は `torusWeight = 1` | model 側 (`GeneratedAction` / `Bruhat`) を実測 |

これが入れば `scalePoint_eq_of_torusWeight_eq_one` で `V ⊓ U ≤ C(C_{Q₀}(P))`、
Galois で `V ⊓ U ≤ P ⊔ W`、coprime 降下 (76) で `V̄ ≤ W̄`、`W_le_V` で `hVW` が出る。

### ⚠ 次セッションはここから

1. (A2) の実測 — `standardPermGroup n` の Weyl 対合 `t` とトーラスの交換関係
   (`Bruhat.lean` / `StandardGenerators.lean` に `t c t⁻¹ = c^{-q}` 型の式が在るはず)。
   `c` が `t` と交換 ⟺ `c^{1+q} = 1` ⟺ `torusWeight c = 1` が狙い。
2. (A1) の辞書を `PSUCentre.lean` を手本に作る。
3. → `hVW` → `exists_standardModel` for `qhyp` → §3 段 (4) 鎖 →
   `corollaryTwo_of_stepFour` → 商から `U` へ持ち上げ ⟹ **段 (2) が閉じる**。

## 2026-08-01 (78): 🎯 (A2) landing — 段 (2) の構造事実の **model 側は完成**

`TorusCentralizer.lean` に 2 本 (フルビルド green・lint 純ゼロ):

| 定理 | 内容 |
|---|---|
| `torusWeight_eq_one_of_commute_weylElement` | Weyl 共役は `c ↦ (c*)⁻¹` なので、固定 ⟺ `c c* = 1` ⟺ `torusWeight c = 1` |
| `commute_rootHom_of_commute_weylElement` | ⟹ そのような**全ての**トーラス元が standard root group の対合を中心化 |

⚠ 既存 `exists_ne_one_odd_centralizing_involutions_standardRoot` は「1 つ在る」型で、
段 (2) が要るのは「全部そう」型。後者が今回。

⚠ lint: `show` は `linter.style.show` に引っかかる (`have` + `exact` に直した)。

### 🔍 残る (A1) の正確な形 — Borel から torus へ

段 (2) が要るのは `V ⊓ U` の元についてなので、model 側で torus まで降りる必要がある。
`V ≤ D ≤ H = N_G(Q)` (`normalizer_Q_eq_H`) なので **`V ⊓ U` の像は
`N(standardRootSubgroup) = standardBorel` に入る**。⟹ 要る model 補題は

> `b ∈ standardBorel n` かつ `Commute (weylElement n) b` ⟹
> `b` は `standardRootSubgroup n` の対合を中心化する

**証明の道 (実測済の材料で書ける)**:
* `standardBorel_eq_infinityStabilizer` (`Bruhat.lean:317`) — `b` は `∞` を固定。
* `weyl` は `∞` と `origin` を入れ替える (`weylElement_smul_*`, `Unital.weylPerm_infinity`
  / `weylPerm_origin`) ので、`b` が `weyl` と交換 ⟹ `b` は `origin` も固定。
* `mem_standardBorel_iff_existsUnique_root_torus` (`Borel.lean:105`) で
  `b = rootHom u * psuTorusHom c` (一意)。`psuTorusHom c` は `origin` を固定するので
  `b • origin = origin` から `u = 1` ⟹ `b = psuTorusHom c`。
* あとは今回の `commute_rootHom_of_commute_weylElement`。

### (A1) の群側 (`PSUCentre.lean` が手本)

`v ∈ V ⊓ U`, `y ∈ C_{Q₀}(P)` に対し `Commute v y` を出す:
1. `U/Z(U) ≃* standardPermGroup n` (`details.residualQuotientEquiv`) で像を取る。
2. `v` の像は Borel に入り (`v ∈ H = N_G(Q)`)、`t` の像 (= Weyl) と交換する
   (`v ∈ V = C_D(t)`)。⟹ 上の model 補題で `v` の像は `y` の像と交換。
3. `Z(U)` は奇位数 (`odd_natCard_center_residual`)、`y` は対合 ⟹
   `commute_of_commutatorElement_mem_of_coprime_natCard` で `U` 内の交換に持ち上げ。
   (= `exists_mem_residual_commute_Q0` の最後の 10 行と同じ形)

⟹ これで `hcent` が出て、Galois (`centralizer_V_centralizer_Q0`) で `V ⊓ U ≤ P ⊔ W`、
coprime 降下 (76) で `V̄ ≤ W̄`、`W_le_V` で **`hVW : qhyp.V = qhyp.W`**。

### ⚠ 次セッションはここから

1. 上の model 補題 (`standardBorel` ∩ `C(weyl)` ⊆ torus) を `Borel.lean` か
   `TorusCentralizer.lean` に書く。
2. (A1) の群側を `PSUCentre.lean` を手本に組む。
3. `hVW` → `exists_standardModel` for `qhyp` → §3 段 (4) 鎖 →
   `corollaryTwo_of_stepFour` → 商から `U` へ持ち上げ ⟹ **段 (2) が閉じる**。

## 2026-08-01 (79): 🎯 段 (2) の構造事実 (A) の **model 側が完成**

`TorusCentralizer.lean` (フルビルド green・lint 純ゼロ):

| 定理 | 内容 |
|---|---|
| `exists_psuTorusHom_eq_of_mem_standardBorel_of_commute_weylElement` | Borel 元は `∞` を固定、Weyl は `∞`↔`origin` を入れ替えるので Weyl と交換する Borel 元は `origin` も固定 ⟹ `borelHom_smul_origin` で根座標が自明 ⟹ トーラス元 |
| `commute_rootHom_of_mem_standardBorel_of_commute_weylElement` | 上記 + (A2) ⟹ standard root group の対合を中心化 |

⟹ 書籍 p.133「by the structure of `PSU(3,ℓ)`」の**中身は全部形式化済**。

### ⚠ 群側 (A1) の残り = 「標準位置」問題

群側で要るのは、`v ∈ V ⊓ U` の像について
* **像が Borel に入る** — `V ≤ D ≤ H = N_G(Q)` (`normalizer_Q_eq_H`) から、像は
  `C_Q(P)` の像 (= `F/Z(F)` の Sylow 2) の正規化群に入る。
* **像が `t` の像と交換する** — `V = C_D(t)`。

しかし model 補題は **standard** root subgroup と **standard** Weyl element について
述べている。`PSUCentre.lean` の `exists_mem_residual_commute_Q0` が
`exists_ne_one_odd_centralizing_involutions_of_sylowTwo` (= **任意の** Sylow 2 版) を
使えたのは、その model 補題が最初から任意 Sylow 用に書かれていたから。

⟹ 今回は **`(S, τ)` の対を標準位置に合わせる**必要がある。これは
`CentralizerPSUDistinguished.lean` (553 行) が `|st| = 3` のためにやっている
「Sylow 共役 + 根/行列式 1 トーラス補正で `Q` と `t` を同時に標準位置へ」と同じ手順。
⚠ その補助定理は `private` なので、再利用するには一般化して公開する必要がある。

### 選択肢 (次セッションで判断)

1. **model 補題の任意-Sylow 版を作る** — `exists_ne_one_odd_centralizing_involutions_of_sylowTwo`
   と同じ流儀で `(S, τ)` を引数に取る形。`τ` が standard Weyl の共役であることを
   仮説に入れれば機械的な共役移送で済む。
2. **`CentralizerPSUDistinguished.lean` の標準位置補題を public 化して再利用** —
   `orderOf_distinguishedInvolution_mul_t_of_psu3Target` の証明中で
   `e0 : L ≃* standardPermGroup n` を作り `Q`/`t` を同時に標準位置へ送っている
   (行 161-230 あたり)。ここを `∃ e0, e0 '' Q = standardRootSubgroup ∧ e0 t = weylElement`
   の形で切り出せれば (A1) は数行になる。**こちらが本命**。

### ⚠ 次セッションはここから

1. `CentralizerPSUDistinguished.lean` の `orderOf_distinguishedInvolution_mul_t_of_psu3Target`
   の証明 (161-350) を読み、標準位置同型の切り出しが可能か実測する。
2. 切り出せたら (A1) → `hcent` → Galois → coprime 降下 → `hVW`。
3. → `exists_standardModel` for `qhyp` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour`
   → 商から `U` へ持ち上げ ⟹ **段 (2) が閉じる**。

## 2026-08-01 (80): 🎯 (A) の model 側を**任意の入替対合**へ一般化 — 標準位置問題が消えた

(79) で「群側は `(S, τ)` を標準位置へ合わせる必要がある (= `CentralizerPSUDistinguished.lean`
の 350 行を切り出す)」と書いたが、**model 補題を一般化する方が正しかった**。

`commute_rootHom_of_mem_standardBorel_of_commute_swap (hn : 0 < n)
 (htinf : tau • ∞ = origin) (htorig : tau • origin = ∞)
 (hb : b ∈ standardBorel n) (hc : Commute tau b) (hu : u ^ 2 = 1) :
 Commute b (rootHom n u)`

⚠ **一般化が必須だった理由**: `orderOf_distinguishedInvolution_mul_t_of_psu3Target` の
証明 (225-330) を実測すると、`Q` を標準根部分群に合わせても `t` の像は
**`T₀ · w` (トーラス因子付き)** にしかならない (`z1 = psuTorusHom c₀ * weylElement`)。
その因子は無害: `tau · w` は `∞`/`origin` を両方固定するので自分もトーラス元、
トーラスは可換なので共役作用は結局 `psuWeylParameterHom` を通り `torusWeight c = 1`。

* `exists_psuTorusHom_eq_of_fixes_infinity_origin` — 2 点を固定 ⟹ トーラス元。
* 群側に渡す仮説は **`τ • ∞ = origin` と `τ • origin = ∞` だけ**。
  `orderOf_distinguishedInvolution_mul_t_of_psu3Target` の証明中の `hz1inf`/`hz1origin`
  がまさにこの形なので、そこを切り出せば足りる (350 行の全体は不要)。

⟹ **model 側は完全に閉じた**。残りは群側の transport のみ。

### ⚠ 次セッションはここから

1. `CentralizerPSUDistinguished.lean` の `hz1inf` / `hz1origin` (行 289-303) に相当する
   「`e0`, 根共役 `a`, `z1 = a·e0(t)·a⁻¹` が 2 点を入れ替える」データを public 補題に
   切り出す (`∃ e0 a, (Q の像の a-共役) = standardRootSubgroup ∧ z1 • ∞ = origin ∧
   z1 • origin = ∞` の形)。⚠ 全体でなく**この 3 点だけ**でよい。
2. (A1) 群側: `v ∈ V ⊓ U` の像が Borel に入る (`V ≤ D ≤ H = N_G(Q)`) + `v` が `t` の像と
   交換する ⟹ 上の model 補題 ⟹ `Z(U)` 奇位数で持ち上げ
   (`commute_of_commutatorElement_mem_of_coprime_natCard`、手本 = `exists_mem_residual_commute_Q0`)。
3. `hcent` → Galois → coprime 降下 (76) → **`hVW : qhyp.V = qhyp.W`**。
4. → `exists_standardModel` for `qhyp` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour`
   → 商から `U` へ持ち上げ ⟹ **段 (2) が閉じる**。

## 2026-08-01 (81): 標準位置同型を切り出した + ⚠ `hVW` の前提そのものに疑義

### landing: `exists_standardPosition_of_psu3Target`

`orderOf_distinguishedInvolution_mul_t_of_psu3Target` の証明本体から切り出して公開:

```
∃ (e : L ≃* standardPermGroup data.n) (tL : L), (tL : G) = hyp.t ∧
  (∀ x : L, e x ∈ standardRootSubgroup data.n ↔ (x : G) ∈ hyp.Q) ∧
  e tL = weylElement data.n
```

⚠ **(80) の記述を訂正**: 既存証明は入替補正 (`hz1inf`/`hz1origin`) の**先**まで進み、
行列式 1 トーラス補正 (`hnormalize`) で `t` の像を**標準 Weyl 元ちょうど**に正規化して
いた。⟹ 切り出しは (79)/(80) の想定より素直で、`_swap` 版の一般化は無くてもよかった
(ただし一般化自体は正しく、より弱い仮説なので保持)。

元の定理は `obtain` + 残り (braid → `eq_distinguishedPair_of_structure` → 位数 3) に
なった。フルビルド green (4986 jobs)・lint 純ゼロ。

### ⚠⚠ 重大: `hVW : qhyp.V = qhyp.W` は**そもそも真でない可能性が高い**

(A1) を組もうとして判明した:

* `exists_standardPosition_of_psu3Target` を `qhyp` に当てると `e` は
  `L̄ = tri.result.L`(= `O^{2'}(Ḡ)`) 上の同型。**`v̄ ∈ qhyp.V` が `L̄` に入る保証がない**。
  `L̄` は奇指数の正規部分群で、`V̄` は奇位数 — 奇位数元が奇指数部分群に入る理由はない。
* **書籍もそう主張していない**。p.133 の主張は `(V ∩ U)/(P ∩ U)` についてであって
  `V` 全体ではない。§3 Corollary 2 は書籍では `V = W` を仮説にしていない
  (それは Corollary **1** の追加仮説)。
* ⟹ repo の `corollaryTwo_of_stepFour` が担ぐ `hVW` は**特殊化債務の疑い**
  ([[repo-stronger-hypothesis-is-specialization-not-gap]] の典型パターン)。

### 次に決めるべき設計分岐 (2 案)

| 案 | 内容 | コスト |
|---|---|---|
| (a) | `hVW` の消費点を trace し、実際に要るもの (`D = KW` か、`V ⊓ L = W ⊓ L` 等) まで弱める | `exists_mem_Q0_orbitOfF_eq` / `corollaryTwo` / `stepFive` の `hVW` 使用箇所を全部追う |
| (b) | §3 の適用先を `C_G(P)/N` でなく **`U/(P ∩ U)`** に変える (書籍どおり) | 段 (1) の `Z(U) ⊆ P` があるので `P ∩ U ⊇ Z(U)`。`U/(P∩U)` 上の `Hypothesis` 構成が要る |

⚠ (58) は「§3 Cor 2 が完全な `Hypothesis` を要求するので商経路」と裁定したが、
その商を `C_G(P)/N` と取ったのは repo の既存構成に合わせただけで、書籍の `U/(P∩U)` とは
違う。**`hVW` が真になるのは後者**の可能性が高い (`V ∩ U ⊆ P × C_W(P)` を `P ∩ U` で
割ると `V̄ ≤ W̄` になる)。

### ⚠ 次セッションはここから

1. **まず (a) の trace**: `hVW` が `stepFive` / `corollaryTwo` /
   `exists_mem_Q0_orbitOfF_eq` の証明中で実際に何に使われているかを実測する
   (`exists_mem_K_mem_W_mul` = `D = KW` 以外に使われているか)。
2. `D = KW` だけなら、商 `qhyp` について `D̄ = K̄W̄` を直接示せるか検討 (`hVW` を回避)。
3. 弱められないなら (b) を検討 — `U/(P ∩ U)` 上の `Hypothesis` 構成。
   ⚠ これは設計分岐なので、判断根拠を issue に残すこと。
4. 決着後: → `exists_standardModel` for 商 → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour`。

## 2026-08-01 (82): 🔍 `hVW` の全数 trace — **弱められない** (案 (a) は死んだ)

`hVW : hyp.V = hyp.W` の**原始的な**使用箇所 (単なる threading を除く) を全数調査:

| 箇所 | 使い方 |
|---|---|
| `PSU3OrbitCount.lean:870` (`eq_one_of_conj_eq_mul_Q0_of_mem_D`) | `exists_mem_K_mem_W_mul hVW` = **`D = KW`** |
| `PSU3StepTwenty.lean:247`, `PSU3StepEighteen.lean:84` | 同上 (`D = KW`) |
| `PSU3OrbitCount.lean:466,468,525` | `rwa [hVW]` — `\|V\|` を `\|W\|` に書き換える (ファイバー評価) |
| `PSU3OrbitCount.lean:603` | `index_K_subgroupOf_D` (`\|D:K\| = \|V\|`) の後に `hVW` で `\|W\|` へ |

⟹ **すべて「`D = KW`」か「`\|V\| = \|W\|`」に帰着する**。

### ⚠ しかし両者は `V = W` と**同値**

* `index_K_subgroupOf_D : (K.subgroupOf D).index = Nat.card V` (`hVW` 不要、
  `card_D_eq_card_V_mul_card_K` から)。
* `W ≤ V` (`W_le_V`) は無条件。
* ⟹ `D = KW` ⟹ `\|D\| ≤ \|K\|·\|W\|` ⟹ `\|V\| ≤ \|W\|` ⟹ (`W ≤ V` と併せて) `V = W`。

⟹ **`hVW` を `D = KW` に弱めても何も得しない** (論理的に同値)。
**案 (a) は死んだ** — §3 endpoint の `hVW` は特殊化債務ではなく、本質的な仮説。

### ⟹ 残るのは案 (b): §3 の適用先を書籍どおり `U/(P ∩ U)` にする

書籍 p.133 は `f₁`, `h₁` を「`U`, `U ∩ H`, `t` に関して」取る、と明示している。
repo が `C_G(P)/N` を選んだのは (57)(58) で既存構成 `centralizerQuotientHypothesis` に
合わせたためで、書籍の商とは**別物**。

* `V ∩ U ⊆ P × C_W(P)` を `P ∩ U` で割ると `V̄ ≤ W̄`、すなわち **`U/(P∩U)` では
  `hVW` が成り立つ**見込み。
* 一方 `C_G(P)/N` では `qhyp.V = π(V ⊓ C_G(P))` (coprime 降下、(76)) であって
  `V ∩ U` より大きく、`hVW` が真である保証がない ((81))。

### ⚠ 次セッションはここから (設計分岐の決着)

1. **`U/(P ∩ U)` 上の `Hypothesis` 構成が可能かを実測する**。
   材料: 段 (1) の `Z(U) ⊆ P` (`SectionFourSetup.eq_P_of_centralizes`)、
   `t ∈ U` (`t_mem_primeComplementResidual`)、`U ≤ C_G(P)`。
   ⚠ `centralizerQuotientHypothesis` は `C_G(X)/normalCore(C_H(X))` 専用なので、
   `U` 版は新規構成 (A1)-(A3) が要る可能性が高い。手本 = `CentralizerInduction.lean` の
   `centralizerHypothesisA1` + `CentralizerQuotient.lean` の `quotientOfKernel`。
2. あるいは **`N ≤ P ∩ U` かつ両商が一致するか**を実測する
   (`N = C_D(P) ⊓ C(C_Q(P))`、`Z(U) ⊆ P`)。一致すれば (81) の懸念自体が消える。
   ⚠ **こちらを先に確認する** — 安ければ既存資産が全部そのまま使える。
3. 決着後: `hVW` → `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour`。

## 2026-08-01 (83): 🧭 hub 裁定 — §3 の適用先は **標準モデル `standardPermGroup n`**

### 実測 1: `P ∩ U = Z(U)` (landing)

`mem_center_primeComplementResidual_of_mem_P` — `U ≤ C_G(P)` なので `U` の元は `P` を
中心化し、`P ∩ U ≤ Z(U)`。逆は段 (1) の `Z(U) ⊆ P`。
⟹ **書籍の `U/(P ∩ U)` は `U/Z(U)` そのもの**で、repo は
`CentralizerPSUData.residualQuotientEquiv : (U ⧸ Z(U)) ≃* standardPermGroup n` を
既に持っている。(82) の案 (b) が指す商は新規構成でなく**既存**だった。

### 実測 2: `C_G(P)/N` 経路では `hVW` が出ない (再確認)

`qhyp.V = π(V ⊓ C_G(P))` (coprime 降下、(76)) なので `hVW` は
**`C_V(P) ≤ P ⊔ W`** と同値 (Galois 経由)。書籍が主張するのは `V ∩ U ⊆ P × C_W(P)`
だけで、`U = O^{2'}(C_G(P))` は `C_G(P)` に**奇指数で真に含まれうる**。
⟹ `C/N` 経路では一般に `hVW` は取れない。

### 🧭 裁定: §3 は `standardPermGroup n` 上の `Hypothesis` に当てる

**理由**:
1. `residualQuotientEquiv` で `U/Z(U) ≃* standardPermGroup n` が既にある
   (新規の商構成が不要)。
2. `standardPermGroup n` は `Unital n` に**忠実 2 重推移**に作用する
   (`standardPermGroup_isMultiplyPretransitive`、`Equiv.Perm` の部分群なので忠実) ⟹
   (A1)-(A2) が既存資産で埋まる。
3. **`hVW` が標準モデルでは定理になる**: `D` = トーラス、`V = C_D(weyl)` = ノルム 1 部分、
   `W = D ⊓ C(Q₀)`。今セッションの
   `commute_rootHom_of_commute_weylElement` (ノルム 1 トーラス元は根群の対合を中心化)
   がそのまま `V ≤ W` を与え、`W_le_V` と併せて `V = W`。
   ⟹ (82) で「弱められない」と確定した `hVW` が、正しい対象では**自然に成り立つ**。
4. 書籍自身が Ch. III §3 で「`Q ⋊ KW` を `S₁ ⋊ K₁W₁` と同一視する」と書いており、
   標準モデルで議論するのが原文の流儀。

⚠ **未確認**: `Hypothesis (standardPermGroup n) (Unital n)` は repo に**まだ無い**
(grep 済)。これが次の作業単位。

### ⚠ 次セッションはここから

1. **`Hypothesis (standardPermGroup n) (Unital n)` を構成する**。
   フィールドの見当:
   * `basept := Unital.infinity n`、`doubly_transitive := standardPermGroup_isMultiplyPretransitive`
   * `H := standardBorel n` (= `stabilizer ∞`、`standardBorel_eq_infinityStabilizer`)
   * `Q := standardRootSubgroup n`、`D := torus` (`psuTorusHom` の range)
   * `t := weylElement n` (`weylElement_sq_eq_one`、`t ∉ H` は `weylElement • ∞ = origin ≠ ∞`)
   * `Q_inf_D_eq_bot` / `Q_mul_D_eq_H` = `mem_standardBorel_iff_existsUnique_root_torus`
   * `D_odd` = `orderOf_psuTorus_odd` 系、`Q_even` = `natCard_standardRootSubgroup`
   * (A3) `two_rank_ge_two` = 根群の中心 `Ω₁(S₀)` は位数 `2ⁿ ≥ 4` の elementary abelian
2. その上で `V = W` を `commute_rootHom_of_commute_weylElement` から証明する。
3. `residualQuotientEquiv` で `U/Z(U)` へ transport し、§3 の endpoint を当てる。
4. → 段 (2) → 段 (3)-(10) は landing 済 ⟹ **§4 完成**。

## 2026-08-01 (84): 標準モデル `Hypothesis` の材料 — `D_def` landing

`standardBorel_inf_conj_weylElement (hn : 0 < n) :
 standardBorel n ⊓ (standardBorel n).map (MulAut.conj (weylElement n)).toMonoidHom
   = (psuTorusHom n).range`

`B` = `∞` の固定化群、`B^w` = `origin` の固定化群 ⟹ 交わり = 2 点固定化群 = トーラス。
(フルビルド green・lint 純ゼロ)

### `Hypothesis (standardPermGroup n) (Unital n)` フィールド別の材料表

| フィールド | 材料 | 状態 |
|---|---|---|
| `basept` | `Unital.infinity n` | ✅ |
| `doubly_transitive` | `standardPermGroup_isMultiplyPretransitive` | ✅ |
| `faithful` | `Equiv.Perm` の部分群 ⟹ 自明 | ⚠ 要確認 |
| `H` / `H_def` | `standardBorel n` + `standardBorel_eq_infinityStabilizer` | ✅ |
| `Q` | `standardRootSubgroup n` | ✅ |
| `D` | `(psuTorusHom n).range` | ✅ |
| `t` / `t_sq` | `weylElement n` / `weylElement_sq_eq_one` | ✅ |
| `t_ne_one` | `weylElement • ∞ = origin ≠ ∞` | ⚠ 易 |
| `t_not_mem_H` | 同上 (`∞` を固定しない) | ⚠ 易 |
| **`D_def`** | **`standardBorel_inf_conj_weylElement`** | ✅ **今回** |
| `Q_le_H` | `rootHom_mem_standardBorel` | ✅ |
| `Q_normal_in_H` | Borel = 根群 ⋊ トーラス; `psuTorusHom_mul_rootHom_mul_inv` + 根群自身 | ⚠ 易 |
| `Q_inf_D_eq_bot` / `Q_mul_D_eq_H` | `mem_standardBorel_iff_existsUnique_root_torus` | ⚠ 中 |
| `Q_even` | `natCard_standardRootSubgroup` (`= (2ⁿ)³`) | ⚠ 易 |
| `D_odd` | `orderOf_psuTorus_odd` 系 / `natCard_standardBorel` から | ⚠ 中 |
| `two_rank_ge_two` | `Ω₁(S₀)` (= 根群の中心、位数 `2ⁿ`) の部分群で位数 4 (`n ≥ 2`) | ⚠ 中 |
| `[Finite (standardPermGroup n)]` | `Unital n` 有限 ⟹ `Equiv.Perm` 有限 | ⚠ 要確認 |

⟹ **残りは全部「既存 API を組む」型**。新しい数学は無い。

### ⚠ 次セッションはここから

1. 上表の ⚠ を順に埋め、`standardHypothesis (n : ℕ) (hn : 1 < n) :
   Hypothesis (standardPermGroup n) (Unital n)` を新 leaf
   (`OddOrder/Peterfalvi/Appendices/Suzuki/StandardModelHypothesis.lean`) に構成する。
   ⚠ 新 leaf は同じ commit で `OddOrder.lean` に配線すること。
2. `V = W` を証明: `V = C_D(t)` はノルム 1 トーラス
   (`torusWeight_eq_one_of_commute_weylElement`)、`W = D ⊓ C(Q₀)` (72) で
   `commute_rootHom_of_commute_weylElement` が `V ≤ W` を与える。`W_le_V` で等号。
3. `residualQuotientEquiv` で `U/Z(U)` へ transport → §3 endpoint → 段 (2)。

## 2026-08-01 (85): 標準モデル `Hypothesis` — Borel 分解由来の 2 フィールド landing

* `standardRootSubgroup_inf_psuTorusRange` — **`Q ∩ D = 1`**
  (`mem_standardBorel_iff_existsUnique_root_torus` の一意性から)。
* `standardRootSubgroup_mul_psuTorusRange` — **`Q · D = H`**。

⚠ 配置: `Borel.lean` からは `standardRootSubgroup` (`RootGroupSuzukiType.lean` 定義) が
見えないので、両方を import する `TorusCentralizer.lean` に置いた。
⚠ `ExistsUnique` の一意性部分は `∀ y, p y → y = p` の向き (`p = y` ではない)。

### `Hypothesis (standardPermGroup n) (Unital n)` 残りフィールド

| フィールド | 材料 | 状態 |
|---|---|---|
| `D_def` | `standardBorel_inf_conj_weylElement` | ✅ (84) |
| `Q_inf_D_eq_bot` / `Q_mul_D_eq_H` | **今回** | ✅ |
| `basept`/`doubly_transitive`/`H`/`H_def`/`Q`/`D`/`t`/`t_sq`/`Q_le_H` | 既存 API 直結 | ✅ |
| `t_ne_one` / `t_not_mem_H` | `weylElement • ∞ = origin ≠ ∞` | ⚠ 易 |
| `Q_normal_in_H` | Borel = 根群 ⋊ トーラス (`psuTorusHom_mul_rootHom_mul_inv`) | ⚠ 易 |
| `Q_even` | `natCard_standardRootSubgroup` (`2^(3n)`) | ⚠ 易 |
| `D_odd` | `natCard_psuTorus_standard` / `odd_orderOf_psuTorusParameter` | ⚠ 中 |
| `two_rank_ge_two` | `Ω₁(S₀)` = 根群の中心 (位数 `2ⁿ`, exponent 2) の位数 4 部分群 | ⚠ 中 |
| `faithful` / `[Finite]` | `Equiv.Perm (Unital n)` の部分群、`Unital n` 有限 | ⚠ 要確認 |

⚠ `two_rank_ge_two` の注意: 位数 4 の部分群を `Sylow.exists_subgroup_card_pow_prime` で
**群全体から**取ると巡回群かもしれず `∀ x, x² = 1` が出ない。
**`Ω₁(S₀)` (elementary abelian, 位数 `2ⁿ`, `n ≥ 2`) の中で**取ること。

### ⚠ 次セッションはここから

1. 上表の ⚠ を埋めて `standardHypothesis` を新 leaf
   `OddOrder/Peterfalvi/Appendices/Suzuki/StandardModelHypothesis.lean` に構成
   (⚠ 同じ commit で `OddOrder.lean` に配線)。
2. `V = W` を証明 (`torusWeight_eq_one_of_commute_weylElement` +
   `commute_rootHom_of_commute_weylElement` + `W_eq_inf_centralizer_Q0` + `W_le_V`)。
3. `residualQuotientEquiv` で `U/Z(U)` へ transport → §3 endpoint → 段 (2)。

## 2026-08-01 (86): 🎯 標準モデル `Hypothesis` 完成 + `hVW` が**定理**になった

新 leaf `OddOrder/Peterfalvi/Appendices/Suzuki/StandardModelHypothesis.lean`
(`OddOrder.lean` に同 commit で配線済、フルビルド green 4987 jobs・lint 純ゼロ)。

`standardHypothesis (n : ℕ) (hn : 1 < n) : Hypothesis (standardPermGroup n) (Unital n)`

| フィールド | 実装 |
|---|---|
| `basept` / `doubly_transitive` | `Unital.infinity n` / `standardPermGroup_isMultiplyPretransitive` |
| `faithful` | `Equiv.Perm` の部分群 (`Subtype.ext ∘ Equiv.ext`) |
| `H` / `H_def` | `standardBorel n` / `standardBorel_eq_infinityStabilizer` |
| `Q` / `D` / `t` | `standardRootSubgroup n` / `(psuTorusHom n).range` / `weylElement n` |
| `t_ne_one` / `t_not_mem_H` | `weylElement_smul_infinity_ne` (新) |
| `D_def` | `standardBorel_inf_conj_weylElement` (84) |
| `Q_normal_in_H` | `conj_mem_standardRootSubgroup_of_mem_standardBorel` (新) |
| `Q_inf_D_eq_bot` / `Q_mul_D_eq_H` | (85) |
| `Q_even` / `D_odd` | `natCard_standardRootSubgroup` / `odd_natCard_psuTorusRange` (新) |
| `two_rank_ge_two` | `exists_subgroup_card_four` (新) |

⚠ `two_rank_ge_two` の実装メモ: 位数 4 部分群は **`Ω₁(S₀)` (根群の中心線
`RootGroup.centerLine`、位数 `2ⁿ`、exponent 2) の中で** `Sylow.exists_subgroup_card_pow_prime`
で取る。群全体から取ると巡回群になりうる ((85) の警告どおり)。
`|centerLine| = 2ⁿ` は `centerLineEquivFixed` + `natCard_fixedByConjugation`。

### 🎯 `standardHypothesis_V_eq_W` — 想定より遥かに安かった

(83) では「ノルム 1 トーラスが根群の対合を中心化する」
(`commute_rootHom_of_commute_weylElement`) 経路を想定していたが、実際は

> `W = C_V(K)`、`K ⊆ D`、そして **`D` (行列式 1 トーラス) は可換** ⟹
> `V ≤ D` は `K` を自動的に中心化する

で **3 行**。⟹ (82) で「弱められない」と確定した `hVW` が、正しい対象では自明に成立。
(83) の hub 裁定が正しかったことが実証された。

### ⚠ 次セッションはここから

1. **§3 の endpoint を `standardHypothesis` に当てる**。
   `corollaryTwo_of_stepFour` の残り前提 (`sfive`, `M`, `Φ`, `Ψ`, `hcover` …) を
   `standardHypothesis n hn` について供給する。⚠ `psu3Numerics_and_standingData_*` と
   同じ流儀で、まず `hst` (`|s̄t̄| = 3`) / `hQsuz` / `hm` / `hQ0card` / `hcardQ` /
   `ih` を標準モデルについて出す (標準モデルなので**直接計算**できるはず:
   `|Q₀| = |Ω₁(S₀)| = 2ⁿ`、`|Q| = 2^{3n} = |Q₀|³`)。
   ⚠ `ih : TheoremAInductionBelow (standardPermGroup n) (Unital n)` の供給が要注意 —
   標準モデルは「より小さい群すべて」の量化を要求する。実測すること。
2. `residualQuotientEquiv` で `U/Z(U)` へ transport し、段 (2) の `ω`, `ζ`, `η` を
   ambient へ持ち上げる (`IsFGH.eq_of_le`)。
3. 段 (3)-(10) は landing 済 ⟹ **§4 完成**。

## 2026-08-01 (87): 標準モデルの `hQ0card` / `hcardQ` + ⚠ `ih` は導出不能と実測

(フルビルド green 4987 jobs・lint 純ゼロ)

| 定理 | 内容 |
|---|---|
| `standardHypothesis_Q0` | `Q₀ = (RootGroup.centerLine n).map (rootHom n)` (= `Ω₁(S₀)`) |
| `natCard_standardHypothesis_Q0` | `\|Q₀\| = 2ⁿ` |
| `natCard_standardHypothesis_Q` | `\|Q\| = \|Q₀\|³` |

`Q₀` の同定: Borel 元を半直積分解 `r · c` で書くと `x² = 1` ⟹ `c² = 1`、
トーラスは奇位数なので `c = 1` ⟹ 残るのは根群の対合 = 中心線。
⚠ 実装は `SemidirectProduct.rightHom` で右成分を取り、`SemidirectProduct.ext rfl hright`
で `y = inl y.left` を出すのが素直 (`mk_eq_inl_mul_inr` は形が違って使えない)。
⚠ import は `Basic` → `QStructure` に差し替え (`Q0` は `QStructure.lean` 定義)。

### 🔍 `exists_standardModel` の残り前提の所在 (実測)

| 前提 | 標準モデルでの出どころ |
|---|---|
| `hQ0card` / `hcardQ` | ✅ **今回** |
| `hm : m ≠ 0` | `hn : 1 < n` から (`m := n`) |
| `hQsuz` | ✅ `standardRootSubgroup_isSuzuki2Group` — `Q` は defeq なので**新規作業ゼロ** |
| `hst : \|s·t\| = 3` | ⚠ `standard_st_order n` が model 側にあるが、`distinguishedInvolution` との同定が要る |
| `x₀ ∈ Z(Q)`, `≠ 1` | `exists_center_Q_ne_one` (汎用、(71)) |
| **`ih`** | ⚠⚠ **モデル内では導出不能** |

⚠⚠ **`ih : TheoremAInductionBelow (standardPermGroup n) (Unital n)` は
標準モデル単体からは出ない**。「`Nat.card A < Nat.card (standardPermGroup n)` なる
すべての `A`」を量化するので、これは Theorem A の帰納法仮説そのもの。
⟹ §4 が ambient の `ih` と `Nat.card (standardPermGroup n) ≤ Nat.card G` から供給する
(`theoremAInductionBelow_centralizerActionQuotient` と同じ形)。
その不等式は `standardPermGroup n ≅ U/Z(U)`、`U ≤ C_G(P) ≤ G` から出る見込み。

### ⚠ 次セッションはここから

1. `hst` — `standardHypothesis` の `distinguishedInvolution` を `sStd`
   (= `rootHom (RootGroup.centralInvolution n)`) と同定し、`standard_st_order n` を当てる。
   ⚠ `distinguishedInvolution` の定義 (どう選ばれるか) を先に実測すること。
2. `ih` の供給補題: `Nat.card (standardPermGroup n) ≤ Nat.card G` (経由:
   `residualQuotientEquiv` + `U ≤ C_G(P) ≤ G`) → `theoremAInductionBelow_standardModel`。
3. 揃ったら `lemmaFiveSetup_of_orderThree_of_mem_W` /
   `nonempty_quotientFieldModel_of_orderThree` → `exists_standardModel` →
   §3 段 (4) 鎖 → `corollaryTwo_of_stepFour`。
4. `residualQuotientEquiv` で `U/Z(U)` へ transport → 段 (2) → **§4 完成**。

## 2026-08-01 (88): 🎯 標準モデルの `hst` landing — `exists_standardModel` の前提は `ih` を残すのみ

(フルビルド green 4987 jobs・lint 純ゼロ)

* `standardHypothesis_distinguishedInvolution` — 区別された対合 =
  `rootHom (RootGroup.centralInvolution n)` (書籍 Ch. III §3 の `s = (0,1)`)。
  ⚠ 経路: `distinguishedInvolution` は `Classical.choose` で opaque だが、
  `eq_distinguishedPair_of_structure` (一意性) に候補を渡せば同定できる。
  候補は `s' = r' = rootHom(centralInvolution)` で、構造方程式
  `t s t = r⁻¹ t r` は標準組紐関係 `standard_braid` (`w s w = s w s`) がそのまま与える
  (`s` は対合なので `s⁻¹ = s`)。
* `standardHypothesis_orderOf_distinguishedInvolution_mul_t` — `|s t| = 3`
  (`standard_st_order`)。

### `exists_standardModel` の前提表 (標準モデル、最終)

| 前提 | 状態 |
|---|---|
| `hst` | ✅ **今回** |
| `hm : m ≠ 0` | ✅ `hn : 1 < n` |
| `hQ0card` / `hcardQ` | ✅ (87) |
| `hQsuz` | ✅ `standardRootSubgroup_isSuzuki2Group` (defeq、作業ゼロ) |
| `x₀ ∈ Z(Q)`, `≠ 1` | ✅ `exists_center_Q_ne_one` (汎用、(71)) |
| `hVW` (§3 endpoint 用) | ✅ `standardHypothesis_V_eq_W` (86) |
| **`ih`** | ⚠ **§4 が ambient から供給** ((87) で導出不能と確定) |
| `s : LemmaFiveSetup m` / `M : QuotientFieldModel m` | producer あり ((71))、上記が揃えば出る |

### ⚠ 次セッションはここから

1. **`ih` の供給補題**: `Nat.card (standardPermGroup n) ≤ Nat.card G` を
   `residualQuotientEquiv` (= `U/Z(U) ≃* standardPermGroup n`) と `U ≤ C_G(P) ≤ G` から
   出し、`theoremAInductionBelow_centralizerActionQuotient` と同形の
   `theoremAInductionBelow_standardModel` を作る。
   ⚠ `|U/Z(U)| ≤ |U| ≤ |C_G(P)| ≤ |G|` は素直だが、`Nat.card` の商での不等式
   (`Subgroup.card_quotient_le` 等) を実測すること。
2. 揃ったら `lemmaFiveSetup_of_orderThree_of_mem_W` (要 `w ∈ W#` — 標準モデルでは
   `W = V` = ノルム 1 トーラスなので `exists_ne_one_mem_psuTorus_torusWeight_eq_one`
   (`1 < n`) から直接出る) → `nonempty_quotientFieldModel_of_orderThree` →
   `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour`。
3. `residualQuotientEquiv` で `U/Z(U)` へ transport → 段 (2) → **§4 完成**。

## 2026-08-01 (89): 標準モデルの `W ≠ 1` landing + ⚠⚠ **`ih` に宇宙 (universe) の壁**

### landing

* `commute_weylElement_psuTorusHom_of_torusWeight_eq_one` — (A2) の逆向き。
* `exists_ne_one_mem_standardHypothesis_W` — `W = V` = ノルム 1 トーラス ≠ 1。

⟹ `exists_standardModel` / Lemma 5 producer が要る `w ∈ W#` が標準モデルで出た。

### ⚠⚠ `ih` は universe が合わない (実測)

```
def TheoremAInductionBelow (G : Type u) (Omega : Type v) … : Prop :=
  ∀ {A : Type u} {Lambda : Type v} …, Nat.card A < Nat.card G → …
```

`A` は **`G` と同じ universe `u`**。標準モデルは `standardPermGroup n : Type 0`、
`Unital n : Type 0` なので `TheoremAInductionBelow (standardPermGroup n) (Unital n)` は
`Type 0` の群だけを量化する。⟹ ambient `ih : TheoremAInductionBelow G Ω` (`G : Type u`)
からは `u = 0` でない限り**直接は取れない**。

⚠ `Hypothesis` 自体と §3 の endpoint (`corollaryTwo_of_stepFour` 等) は universe
polymorphic なので、標準モデルに当てること自体は問題ない。**`ih` だけが壁**。

### `ih` を Lemma 5 の結論で置換する案は不可 (実測)

`ih` は Lemma 5 の producer chain に**深く threading されている**:
`WCyclicDivides.lean:70,205` / `TypeBFromW.lean:162,196,340`。
単一の消費点ではないので「`IsCyclic W ∧ |W| ∣ q+1` に弱める」では済まない。

### 🧭 次の作業単位 = **`Hypothesis` の transport 構成**

必要なのは `Hypothesis A Λ` を群同型 + 同変全単射に沿って移す一般構成:

```
Hypothesis.ofMulEquiv (h : Hypothesis A Λ) (e : A ≃* B) (f : Λ ≃ Λ')
  (hf : ∀ a l, f (a • l) = e a • f l) : Hypothesis B Λ'
```

これが在れば
1. **`ih` の universe 問題**: `ULift.{u} A` へ移して ambient `ih` を当て、結論を戻す。
2. **段 (2) の結論 transport**: `standardPermGroup n` で得た `ω`, `ζ` を
   `residualQuotientEquiv` で `U/Z(U)` へ、さらに ambient へ持ち上げる。
両方に効く。⟹ **これを先に作るのが正しい順序**。

### ⚠ 次セッションはここから

1. `Hypothesis.ofMulEquiv` を構成する (フィールドを `e`/`f` で押し出すだけだが、
   `doubly_transitive` / `faithful` / `H_def` の transport に注意)。
   置き場は `Basic.lean` の下流の新 leaf か `QStructure` 手前。
2. それで `ih` の `ULift` 経由供給を作る。
3. → `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2)。

## 2026-08-01 (90): 🎯 `Hypothesis.ofMulEquiv` landing — universe の壁を越える道具

新 leaf `HypothesisTransport.lean` (`OddOrder.lean` 配線済、フルビルド green 4988 jobs・
lint 純ゼロ)。

```
Hypothesis.ofMulEquiv (h : Hypothesis A Λ) (e : A ≃* B) (f : Λ ≃ Λ')
  (hf : ∀ a l, f (a • l) = e a • f l) : Hypothesis B Λ'
```

⚠ **universe 制約なし** (`A`/`B`/`Λ`/`Λ'` は独立)。これが (89) の壁を越える道具。

### 実装メモ (再現用)

* `doubly_transitive` — `isMultiplyPretransitive_iff` に落とし tuple を
  `f.symm.toEmbedding` で引き戻す。⚠ `rw ... at h.doubly_transitive` は**不可**
  (射影に rw できない) — `have hdt := h.doubly_transitive` してから。
* `faithful` — `eq_of_smul_eq_smul` を `e.symm b` に当てて `e` で戻す。
* `D_def` — `Subgroup.mem_map_equiv` は **要素を量化した形**
  (`∀ K y, y ∈ K.map e ↔ e.symm y ∈ K`) で `have` しないと共役項 `(e t)⁻¹ b (e t)` に
  当たらない。
* `Q_mul_D_eq_H` — `Set.image_mul_of_injective` は mathlib に無い ⟹ `ext` + 両方向。
* `Q_even` / `D_odd` — `rwa` は不可 (仮定は射影なので `assumption` が拾わない)、
  `rw` + `exact h.Q_even`。

### ⟹ 次の設計 (確定)

段 (2) の §3 適用先は **`U/Z(U)` (= `U/(P∩U)`、`Type u`)** で、そこへ
`standardHypothesis` (`Type 0`) を `ofMulEquiv` + `residualQuotientEquiv.symm` で移す。
作用集合は `ULift.{v} (Unital n)` に持ち上げれば ambient の
`ih : TheoremAInductionBelow G Ω` (`Ω : Type v`) と universe が揃う。

| 供給物 | 経路 |
|---|---|
| `Hypothesis (U/Z(U)) (ULift (Unital n))` | `ofMulEquiv standardHypothesis residualQuotientEquiv.symm Equiv.ulift.symm` |
| `hVW` / `hQ0card` / `hcardQ` / `hst` / `hQsuz` / `w ∈ W#` | 標準モデルで証明済 ((86)-(89)) — transport 後の対応を示す補題が要る |
| `ih` | ambient `ih` + `Nat.card (U/Z(U)) < Nat.card G` (同 universe なので素直) |

### ⚠ 次セッションはここから

1. `ofMulEquiv` の**フィールド対応補題**を書く (`(h.ofMulEquiv e f hf).Q = h.Q.map e`
   等は `rfl` のはずだが、`V`/`W`/`Q0` は導出定義なので `map` と可換であることを
   別途示す必要がある — ここが次の実作業)。
2. `U/Z(U)` 上の `Hypothesis` を組み、`ih` を ambient から供給する。
3. → `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2)。

## 2026-08-01 (91): `ofMulEquiv` のフィールド対応補題 landing

(フルビルド green 4988 jobs・lint 純ゼロ)

| 補題 | 内容 |
|---|---|
| `map_centralizer_equiv` | `C(S).map e = C(e '' S)` |
| `map_inf_equiv` | `(K ⊓ L).map e = K.map e ⊓ L.map e` |
| `ofMulEquiv_H` / `_Q` / `_D` / `_t` | `rfl` (`@[simp]`) |
| `ofMulEquiv_V` / `_KSet` / `_W` / `_Q0` | 導出定義の transport |

⚠ 実装メモ (再現用):
* 導出定義の中の `(h.ofMulEquiv e f hf).t` は自動で `e h.t` に簡約されない ⟹
  `have ht : … = e h.t := rfl` を置いて `rw [ht]`。
* `rwa [..., e.symm_apply_apply, e.symm_apply_apply]` は片方が既に簡約済で失敗しうる
  ⟹ `simpa only [...] using h2` が頑健。
* 一般補題 2 本は `[Finite A] [Finite B]` 不使用 ⟹ `omit … in` (`unusedSectionVars`)。
* import は `Basic` → `QStructure` (`Q0` の定義元)。

### ⟹ 標準モデルの成果を transport 先へ移す準備が整った

`h' := standardHypothesis n hn |>.ofMulEquiv e f hf` について:
* `h'.V = V.map e`, `h'.W = W.map e` ⟹ **`hVW` は `standardHypothesis_V_eq_W` の
  `congrArg (Subgroup.map e)`** で出る。
* `h'.Q0 = Q0.map e` ⟹ `hQ0card` は `Nat.card` の同型不変性で。
* `h'.Q = Q.map e` ⟹ `hcardQ` / `hQsuz` (`IsSuzuki2Group.of_equiv`) も同様。
* `w ∈ h'.W` は像を取るだけ。

⚠ 残る非自明: **`hst`** — `distinguishedInvolution` は `Classical.choose` なので
`h'.distinguishedInvolution = e (h.distinguishedInvolution)` を**一意性経由**で示す必要
がある (`eq_distinguishedPair_of_structure` に `e s`, `e r` を渡す)。
`standardHypothesis_distinguishedInvolution` と同じ手口。

### ⚠ 次セッションはここから

1. `ofMulEquiv_distinguishedInvolution` を一意性経由で示す。
2. 上の 5 つを `h'` について並べる補題群を書く。
3. `U/Z(U)` 上の `Hypothesis` を `ofMulEquiv standardHypothesis residualQuotientEquiv.symm
   Equiv.ulift.symm` で組み、`ih` を ambient から供給
   (`Nat.card (U/Z(U)) < Nat.card G`)。
4. → `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2)。

## 2026-08-01 (92): 🎯 `ofMulEquiv` の transport 補題が全部そろった

(フルビルド green 4988 jobs・lint 純ゼロ)

| 補題 | 供給する前提 |
|---|---|
| `ofMulEquiv_distinguishedInvolution` | — (下の 2 本の土台) |
| `ofMulEquiv_orderOf_distinguishedInvolution_mul_t` | **`hst`** |
| `ofMulEquiv_V_eq_W` | **`hVW`** |
| `ofMulEquiv_natCard_Q0` / `_natCard_Q` | **`hQ0card`** / **`hcardQ`** |
| `ofMulEquiv_exists_ne_one_mem_W` | **`w ∈ W#`** |
| `ofMulEquiv_Q` (+ `IsSuzuki2Group.of_equiv`) | **`hQsuz`** |

⚠ `distinguishedInvolution` は `Classical.choose` なので transport で「計算」できない。
`(e s, e r)` を定義条件に当てて一意性 `eq_distinguishedPair_of_structure` で同定する
(`standardHypothesis_distinguishedInvolution` (88) と同じ手口)。

⟹ **標準モデルで証明した (86)-(89) の成果がすべて transport 先へ渡る**。

### 残り

1. **`U/Z(U)` 上の組み立て**: `residualQuotientEquiv : (U ⧸ Z(U)) ≃* standardPermGroup n`
   なので `e := residualQuotientEquiv.symm`、`f := Equiv.ulift.symm`
   (`Unital n ≃ ULift.{v} (Unital n)`)、`hf` は `ULift` の作用の定義から。
   ⚠ `ULift (Unital n)` 上の `MulAction` インスタンスをどう与えるか要実測
   (`Equiv.ulift` を使った transport が要る可能性)。
2. **`ih`**: ambient `ih : TheoremAInductionBelow G Ω` + `Nat.card (U ⧸ Z(U)) < Nat.card G`。
   ⚠ ただし `Ω` と `ULift (Unital n)` は別の型なので、`TheoremAInductionBelow` の
   `Lambda` は `Type v` を量化する ⟹ `ULift.{v} (Unital n) : Type v` なら合う。
3. → `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2)。

### ⚠ 次セッションはここから

1. `ULift` 上の `MulAction` transport (`MulAction.compHom` か `Equiv.ulift` 経由) を実測し、
   `standardHypothesis n hn |>.ofMulEquiv (MulEquiv.refl _) Equiv.ulift.symm _` で
   universe を上げた版を作る。
2. `Nat.card (U ⧸ Z(U)) < Nat.card G` を示す (`U ≤ C_G(P) ≤ G`、`Z(U) ≠ ⊥` か
   `C_G(P) < G`)。
3. `ih` を供給し `exists_standardModel` を呼ぶ。

## 2026-08-01 (93): 🎯 `standardHypothesisULift` — universe の壁を実際に越えた

(フルビルド green 4988 jobs・lint 純ゼロ)

```
standardHypothesisULift (n) (hn : 1 < n) :
  Hypothesis (standardPermGroup n) (ULift.{w} (Unital n)) :=
  (standardHypothesis n hn).ofMulEquiv (MulEquiv.refl _) Equiv.ulift.symm fun _ _ => rfl
```

⚠ 実測結果:
* `ULift.mulAction'` (`Mathlib/Algebra/Module/ULift.lean:61`) が
  `MulAction R (ULift M)` を与える (`MulAction.compHom` 不要)。
* 同変性 `Equiv.ulift.symm (m • a) = m • Equiv.ulift.symm a` は **`rfl`**。
* 群側は恒等同型なので部分群は一切動かない。

持ち上げ済の事実 (すべて (86)-(89) からの transport):
`standardHypothesisULift_V_eq_W` / `natCard_standardHypothesisULift_Q0` (`= 2ⁿ`) /
`natCard_standardHypothesisULift_Q` (`= |Q₀|³`) /
`standardHypothesisULift_orderOf_distinguishedInvolution_mul_t` (`= 3`) /
`exists_ne_one_mem_standardHypothesisULift_W`。

⚠ 実装メモ: `standardHypothesisULift` は素の `def` なので
`rw [Hypothesis.ofMulEquiv_natCard_Q0]` は**当たらない** (unfold されない)。
`exact` / `calc` の**項モード**で書けば defeq で通る。

### ⟹ §4 が使える形になった

`exists_standardModel` の前提のうち **`ih` 以外はすべて `standardHypothesisULift` について
証明済**。あとは:

1. `ih : TheoremAInductionBelow (standardPermGroup n) (ULift.{v} (Unital n))` を
   ambient `ih : TheoremAInductionBelow G Ω` から供給する。
   ⚠ universe は合った (`Ω : Type v`、`ULift.{v} (Unital n) : Type v`) が、**群側**は
   `standardPermGroup n : Type 0` と `G : Type u` で**まだ合わない**。
   ⟹ 群も `ULift` するか、`residualQuotientEquiv.symm` で `U/Z(U) : Type u` へ移すか。
   **後者が本筋** (書籍の対象そのもの)。
2. `Nat.card (U ⧸ Z(U)) < Nat.card G`。
3. → `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2)。

### ⚠ 次セッションはここから

1. **群側の transport**: `hU := standardHypothesisULift.ofMulEquiv residualQuotientEquiv.symm (Equiv.refl _) _`
   で `Hypothesis (U ⧸ Z(U)) (ULift.{v} (Unital n))` を作る。
   ⚠ `residualQuotientEquiv` は `CentralizerPSUData` のフィールドなので、§4 の枝データ
   から取り出す形になる。同変性 `hf` は `Equiv.refl` + 作用の定義から
   (作用は `MulAction.compHom` で引き戻す必要がある — 要実測)。
2. `Nat.card (U ⧸ Z(U)) < Nat.card G` → `ih` 供給。
3. → `exists_standardModel` 以降。

## 2026-08-01 (94): `ofMulEquivPullback` + `natCard_centralizer_lt`

(フルビルド green 4988 jobs・lint 純ゼロ)

* **`Hypothesis.ofMulEquivPullback (h) (e : A ≃* B)`** — 作用集合はそのままで群だけ
  `e` で移し、作用を `MulAction.compHom Λ e.symm.toMonoidHom` で引き戻す。
  ⚠ `ofMulEquiv h e (Equiv.refl Λ) _` として定義したので、**既存の `ofMulEquiv_*`
  transport 補題がそのまま defeq で使える** (新規補題不要)。
* **`natCard_centralizer_lt (hXV) (hX : X ≠ ⊥) : Nat.card ↥(C_G(X)) < Nat.card G`** —
  `card_centralizerActionQuotient_lt` の証明本体 (「中心的なら `H` の自明な normal core
  に入って矛盾」) を切り出して公開。元の定理は全射性で降ろす 3 行になった。

### ⟹ `ih` 供給の材料

`Nat.card (↥U ⧸ Z(U)) ≤ Nat.card ↥U ≤ Nat.card ↥(C_G(P)) < Nat.card G`
* 1 つ目: `Nat.card_le_card_of_surjective (QuotientGroup.mk' _)`
* 2 つ目: `U : Subgroup ↥C` なので `Subgroup.card_subgroup_dvd_card` + `Nat.le_of_dvd`
* 3 つ目: **今回の `natCard_centralizer_lt`**

### ⚠ 次セッションはここから

1. `Nat.card (↥U ⧸ Z(U)) < Nat.card G` を上の 3 段で組む。
2. `ih : TheoremAInductionBelow (↥U ⧸ Z(U)) (ULift.{v} (Unital n))` を ambient
   `ih : TheoremAInductionBelow G Ω` から供給する
   (`theoremAInductionBelow_centralizerActionQuotient` と同形)。
   ⚠ `Lambda` の universe は `ULift.{v}` で合わせてある (93)。
3. `hU := (standardHypothesisULift n hn).ofMulEquivPullback residualQuotientEquiv.symm`
   で `Hypothesis (↥U ⧸ Z(U)) (ULift.{v} (Unital n))` を作る
   (⚠ `residualQuotientEquiv` は `CentralizerPSUData` のフィールド)。
4. → `exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2)。

## 2026-08-01 (95): `ih` の制限補題 + `|U/Z(U)| < |G|` landing

(フルビルド green 4988 jobs・lint 純ゼロ)

* **`TheoremAInductionBelow.of_natCard_le (ih) (hle : Nat.card B ≤ Nat.card G) :
  TheoremAInductionBelow B Λ'`** — `TheoremAInductionBelow` は `Nat.card G` 未満を
  すべて量化するので、位数がそれ以下の任意の群へ制限できる。
  ⚠ **`B`/`Λ'` の universe は statement が許す範囲で自由** — これが (89) の壁を実際に
  通す補題。§4 は `B := ↥U ⧸ Z(U)` (`Type u`)、`Λ' := ULift.{v} (Unital n)` (`Type v`) で
  使う。
* **`natCard_residualQuotient_lt`** — `|U/Z(U)| < |G|`。3 段: 商の全射性 →
  `Subgroup.card_subgroup_dvd_card` → `natCard_centralizer_lt` (94)。

⚠ `theoremAInductionBelow_centralizerActionQuotient` を新補題で書き直すのは**前方参照**
になるので見送った (新補題は同 leaf の後方)。将来 leaf 整理するときに順序を入れ替える。

### ⟹ 段 (2)(b) に必要な部品はすべて揃った

| 部品 | 状態 |
|---|---|
| `Hypothesis (↥U ⧸ Z(U)) (ULift.{v} (Unital n))` | `ofMulEquivPullback` + `standardHypothesisULift` で**組むだけ** |
| `hVW` / `hQ0card` / `hcardQ` / `hst` / `w ∈ W#` | ✅ transport 補題群 (91)(92)(93) |
| `hQsuz` | ✅ `IsSuzuki2Group.of_equiv` |
| `x₀ ∈ Z(Q)` | ✅ `exists_center_Q_ne_one` (71) |
| **`ih`** | ✅ **今回** (`of_natCard_le` + `natCard_residualQuotient_lt`) |

### ⚠ 次セッションはここから

1. **組み立て**: §4 の枝データ (`CentralizerPSUData`) から `residualQuotientEquiv` を
   取り出し、`hU := (standardHypothesisULift n hn).ofMulEquivPullback
   residualQuotientEquiv.symm` で `Hypothesis (↥U ⧸ Z(U)) (ULift.{v} (Unital n))` を作る。
   ⚠ `n := data.n` で `1 < data.n` は `data.one_lt_n`。
2. 上表の前提を `hU` について並べ、`exists_standardModel` を呼ぶ。
3. → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2) の `ω`, `ζ` を得る。
4. 商から ambient へ持ち上げ (`IsFGH.eq_of_le`) ⟹ **段 (2) が閉じる** ⟹ §4 完成。

## 2026-08-01 (96): 🎯 `U/Z(U)` 上の標準仮説が組めた + §3 前提 5 本

新 leaf `PSU3SectionFourModel.lean` (`OddOrder.lean` 配線済、フルビルド green 4989 jobs・
lint 純ゼロ)。

* **`Hypothesis.residualQuotientHypothesis (details : CentralizerPSUData …)`** —
  標準 `PSU(3,ℓ)` モデルを `CentralizerPSUData.residualQuotientEquiv` に沿って
  `U/Z(U)` へ移した (A1)-(A3) carrier。書籍 p.133 が「`U`, `U ∩ H`, `t` に関して」
  §2/§3 を走らせる、その `U/(P∩U) = U/Z(U)` ((83) の裁定どおり)。
* 前提 5 本 (標準モデルからの transport):
  `residualQuotientHypothesis_V_eq_W` / `natCard_residualQuotientHypothesis_Q0` (`= 2ⁿ`) /
  `natCard_residualQuotientHypothesis_Q` (`= |Q₀|³`) /
  `..._orderOf_distinguishedInvolution_mul_t` (`= 3`) /
  `exists_ne_one_mem_residualQuotientHypothesis_W`。
* 支援: `HypothesisTransport.lean` に `ofMulEquivPullback_*` 5 本。

### ⚠ 実装メモ (再現用、どれも 1 回ずつ踏んだ)

1. **型の `letI` は項モードの本体からは見えない** ⟹ `by letI := …; exact …` にする。
2. `ofMulEquivPullback` は同変性証明を**内部で固定**するので、汎用 `ofMulEquiv_*` を
   使用点で当てると `hf` が推論できない ⟹ pullback 形の言い直しが要る。
3. `ULift` を含む補題は **universe を明示** (`.{v}`) しないと universe metavariable が残る。

### ⚠⚠ 未解決: `theoremAInductionBelow_residualQuotient` が elaborate しない

`TheoremAInductionBelow.of_natCard_le` を `B := ↥U ⧸ Z(U)`, `Λ' := ULift.{v} (Unital n)`
で当てようとすると **`Finite ?m` で typeclass instance problem is stuck**。
`(G := G) (Ω := Ω) (B := …) (Λ' := …)` を明示しても解消しなかった。
⟹ **この 1 本だけ leaf から外して commit** (他の 5 本と carrier はすべて green)。

⚠ 次セッションの調査方針:
* `of_natCard_le` の `[Finite B]` が `↥U ⧸ Z(U)` について合成できているか単独で確認する
  (`example : Finite (↥(residual X) ⧸ Subgroup.center _) := inferInstance`)。
  `Subgroup.center` の引数が `_` のままだと決まらない可能性が高い ⟹
  `Subgroup.center ↥(residual (G := G) X)` と完全に書く。
* それでも駄目なら `@TheoremAInductionBelow.of_natCard_le` で全引数明示。
* あるいは `of_natCard_le` の `[Finite B]` を `Finite B` の明示引数に変える。

### ⚠ 次セッションはここから

1. 上記 `ih` 供給の 1 本を通す。
2. 6 本そろったら `exists_standardModel` を `residualQuotientHypothesis` に当てる。
3. → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2) の `ω`, `ζ`。
4. 商から ambient へ持ち上げ (`IsFGH.eq_of_le`) ⟹ **段 (2) が閉じる** ⟹ §4 完成。

## 2026-08-01 (97): 🎯 `ih` 供給 landing — 段 (2)(b) の前提が**全部そろった**

`theoremAInductionBelow_residualQuotient` (フルビルド green 4989 jobs・lint 純ゼロ)。

⚠ **(96) の未解決点の原因は数学でなく elaboration だった**。汎用補題
`TheoremAInductionBelow.of_natCard_le` を当てると `Finite ?m` で stuck になるのは、
`TheoremAInductionBelow` が**素の `def`** なので goal との unify で `B` が決まらないため
(`(B := …) (Λ' := …) (G := G) (Ω := Ω)` を全部明示しても解消しなかった)。
⟹ **`intro` で直接展開して ambient `ih` を当てれば通る**
(`TheoremAInductionBelow` は `∀` に展開されるので `intro` が効く)。
⚠ 同種の「汎用補題が当たらない」は今後も起きるので、**`TheoremAInductionBelow` 系は
`intro` で開くのが定石**と覚えておく。

### 🎯 `residualQuotientHypothesis` について前提が全部そろった

| 前提 | 供給元 |
|---|---|
| `hst` | `residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t` |
| `hm : n ≠ 0` | `data.one_lt_n` |
| `hQ0card` | `natCard_residualQuotientHypothesis_Q0` |
| `hcardQ` | `natCard_residualQuotientHypothesis_Q` |
| `ih` | **今回** |
| `x₀ ∈ Z(Q)`, `≠ 1` | `exists_center_Q_ne_one` (汎用、(71)) |
| `hVW` (§3 endpoint) | `residualQuotientHypothesis_V_eq_W` |
| `w ∈ W#` (Lemma 5) | `exists_ne_one_mem_residualQuotientHypothesis_W` |
| `hQsuz` | `IsSuzuki2Group.of_equiv` + `standardRootSubgroup_isSuzuki2Group` |

### ⚠ 次セッションはここから

1. `lemmaFiveSetup_of_orderThree_of_mem_W` → `nonempty_quotientFieldModel_of_orderThree`
   → **`exists_standardModel` を `residualQuotientHypothesis` に当てる**。
   ⚠ `hQsuz` は `(residualQuotientHypothesis details).Q` が標準根群の像であることを
   使う ⟹ `ofMulEquivPullback_Q` 相当 (`ofMulEquiv_Q` は `rfl`) + `of_equiv`。
2. → §3 段 (4) 鎖 (`stepFour_star`/`base`/`pointwise`/`at_omega`/`cover`) →
   `corollaryTwo_of_stepFour` → 段 (2) の `ω`, `ζ`。
3. 商から ambient へ持ち上げ (`IsFGH.eq_of_le`) ⟹ **段 (2) が閉じる** ⟹ §4 完成。

## 2026-08-01 (98): 🎯 §2/§3 が `U/Z(U)` の中で走る

(フルビルド green 4989 jobs・lint 純ゼロ)

* `isSuzuki2Group_residualQuotientHypothesis_Q` — `Q` は標準根群の像なので
  `standardRootSubgroup_isSuzuki2Group` + `Subgroup.equivMapOfInjective` 2 段 +
  `IsSuzuki2Group.of_equiv`。
* **`nonempty_standingData_residualQuotient`** — §4 の ambient 仮説
  (`hXV` / `hX` / `ih` / 枝データ `details`) だけから `U/Z(U)` について
  `LemmaFiveSetup data.n` と `QuotientFieldModel data.n` の**両方**が出る。

⚠ 実装メモ (罠の族、(96)(97) と同じ): 型に `letI` を持つ補題を `have h := …` で
受けると `Finite ?m` で stuck ⟹ **期待型を明示**
(`have ihq : TheoremAInductionBelow … := …`) すれば通る。

### ⟹ 段 (2)(b) は `exists_standardModel` を呼ぶだけ

残る作業:
1. `exists_standardModel` を `residualQuotientHypothesis` に当てる
   (`sfive`, `M` は今回の standing data、6 前提は (97) の表)。
2. §3 段 (4) 鎖 (`stepFour_star` → `base` → `pointwise` → `at_omega` → `cover`) を
   `U/Z(U)` 上で走らせ `hcover` を作る。
   ⚠ ここが (60) で言った「多量の仮説スレッディング」の本体。
   `corollaryTwo_of_stepFour` は ~25 前提を取る。
3. `corollaryTwo_of_stepFour` → 段 (2) の `ω`, `ζ`。
4. 商から ambient へ持ち上げ (`IsFGH.eq_of_le`) ⟹ 段 (2) 完了 ⟹ **§4 完成**。

### ⚠ 次セッションはここから

1. `exists_standardModel` を当てて出力 (`φ`, `Φ`, `Θ`, `u`, `d`, `hequiv` …) を取り出す。
2. 段 (4) 鎖を順に当てる。⚠ 各段の前提は前段の出力なので、`obtain` で受けながら
   一直線に流せるはず。詰まったら §3 側 (`PSU3InverseFormula.lean`) の
   `stepFour_cover` の呼び出し形を読んで合わせる。

## 2026-08-01 (99): `x₀` も `U/Z(U)` へ — 前提が実際に**全部** landing

`exists_center_Q_ne_one_residualQuotient` (フルビルド green 4989 jobs・lint 純ゼロ)。

### `U/Z(U)` について landing 済の一覧 (これで完全)

| 供給物 | 補題 |
|---|---|
| carrier `Hypothesis (↥U ⧸ Z(U)) (ULift (Unital n))` | `residualQuotientHypothesis` (96) |
| `hst` | `residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t` |
| `hm` | `data.one_lt_n` |
| `hQ0card` / `hcardQ` | `natCard_residualQuotientHypothesis_Q0` / `_Q` |
| `ih` | `theoremAInductionBelow_residualQuotient` (97) |
| `x₀` | **今回** |
| `hVW` | `residualQuotientHypothesis_V_eq_W` |
| `w ∈ W#` | `exists_ne_one_mem_residualQuotientHypothesis_W` |
| `hQsuz` | `isSuzuki2Group_residualQuotientHypothesis_Q` (98) |
| `LemmaFiveSetup` / `QuotientFieldModel` | `nonempty_standingData_residualQuotient` (98) |

### ⚠ 残る作業は **1 本の大きな threading 証明**

`exists_standardModel` → §3 段 (4) 鎖 → `corollaryTwo_of_stepFour` は、
中間出力 (`φ`, `Φ`, `Θ`, `u`, `d`, `hequiv`, `ι`, `hker`, `Ψ`, `hΨq`, `hΨc`,
`hconjq`, `hconjy`, `hdsq`, `hs`, `hmu`, `hKcard`, `hWdvd`, `hW1`, `hfQ`, `hhW`,
`ω₀`, `hcover` …) を一直線に受け渡す **~25 前提の証明**になる。
分割して commit できる自然な境界が乏しいので、fresh context で一気に書くのが吉
((60) の見立てどおり)。

⚠ 着手時の注意 (これまでに踏んだ罠):
* 型に `letI` を持つ補題を `have` で受けるときは**期待型を明示**する。
* `TheoremAInductionBelow` 系の goal は `intro` で開く (汎用補題は unify しない)。
* `ULift` を含む補題は universe を明示 (`.{v}`)。

### ⚠ 次セッションはここから

1. `PSU3InverseFormula.lean` の `stepFour_cover` / `stepFour_at_omega` /
   `stepFour_pointwise` / `stepFour_base` / `stepFour_star` の**呼び出し形**を読み、
   各段が要る前提と前段の出力の対応表を作る (先に読んでから書く)。
2. `exists_standardModel` の出力と突き合わせ、足りないものだけを個別に補う。
3. 一気に threading して `corollaryTwo_of_stepFour` を呼び、段 (2) の `ω`, `ζ` を得る。
4. `IsFGH.eq_of_le` で ambient へ持ち上げ ⟹ **§4 完成**。

## 2026-08-01 (100): 🔍 段 (4) 鎖の呼び出し形を実測 — 橋は**既に在る**

### 段 (4) 鎖 (`PSU3InverseFormula.lean`) の前提は 3 段とも**同一**

`stepFour_star` (163) / `stepFour_base` (312) / `stepFour_pointwise` (378) はいずれも

`H`, `hC2`, `sfive`, `M`, `hZc`, `hmu`, `hVW`, `Φ`, `hquot`, `ι`, `hker`, `hu`, `Ψ`,
`hΨq`, `hΨc`, `hconjq`, `hconjy`, `d`, `hequiv`, …

という**同じ長いリスト**を取る。`stepFour_at_omega` (451) はもっと短く
(`M`, `hu`, `Ψ`, `hconjq`, `hconjy`, `ζ`, `ω`, `hf`, `hx`)、`stepFour_cover` (867) は
`M`, `hu`, `Ψ`, `ω`, `hxne`, `h1`, `h2`。`corollaryTwo_of_stepFour` (`PSU3StepFive.lean:566`)
も同じリスト + `hcover`, `hhW`, `ζ`。

⟹ **一度そろえれば全部に使い回せる**。分割の必要は薄い。

### 🔑 `exists_standardModel` の出力 → `Ψ` への橋は既存 (`PSU3RootGroupModel.lean`)

| 補題 | 行 | 役割 |
|---|---|---|
| `exists_modelEquiv_conj` | 696 | `exists_standardModel` の出力 (`Φ`, `Θ`, `u`, `hquot`, `hΘq`, `hu`, `hconj`, `hmu`) を取り、共役の振る舞いが良い `Φ'` を返す |
| `exists_unitaryModel_conj` | 609 | `Φ'` から **hermitian cocycle 版 `Ψ`** と `hΨq` / `hΨc` / 共役則を作る |
| (183 付近の無名補題) | 214-306 | `hsemi`/`haniso`/`hW` から `u`, `hu`, `e`, `Ψ` を出す版 |

⟹ **鎖は `exists_standardModel` → `exists_modelEquiv_conj` → `exists_unitaryModel_conj`
→ 段 (4) 鎖 → `corollaryTwo_of_stepFour`**。新規の数学は要らない。

### 残る前提の出どころ (`U/Z(U)` について)

| 前提 | 出どころ |
|---|---|
| `hZc` | `sfive.centerEqQ0` |
| `hWdvd : \|W\| ∣ 2^m+1` | Lemma 5 (`lemmaFive_of_orderThree` の第 2 成分) |
| `hW1 : 1 < \|W\|` | `exists_ne_one_mem_residualQuotientHypothesis_W` から |
| `hKcard : \|K\| = 2^m−1` | `card_K_eq_card_Q0_sub_one` + `hQ0card` |
| `hmu` | `M.mu` の単射性 — `QuotientFieldModel` のフィールドか要実測 |
| `H : IsFGH …`, `hfQ`, `hhW` | §1 の `exists_fgh` (`RankOneBNPair.lean`) |
| `hC2` | `hst` (`|st| = 3`) から (`orderThree` 系) |
| `ω₀`, `hcover` | 段 (4) 鎖の出力 |

### ⚠ 次セッションはここから

1. `exists_standardModel` を `residualQuotientHypothesis` に当て、
   `exists_modelEquiv_conj` → `exists_unitaryModel_conj` で `Ψ` まで進む。
2. 上表の残り前提を個別に埋める (`hmu` と `H : IsFGH` が要実測)。
3. 段 (4) 鎖 → `corollaryTwo_of_stepFour` → 段 (2) の `ω`, `ζ`。
4. `IsFGH.eq_of_le` で ambient へ持ち上げ ⟹ **§4 完成**。

## 2026-08-01 (101): `hmu` landing + (100) の ⚠ 2 点は既存資産で埋まると実測 — **セッション区切り**

(フルビルド green 4989 jobs・lint 純ゼロ)

* `mu_injective_residualQuotient` — `M.mu` の単射性 (`hmu`)。
* 実測 1: **`hmu`** は `QuotientFieldModel` のフィールドではない (フィールドは
  `mu_K_injective` = K 部分のみ) が、`QuotientKWField.lean:504` の **`mu_injective`** が
  `hst`/`hm`/`hQ0card`/`hcardQ`/`ih`/`sfive`/`M` から全体の単射性を出す。
* 実測 2: **`H : IsFGH`** は `RankOneSetup.lean:115` の **`exists_fgh`** が
  **任意の `hyp`** について与える (`hyp.rankOneSetup` 経由)。新規補題**不要**。

⚠ lint: `∀ (sfive : …)` の binder が結論で参照されないと `unusedVariables` ⟹ `_sfive`。

### 🧭 セッション区切り時点の状態 (ユーザー指示により中断)

**段 (2)(b) の前提はすべて `U/Z(U)` について landing 済**:
carrier / `hst` / `hm` / `hQ0card` / `hcardQ` / `ih` / `x₀` / `hVW` / `w ∈ W#` /
`hQsuz` / `LemmaFiveSetup` / `QuotientFieldModel` / `hmu`。
`H : IsFGH` と `hfQ` / `hhW` は `exists_fgh` から即取れる。

### ⚠ 再開時はここから (残りは 1 本の大きな threading 証明)

1. `exists_standardModel` を `residualQuotientHypothesis` に当てる。
2. `exists_modelEquiv_conj` (`PSU3RootGroupModel.lean:696`) →
   `exists_unitaryModel_conj` (:609) で `Ψ` / `hΨq` / `hΨc` / `hconjq` / `hconjy`。
3. 残り: `hZc = sfive.centerEqQ0` / `hWdvd`・`hW1` (Lemma 5 と `w ∈ W#` から) /
   `hKcard = card_K_eq_card_Q0_sub_one + hQ0card` / `hC2` (`|st| = 3` から) /
   `ι`, `hker`, `d`, `hequiv`, `hdsq`, `hs` (`exists_standardModel` の出力)。
4. 段 (4) 鎖 (`stepFour_star`/`base`/`pointwise`/`at_omega`/`cover`; 前提は共通) →
   `corollaryTwo_of_stepFour` → 段 (2) の `ω`, `ζ`。
5. `IsFGH.eq_of_le` で ambient へ持ち上げ ⟹ 段 (2) 完了 ⟹ **§4 完成**
   (段 (3)-(10) は landing 済)。

⚠ 踏んだ罠 (再開時に注意): 型に `letI` を持つ補題を `have` で受けるときは**期待型を明示** /
`TheoremAInductionBelow` 系の goal は **`intro` で開く** (汎用補題は unify しない) /
`ULift` を含む補題は **universe を明示** (`.{v}`) / `∀` binder が未参照なら `_` 前置。

## 2026-08-01 (102): 🎯 §3 が閉じた — Corollary 2 が「モデル + 型 B 対 + base pair」だけに

新 leaf `OddOrder/Peterfalvi/Appendices/Suzuki/PSU3CorollaryTwo.lean` (656 行, sorry 0)。
(100)(101) で「残りは 1 本の大きな threading 証明」と書いた本体を通した。

### 段 (4) 鎖 → `hcover` (`corollaryTwo_of_stepFour` が残していた唯一の入力)

| 定理 | 内容 |
|---|---|
| `stepFour_fibre` | 段 (4) の **1 回分**。`stepFour_base` で基点の unitary 座標 = `μ(1,ζ)` を出し、`stepFour_elem` の 3 入力 (`stepFour_pointwise` / `stepTwo_quotient` / `stepFour_at_omega`) をそろえる。戻り値に基点の値も返すので呼ぶ側が `hx` を再計算しない |
| `stepFour_cover_of_base` | `(ω, ζ)` と `(ω⁻¹, ζ⁻¹)` の 2 回を `stepFour_cover` で貼る = **`hcover`** |
| `corollaryTwo_of_base` | Corollary 2、残る仮説は §2 の base pair と `hstage3` のみ |

⚠ 2 回目に新しい数学は要らない: `f_inv_eq` が標準仮説を移し、段 (3) は
`quotient_inv_eq` (反転は商座標を動かさない) と `μ(1,ζ⁻¹) = μ(1,ζ)⁻¹` で跡
`μ(1,ζ)+μ(1,ζ)⁻¹` が不変ゆえそのまま成立。除外点が食い違うのは `mu_W_ne_inv`。

⚠ `stepFour_cover` の結論は分子が `(Ψ ω₀).quotient`、`corollaryTwo_of_stepFour` の
`hcover` は `(Ψ ρ).quotient` を要求 — ファイバー仮説の下で等しいので
`stepFour_cover_of_base` 側で合わせた。

### `exists_standardModel` の強化 (`ModelAction.lean`)

段 (1)-(5) は中心座標 `ι` と `hker : Φ z = ⟨0, ι z⟩` の中で計算するのに、
`exists_standardModel` はそれを結論に出していなかった (証明の中には
`exists_mulEquiv_bookCocycle` の出力として在った)。結論に追加:
`ι` / `hker` / 対角スケール則 `hdiagscale` / `∃ d` ブロックの `ι` 版 `hequiv`。
証明本体は `refine` 1 行の変更のみ。既存 consumer なし。

### モデル → Corollary 2 (`corollaryTwo_of_standardModel`)

`exists_standardModel` の出力 + §3 (3) の 2 結論 (`hθ`, `hα`) + base pair から直接。
中で組み立てるもの:

* `hθ` ⟹ `hbil` ⟹ `cocycle_diag_eq_norm` で対角が `φ(1,1)·x^{1+q}`;
* その形が不透明な指数 `d` を 2 乗と同定 (`mu_K_zpow_eq_sq`) — 「θ = 1」の中身;
* `exists_modelEquiv_conj` (共役作用を点ごと) → `exists_unitaryModel_conj` (ユニタリ座標)。
  ⚠ `Φ'` の `hker` は「中心の像を動かさない」条件 + 元の `hker` で**同じ `ι`** のまま出る;
* 書籍の正規化 `s = (0,1)` は `ν := c(s)⁻¹` (`hs`);
* base pair での段 (3) = `stepThree_quotient_norm` を `hα` で読む。§2 の形
  `f(ω₀) = ζ₀⁻¹(ω₀y₀)ζ₀` は `f_eq_conj_inv_of_sq_eq` で反転公式へ。

### §3 (3) の梱包 (`stepThree_model`) と合成 (`corollaryTwo_of_sectionThree`)

`stepThree` は結論を型 B のスカラー対 (σ, τ) 越しに述べる (第 1 = 「F 上 σ = τ」、
第 2 = σ⁻¹ を掛けた `α`)。`thetaModel_eq_id_on_frobFixed` が「F 上 σ = τ」を
「F 上 σ = 1」に格上げすると σ が両方から消え、同時に**モデルの捻れ θ が F 上恒等**も
出る ⟹ 出力はちょうど `hθ` と `hα`。

⟹ **`corollaryTwo_of_sectionThree`**: 残る仮説は
**(a) Ch. III §3 Proposition の出力** (= `exists_standardModel`)、
**(b) 型 B のスカラー対 (σ, τ) と `hscale` / `hWinv`**、
**(c) §2 が閉じる base pair** の 3 つだけ。

### 🔍 実測: 型 B の σ, τ は導出できない (回避策を探した記録)

`hscale : σ(μ(k,1))·τ(μ(k,1)) = μ(k,1)^d` と `hWinv : σ(μ(1,v))·τ(μ(1,v)) = 1` を
既存資産から作れないか検討したが**不可**:

* `σ = id, τ = Frob^m` — `hWinv` は `mu_W_normOne` で ✅ だが `hscale` が `hdsq`
  (`μ(k,1)^d = μ(k,1)²`) と同値になり循環 (`hdsq` は `hnorm` ⟸ `hθ` ⟸ `stepThree` 経由)。
* `σ = id, τ = θ_model` — `hscale` は `hsemi` + `hscaleQ0` から ✅ (`hmodel`) だが
  `hWinv` が `θ(μ(1,v)) = μ(1,v)⁻¹` を要求し、これは「θ = Frob^m」そのもの。
* `hsemi` を `E` 全体へ広げる路も不可: `φ : E×E → F` なので `a·θ(b)·φ(x,y) ∈ F` が
  全 `a,b ∈ E` で成り立つのは `φ ≡ 0` のときだけ。

⟹ 書籍どおり**型 B の資料に属する外部入力**として仮説に残す (`stepThree` の
docstring の判断と一致)。数学的な内容は「`a·θ(a) = a^d` が `F^×` 上で成り立つので
`1 + 2^j ≡ d (mod 2^m−1)`、`j = 0` を決めるのが §3 (3) の数え上げ」。

### ⚠ 次セッションはここから (§4 段 (2))

`corollaryTwo_of_sectionThree` を `U/Z(U)` に当てる。必要な入力の所在 (実測済):

| 入力 | 出どころ |
|---|---|
| carrier / `hst` / `hm` / `hQ0card` / `hcardQ` / `ih` / `x₀` / `hVW` / `w ∈ W#` / `hQsuz` / `sfive` / `M` / `hmu` | `PSU3SectionFourModel.lean` に landing 済 (96)-(101) |
| `hZc` | `sfive.centerEqQ0` (`LemmaFiveSetup` のフィールド) |
| `hC2` | `braid_of_involutions_of_orderOf_mul_eq_three` (`OrderThreePSL.lean:42`) を `hst` に |
| `hKcard` | `card_K_eq_card_Q0_sub_one` + `hQ0card` |
| `hWdvd` | Lemma 5 (`lemmaFive_of_orderThree`, `WCyclicDivides.lean:356`) |
| `hW1` | `exists_ne_one_mem_residualQuotientHypothesis_W` |
| `H : IsFGH` | `exists_fgh` (`RankOneSetup.lean:115`) — 任意の `hyp` に与える |
| `hfQ` | ⚠ `IsFGH.mem` は `x ≠ 1` 付き。`f' := fun x => if x = 1 then 1 else f x` に取り替えれば `IsFGH` は保たれる (`IsFGH` は `Q^#` 上の 2 フィールドのみ) |
| `hhW` | ⚠ **未**。`h_mem_W` (`PSU3StepEighteen.lean:171`) は特定の `ω` について §2 の鎖データ込みで出す。∀ 版は要検討 |
| `hcard : 5 ≤ \|F\|` | 書籍の `\|F\| ≥ 8` (θ の位数が奇 ⟸ 型 B)。仮説のまま |
| σ, τ, `hscale`, `hWinv` | 型 B の資料 (上記のとおり導出不可) |
| base pair | §2 の閉じの Proposition (`f_eq_conj_inv_of_stepTwenty_chain`) |

⟹ **`exists_standardModel` を `residualQuotientHypothesis` に当てる**のが次の 1 手
(7 入力は全部 landing 済)。その後 `corollaryTwo_of_sectionThree` で段 (2) の `ω`, `ζ`、
最後に `IsFGH.eq_of_le` で ambient へ。

## 2026-08-01 (103): §3 の入力を全部 landing + `IsFGH.map` (商版の一意性)

(102) の続き。`corollaryTwo_of_sectionThree` の仮説のうち標準仮説から出るものと、
§4 段 (2) の「relative to `U`」の橋を landing。

### `IsStandardModel` 述語化 と `U/Z(U)` 版

* `ModelAction.lean`: `exists_standardModel` の結論 (11 節の連言) を
  **`Hypothesis.IsStandardModel s M x₀`** として切り出した (定義は逐語で同じ、
  証明は無変更)。⚠ 目的は §4 が同じ Proposition を `U/Z(U)` について**述べ直さずに**
  言えること。
* 新 leaf `PSU3SectionFourCorollaryTwo.lean`: **`isStandardModel_residualQuotient`** —
  `residualQuotientHypothesis` について Ch. III §3 の Proposition が成り立つ
  (5 入力は (96)-(101) で移してあったものをそのまま当てるだけ)。

### 残り入力 3 本 (`PSU3CorollaryTwo.lean`)

| 定理 | 供給する仮説 |
|---|---|
| `braid_of_orderThree` | `hC2` (`s`,`t` 対合 + `\|st\| = 3` ⟹ braid) |
| `one_lt_natCard_W` | `hW1` |
| `exists_fgh_mapsTo` | `hfQ` — ⚠ `IsFGH` は `f` を `Q^#` 上でしか縛らないので `exists_fgh` の `f` は `1` の行き先が不定。`1` での値を `1` に取り替えると `IsFGH` が見るものは不変で `f : Q → Q` になる |

`hKcard` / `hWdvd` は既存の `card_actualKActor_eq` / `lemmaFive_of_orderThree` が
そのまま与えるのでラッパーは書かない (ラッパー方針)。

### `IsFGH.map` (`OddOrder/GroupTheory/RankOneBNPair.lean`)

`IsFGH.eq_of_le` (部分群版) の**商版**。準同型 `π` が rank-one setup を別の setup へ
運ぶ (`π t = t'`, `Q → Q'`, `D → D'`) なら、定義式の π 像は下の setup にとっても
canonical 分解なので `fgh_eq_of_canonical` が `f₁(π x) = π (f x)` 等を与える。
⚠ 仮説は `x ≠ 1` でなく **`π x ≠ 1`** (π が潰す元では `f₁` を縛るものが無い)。

⟹ 書籍 p.133 段 (2) の「`U/Z(U)` で示した Corollary 2 を `U` の中で読む」
(結論が核 = `P ∩ U` を法として成り立つ) の道具。

### ⚠ 次セッションはここから — 残る **1 つの本物の同定**

段 (2) を閉じるのに要る配線は、`IsFGH.map` を `π : U → U/Z(U)` に当てること。
そのために必要な**未検証の点** (次の一手はここの実測):

1. **`U` 自身の `Setup`** (`M = U ∩ H`, `Q ∩ U`, `D ∩ U`, `t`) が repo に在るか。
   `t ∈ U` は landing 済 (`t_mem_primeComplementResidual`)。
2. **`π t = t̄`** — ⚠ ここが本物の同定。`residualQuotientHypothesis` の `t̄` は
   `standardHypothesisULift` の `t` を `residualQuotientEquiv.symm` で引き戻したもので、
   ambient の `t` の像とは**定義上は別物**。「Ch. I §3 Prop 1(c) の同一視が `t` を
   標準モデルの区別された対合へ送る」ことを示す必要がある
   (`CentralizerPSUData.residualQuotientEquiv` の構成を読むこと)。
   ⚠ 共役で済む可能性もある (`Hypothesis` の `t` は共役を除いて決まる) が、
   §4 は**同じ `t`** を使うので、共役なら共役元で `Hypothesis` を取り替える必要がある。
3. `Q ∩ U → Q̄`, `D ∩ U → D̄` の像条件。

⟹ 次の一手 = **`CentralizerPSUData.residualQuotientEquiv` の構成を読み、`t` の行き先を
実測する**。

## 2026-08-01 (104): 🔍 `π t = t̄` は**そのままでは成り立たない** — 経路は共役で確定

(103) の「次の一手」を実測した結果、**設計上の要点**が 1 つ判明した。

### 実測: `residualQuotientEquiv` は `t` について何も言わない不透明データ

`CentralizerPSUData.residualQuotientEquiv` は**構造体のフィールド**で、
`centralizer_trichotomy_of_induction` での構成は

```
residualQuotientEquiv := (hyp.centralizerResidualQuotientEquiv hXV hCQ).trans eTarget
```

`eTarget` は**帰納法が返す `TheoremAConclusion` の `data.groupEquiv`** — 完全に不透明。
⟹ `residualQuotientHypothesis` の `t̄` (標準モデルの `t` を引き戻したもの) が
ambient の `t` の像 `π t` と一致する保証は**無く、フィールドを足して主張することも
できない** (構成側で証明できないので unsound になる)。

### 🔑 経路: 対合は 1 つの共役類 (Ch. I Prop 2(b)) — 既に repo に在る

`Hypothesis.isConj_of_involutions` (`InvolutionClass.lean:149`) が
**任意の `Hypothesis` について「`G` の対合は単一の共役類」**を与える。
`residualQuotientHypothesis` にこれを当てればよい:

1. `t ∈ U` は landing 済 (`t_mem_primeComplementResidual`)。`Z(U) = P ∩ U` は
   奇位数なので `π t ≠ 1`、かつ `(π t)² = 1` ⟹ `π t` は `U/Z(U)` の対合。
2. `isConj_of_involutions` (対 `residualQuotientHypothesis`) で `IsConj t̄ (π t)`、
   すなわち `π t = c * t̄ * c⁻¹` なる `c` を得る。
3. `Hypothesis.ofMulEquiv` は **`t := e h.t`** と定める
   (`HypothesisTransport.lean`)。`e := MulAut.conj c`、点の写像を `ω ↦ c • ω`
   (内部自己同型と作用は両立: `(c g c⁻¹) • (c • ω) = c • (g • ω)`) に取ると、
   **`t` が `π t` である `Hypothesis` が `U/Z(U)` 上で得られる**。
4. そこへ `IsFGH.map` (`π : U → U/Z(U)`) を当てる ⟹ 書籍 p.133 の
   `f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)`、`h₁(ω) ∈ ζ₁³(P ∩ U)`。

⚠ (96)-(101) で landing した `U/Z(U)` の供給物 (`hVW`, `hQ0card`, …) は
`residualQuotientHypothesis` について述べてあるので、**共役でひねった版へ移す**
補題が要る (どれも `ofMulEquiv_*` transport で機械的。`ofMulEquiv` は
`MulAut.conj c` について `Q`, `Q0`, `W`, `V` を `map (conj c)` に送る)。

### ⚠ 次セッションはここから

1. `conjugateHypothesis` (仮称) — `Hypothesis A Λ` と `c : A` から
   `MulAut.conj c` + `ω ↦ c • ω` で移した `Hypothesis`。`ofMulEquiv` の特殊化。
2. `π t` が対合であること (`Z(U)` の奇位数 = `P` が奇素数位数から)。
3. `isConj_of_involutions` で `c` を取り、`t = π t` の `Hypothesis` を作る。
4. (96)-(101) の供給物をその版へ移す (`ofMulEquiv_*`)。
5. `IsFGH.map` + `IsFGH.eq_of_le` ⟹ 段 (2) 完了。

### (104) 続き: `Hypothesis.conjugate` landing

`HypothesisTransport.lean` に `conjugate` (= `ofMulEquiv` を `MulAut.conj c` +
点の写像 `ω ↦ c • ω` に特殊化) と `conjugate_t : (h.conjugate c).t = c * h.t * c⁻¹`
(`rfl`) を追加。上記手順 1 が landing。

⚠ ただし手順 4 (「(96)-(101) の供給物を共役版へ移す」) を書く前に、**段 (2) の
`IsFGH.map` に何が要るかを正確に測ること**:

* `IsFGH.map` は下の setup として `Setup M'' Q'' D'' t''` と
  `hQπ : ∀ y ∈ Q_U, π y ∈ Q''`、`hDπ` を要求する。
* `Q''` は自由に選べない: `Hypothesis` の公理から **`Q = O_2(H)`**
  (`Q ⊴ H`, `Q ⊓ D = ⊥`, `Q·D = H`, `Q` even, `D` odd ⟹ `Q` は `H` の正規 Hall
  2-部分群で一意)、`H = stabilizer(basept)`、`D = H ⊓ H^t` なので、
  **`Hypothesis` は `(basept, t)` で決まる**。
* ⟹ `t'' = π t` に合わせても、`H'' = π(U ∩ H)` になるかは **base point の選び方**
  次第。ここが段 (2) の残る本物の同定。
* 逆に `π(Q ∩ U)` が `H''` の正規 Hall 2-部分群であることさえ言えれば
  `Q'' = π(Q ∩ U)` は自動 (一意性)。この線で攻めるのが筋。

## 2026-08-02 (105): 🔍 §4 段 (2) の残りを実測 — `U` 側の `Setup` が本体

`exists_conjugate_t_eq` (Ch. I Prop 2(b) + `conjugate`) を landing
(⟹ (104) の手順 1-3 完了)。そのうえで**残りが何か**を全数調査した。

### 調査結果 (subagent、全て自分で file:line を再確認済)

| 問 | 実測 |
|---|---|
| `RankOneBNPair.Setup` の構成は repo に何個あるか | **1 個だけ**: `RankOneSetup.lean:79` の `hyp.rankOneSetup` (full `Hypothesis` について)。`↥U` / `↥C` 版は無い |
| `H ∩ K = (Q ∩ K)(D ∩ K)` 型の積分解 | **`K = C_G(X)` について在る**: `FixedPointCentralizer.lean:282` の `cQ_mul_cD_eq_cH`。⚠ `K = U` (residual) 版は無い |
| `hyp.Q` が 2-群か | **無条件では未証明**。`InductionHypothesis.lean:37` が `hΩ : ∃ n, \|Ω\| − 1 = 2ⁿ` 条件付きで与えるのみ。他は全部仮説 |
| `C_G(X)` に (A1) 相当の構造があるか | **在る**: `CentralizerInduction.lean:246` の `centralizerHypothesisA1` (`HypothesisA1`, `:75`)。`Hypothesis` から `faithful` と `two_rank_ge_two` を抜いた 15 フィールド |
| `O^{2'}(G) ⊓ K` 型の補題 | **無い** (`PrimeComplementResidual.lean` 全 150 行を確認; Dedekind 系は `Mathlib/Subgroup.lean:724` 等にあるが residual とは無関係) |
| `hyp.Q ⊓ U`, `hyp.D ⊓ U`, `hyp.H ⊓ U` | 名前付き補題は**無し**。`C_Q(P) ≤ U` だけ `StructureOfH/PSUCentre.lean:75` に局所 `have` として在る (`residual_eq_normalClosure` から) |

### 🔑 構造の理解 (ここが今回の収穫)

* **`IsFGH.eq_of_le` は小さい方の `Setup` を要求しない** — `IsFGH` だけでよい。
  ただし `M' Q' D'` は**同じ ambient `L` の部分群**で `f₁ g₁ h₁ : L → L`。
* ⟹ §4 が要るのは「ambient の三つ組が `(H∩U, Q∩U, D∩U, t)` についても `IsFGH`
  である」こと。すなわち **`x ∈ (Q∩U)^#` に対し `f(x), g(x) ∈ Q∩U` かつ
  `h(x) ∈ D∩U`**。
* `C = C_G(P)` までは行ける: `txt ∈ C` の canonical 分解は ambient の一意性より
  `C` 内の分解と一致するので `f(x), g(x) ∈ Q∩C`、`h(x) ∈ D∩C`。
  さらに `Q ∩ C = C_Q(P) ≤ U` (`residual_eq_normalClosure`) ⟹ **`f(x), g(x) ∈ U` は出る**。
* ⚠ **`h(x) ∈ U` は出ない**: `C/U` は奇位数 (2'-群) で `D∩C` も奇位数なので
  `D ∩ C ⊄ U` が普通。ここが段 (2) の**本当の残り**。

### ⚠ 次セッションはここから (優先順)

1. **`HypothesisA1.rankOneSetup` の一般化** — `rankOneSetup` の証明 (`RankOneSetup.lean:79`)
   は `faithful` / `two_rank_ge_two` を**一切使わない** (使うのは `Q_le_H`, `D_def`,
   `t_sq`, `t_conj_mem_D`, `Q_normal_in_H`, `existsUnique_Q_mul_D`,
   `existsUnique_canonicalForm`, `t_not_mem_H`, `mem_D_iff`, `t_inv_eq`,
   `Q_inf_D_eq_bot`)。⚠ ただし `existsUnique_Q_mul_D` / `existsUnique_canonicalForm`
   (`CanonicalForm.lean:123`) 自体が `Hypothesis` について述べてあるので、
   **それらの一般化が要るかを先に実測すること** (`exists_canonicalForm` が
   2-推移性以外を使っていないか)。
   ⟹ 通れば `C_G(P)` に `Setup` と `f,g,h` が付き、`IsFGH.eq_of_le` で
   ambient と繋がる。
2. `h(x) ∈ U` の扱い — 3 案:
   (a) `D ∩ U` でなく `D ∩ C` を `D'` に取る (= `C` 用の setup で止める) が、
       その場合 `π : ↥C → ?` の行き先が `U/Z(U)` にならない;
   (b) `h(x)` の `U`-成分だけ取り出す (書籍の誤差項 `η ∈ P` はまさにこれの可能性);
   (c) 書籍 p.133 を**ページ画像で読み直す** — `h₁(ω) ∈ ζ₁³(P ∩ U)` の `P ∩ U` が
       ちょうどこの `D`-side の誤差なら、(b) が書籍の言っていること。
   ⟹ **まず (c) を実行する** (`references/peterfalvi/pages/` に p.133 を残す)。

## 2026-08-02 (106): 📖 p.133 再読 + `fgh_mem_centralizer` landing ⟹ 経路が完全に決まった

### 書籍 p.133 の該当段落 (ページ画像 `references/peterfalvi/pages/peterfalvi-p133.png` で確認)

> Let `ζ₁ ∈ (V ∩ U) − (P ∩ U)` and `ζ ∈ C_W(P)` be such that `ζ₁ ∈ ζP`.
> If `f₁` and `h₁` denote the mappings `f` and `h` relative to `U`, `U ∩ H` and `t`,
> then, by Corollary 2 of the proposition of §3, there is an element `ω ∈ (Q − Q₀) ∩ U`
> such that `f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)` and `h₁(ω) ∈ ζ₁³(P ∩ U)`. **By the uniqueness of
> the canonical form of an element of `G − H`, `f(ω) = f₁(ω) = ω^{-ζ₁} = ω^{-ζ}` and
> `h(ω) = h₁(ω) ∈ ζ³P`.**

⚠ 重要な読み: **`f` には誤差項が付かない**。`f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)` の剰余元は
`f₁(ω)` と `ω^{-ζ₁}` が**どちらも `Q` の元**である一方 `P ∩ U` は奇位数で
`Q ⊓ P = 1` なので**強制的に 1**。だから `f(ω) = ω^{-ζ₁}`。さらに `ω ∈ U ⊆ C_G(P)`
ゆえ `P` が `ω` を中心化し `ζ₁ ∈ ζP` から `ω^{-ζ₁} = ω^{-ζ}`。
誤差 `∈ ζ³P` が残るのは **`h` だけ**。

⟹ (105) の「`h(x) ∈ U` が出ない」は**問い方が間違っていた**。書籍は `U` **自身の**
三つ組 `f₁, g₁, h₁` を使い、`h₁(ω) ∈ D ∩ U` は `U` の `IsFGH` の定義に含まれる。
必要なのは **`U` の `Setup`** であって「ambient の `h` が `U` に入るか」ではない。

### 🔑 `U` の `Setup` は出る (今回の `fgh_mem_centralizer` の論法を一般化するだけ)

`fgh_mem_centralizer` (今回 landing) の核は「`P` による共役が canonical 分解を保つ
⟹ 分解の因子が `C_G(P)` に入る」。これを `t x t` でなく**任意の `y ∈ C − H`** に
適用すると:

* `fact`: `y ∈ U` を `y = x·t·q` (`x ∈ H`, `q ∈ Q`) と書くと `q ∈ C_Q(P)`、
  そして **`C_Q(P) ≤ U`** (`residual_eq_normalClosure`: `U = normalClosure(C_Q)`)。
  ⟹ `x = y·q⁻¹·t⁻¹ ∈ U` (`t ∈ U` は landing 済)。**両因子が `U` に入る**。
* `split`: `a ∈ H ∩ U` を `a = q·d` と書くと同様に `q ∈ C_Q(P) ≤ U`、
  ⟹ `d = q⁻¹·a ∈ U`。**`h₁(ω) ∈ D ∩ U` はこれで出る**。
* `tconj` は ambient から自明に降りる。

⟹ **割り算するだけ**で `U` 側の `Setup` が閉じる。新しい数学は要らない。

### ⚠ 次セッションはここから

1. **`Setup.restrict`** (`OddOrder/GroupTheory/RankOneBNPair.lean` に一般補題):
   `Setup M Q D t` と `t ∈ K` と「canonical / QD 分解の `Q`-成分が `K` に入る」
   2 条件から `Setup (M.subgroupOf K) (Q.subgroupOf K) (D.subgroupOf K) ⟨t, htK⟩`。
   (他の因子は割り算で出るので吸収条件は `Q`-成分だけでよい。)
2. §4 側でその 2 条件を `C_Q(P) ≤ U` から供給する
   (`fgh_mem_centralizer` の共役論法を `y ∈ C − H` 一般に切り出す)。
3. `Setup.exists_fgh` ⟹ `U` の `f₁,g₁,h₁`。`IsFGH.map` で `U/Z(U)` へ、
   `IsFGH.eq_of_le` で ambient へ。⟹ **段 (2) 完了**。

### (106) 続き: `Setup.restrict` landing

`RankOneBNPair.lean` に一般補題を追加 (手順 1 完了)。⚠ 吸収条件は結局
**`Q`-成分だけ**でよい形に絞れた (もう一方は `d = q⁻¹a`, `x = y q⁻¹ t⁻¹` と
割り算で出る)。残り = 手順 2 (吸収条件を `C_Q(P) ≤ U` から供給) と手順 3。

⚠ 手順 2 の材料はもう在る: `fgh_mem_centralizer` (今回) の共役論法
(「`p ∈ X` が `y` を中心化 ⟹ canonical 分解が `p`-不変 ⟹ 因子が `C_G(X)` に入る」)
を `y = t x t` でなく **任意の `y ∈ C_G(P) − H`** について切り出せばよい。
`C_Q(P) ≤ U` は `CentralizerCommonData.residual_eq_normalClosure` から
(`StructureOfH/PSUCentre.lean:75` に局所 `have` の実例)。

## 2026-08-02 (107): 🎯 `U` の rank-one setup が landing — 段 (2) の部品が全部そろった

(106) の手順 1-2 完了。**新しい数学は一切要らず**、既存の一意性 2 本の組み合わせだった。

| 定理 | 内容 |
|---|---|
| `Setup.restrict` (`RankOneBNPair.lean`) | `t ∈ K` かつ 2 分解の **`Q`-成分が `K` に入る** なら `K` は setup を継承 (他の因子は `d = q⁻¹a`, `x = y q⁻¹ t⁻¹` と割り算で出る) |
| `mem_centralizer_of_conj_eq` | 「全 `p ∈ X` で `p y p⁻¹ = y`」⟹ `y ∈ C_G(X)` |
| `canonicalForm_mem_centralizer` | `y ∈ C_G(X)` の canonical 分解 `y = x·t·q` は両因子が `C_G(X)` に入る (Ch. I Prop 4(a) の一意性) |
| `splitQD_mem_centralizer` | `a ∈ C_H(X)` の `Q·D` 分解も同様 (Ch. I Prop 6(a) + `Q·D` 一意性) |
| `fgh_mem_centralizer` | 上 2 本の系に書き直し (証明 6 行) |
| `rankOneSetup_subgroup` | `C_Q(X) ≤ K ≤ C_G(X)`, `t ∈ K` ⟹ `K` は setup を持つ |
| `inf_centralizer_le_residual` | `C_Q(X)` が 2-群 ⟹ `C_Q(X) ≤ O^{2'}(C_G(X))` |
| `t_mem_residual` | `t ∈ O^{2'}(C_G(X))` (§4 固有だった補題の一般化) |
| **`rankOneSetup_residual`** | ⟹ **`U = O^{2'}(C_G(X))` が rank-one setup を持つ** |

⟹ `Setup.exists_fgh` が書籍の **`f₁, g₁, h₁`** を与える。

### ⚠ 残る 1 点: 商 `U/Z(U)` 側の `H̄` / `Q̄` と `π(H ∩ U)` / `π(Q ∩ U)` の同定

`IsFGH.map` は下の setup について `hQπ : π(Q ∩ U) ⊆ Q̄`, `hDπ : π(D ∩ U) ⊆ D̄` を要求する。
`t̄ = π t` は `exists_conjugate_t_eq` (104) で合わせられるが、**`H̄` が
`π(H ∩ U)` と一致するかは base point の取り方次第**。

⚠ `Hypothesis` は `(basept, t)` で決まる (`H = stab(basept)`, `D = H ⊓ H^t`,
`Q = H` の正規 Hall 2-部分群で一意) ので、制約は 2 本 (`t̄ = π t` と `H̄ = π(H∩U)`)、
共役の自由度は 1 パラメータ。**両立するか**が次の問い。

見通し: `π(C_Q(P))` は `U/Z(U)` の 2-部分群、`Q̄` は Sylow 2。もし
`π(C_Q(P))` が Sylow 2 なら `Q̄` の共役で、あとは「(Sylow 2, `H` の外の対合) の対に
群が推移的に働く」= 2-推移性の帰結、で両立が言えるはず。

### ⚠ 次セッションはここから

1. `π(Q ∩ U)` が `U/Z(U)` の Sylow 2-部分群か実測 (`|C_Q(P)|` と `|U/Z(U)|₂` の比較;
   `natCard_residualQuotientHypothesis_Q0`/`_Q` と `CentralizerPSUData` の
   `natCard_cQ_eq_baseField_cube` が使えるはず)。
2. 「(Sylow 2, 外の対合) の対の共役性」を `Hypothesis` の公理から示す
   (`isConj_of_involutions` (Ch. I Prop 2(b)) と `Sylow.conj` の合成)。
3. ⟹ 共役でひねった `Hypothesis` で `t̄ = π t` かつ `Q̄ = π(Q∩U)` を同時に達成 ⟹
   `IsFGH.map` → `corollaryTwo_of_sectionThree` → `IsFGH.eq_of_le` ⟹ **段 (2) 完了**。

## 2026-08-02 (108): `Setup.quotient` — 商への降下も landing

`Setup.restrict` (部分群へ) の対。`N ⊴ L`, `N ≤ D` なら
`Setup (M.map π) (Q.map π) (D.map π) (π t)`。要点は「`N` が `Q`-成分を乱さない」:

* `split` — 2 つの持ち上げは `n ∈ N ≤ D` だけずれ、`D`-成分に吸収される。
* `fact` — `a' t b' n = a'(t n t)·t·(n⁻¹ b' n)` とずらすと `t n t ∈ N` が `M`-成分へ、
  `Q`-成分は `n` 共役になるので、どちらも商では見えない。

書籍 p.133 は `U → U/Z(U)` でこれを使う (核 `Z(U) = P ∩ U ≤ P ≤ V ≤ D`、
`Z(U) ⊆ P` は §4 段 (1) の `eq_P_of_centralizes`)。

⚠ 実測メモ (次回の時間節約用):
* **`QuotientGroup.mk'_eq_mk'` は現 pin に存在しない** — `QuotientGroup.eq`
  (`↑x = ↑y ↔ x⁻¹ * y ∈ N`) を使うこと。
* `ȳ` のような合成文字 (combining macron) は Lean の識別子に使えず parse error。
* `∃!` を `refine ⟨…, ?_, ?_⟩` で埋めると残る goal が **beta-redex** なので、
  `rw` の前に `change` で開く。
* 部分型の第 1 成分を `rw [h]` で書き換えると membership 証明が `h` に依存して
  **motive not type correct** — `congrArg (mk' N) h` を直接渡す。

### 段 (2) の在庫 (これで道具は全部そろった)

| 段 | 道具 | 状態 |
|---|---|---|
| ambient → `U` | `rankOneSetup_residual` + `Setup.exists_fgh` | ✅ (107) |
| `U` → `U/Z(U)` | `Setup.quotient` + `IsFGH.map` | ✅ 今回 |
| `U/Z(U)` で Cor 2 | `corollaryTwo_of_sectionThree` + `isStandardModel_residualQuotient` | ✅ (102)(103) |
| `U` → ambient | `IsFGH.eq_of_le` | ✅ (54) |
| `t̄` を `π t` に合わせる | `exists_conjugate_t_eq` | ✅ (104) |
| **降下 setup ≡ transported Hypothesis の setup** | ⚠ **未** | ← 残り |

### ⚠ 次セッションはここから

最後の同定。`Hypothesis` は `(basept, t)` で決まるので、示すべきは
**`π(Q ∩ U)` が `U/Z(U)` の Sylow 2-部分群**であること (⟹ `π(M_U) = N(π(Q∩U))` が
点安定化群 ⟹ 共役で `t̄ = π t` と同時に合わせられる)。

材料: `CentralizerPSUData.natCard_cQ_eq_baseField_cube`
(`|C_Q(P)| = |BaseField n|³`) と `natCard_residualQuotientHypothesis_Q`/`_Q0`
(`|Q̄| = |Q̄₀|³ = 2^{3n}`)。⟹ 位数が一致するので `π|_{Q∩U}` が単射
(`Q ⊓ Z(U) ≤ Q ⊓ D = 1`) なら `|π(Q∩U)| = |Q̄|`。

## 2026-08-02 (109): `setup_residualQuotient` landing + 🔍 最後の同定の 3 経路を評価

`setup_residualQuotient` = `rankOneSetup_residual` (107) + `Setup.quotient` (108)。
`residualImage` (= `O^{2'}(C_G(X))` の `G` 内の像) を abbrev 化。
⟹ **`U/Z(U)` は降下 setup を持つ** (核 `Z(U) ⊆ P ≤ V ≤ D` は §4 段 (1))。

### 何が残っているかの正確な定式化

`IsFGH.eq_of_le` は **同じ `t`** を、`IsFGH.map` は下の setup を要求する。よって
「降下 setup の三つ組」と「transported `hyp'` の三つ組」を結ぶには、`U/Z(U)` の中で

  **`Q̄_desc = hyp'.Q` かつ `t̄_desc (= π t) = hyp'.t`**

を同時に達成する必要がある。`Hypothesis.conjugate` の自由度は 1 パラメータで
制約は 2 本なので、自明ではない。

⚠ 既に在るもの: `normalizer_Q_eq_H` (`Basic.lean:610`, **`N_G(Q) = H`**) —
これで `Q̄` を決めれば `H̄` は自動。Sylow 2 ↔ 点 の対応も `|Ω| = |Q|+1` と
`n_2 = |G:N(Q)| = |G:H| = |Ω|` から出る。

### 3 経路の評価

| 経路 | 内容 | 要る新定理 |
|---|---|---|
| **A 整合** | `hyp'` を共役して `Q̄ = π(Q∩U)` と `t̄ = π t` を同時達成 | 「`H` は `H` の外の対合に推移的」— 未証明、数え上げが必要 (`|D| = \|K\|\|V\|` 等) |
| **B 内在** | 降下 setup から `U/Z(U)` 自身の `Hypothesis` を作る | `Setup ⟹ Hypothesis` (2-推移性は `coordsEquiv`/`permHom` で在る; あとは faithful = `M̄.normalCore = ⊥`, `Q̄` even, `D̄` odd, 2-rank≥2)。**その後 §2/§3 の数値仮説を内在版で再取得**が要る |
| **C 移送** | 2 つの setup を結ぶ `U/Z(U)` の自己同型を作り `ofMulEquiv` で `Hypothesis` を移す | `mulEquivOfPermMatch` (`RankOneBNPairRigidity.lean`) が素材。ただし `f` の一致が要る |

⟹ **次は B の各部品のコストを実測する** (2-推移性の梱包が既に在るかを
`RankOneBNPair.lean` の `coords_smul_*` から確認し、faithful を `permHom_ker`
(`= M.normalCore`) 経由で見る)。B が通れば A の数え上げは不要になる。

⚠ `permHom_ker (hS) : (permHom hS).ker = M.normalCore` と
`permHom_injective (hS) (hcore : M.normalCore = ⊥)` は既に在る
(`RankOneBNPairRigidity.lean:148,160`)。

## 2026-08-02 (110): 🔑 最後の同定 — **経路 A が閉じることが分かった** (3 段の共役)

(109) で「経路 A は `H` が外の対合に推移的であることを要し未証明」と書いたが、
**もっと素直に閉じる**。`U/Z(U)` の中で降下 setup `(M̄, Q̄, D̄, π t)` と transported
`hyp'` の `(H', Q', D', t')` を、**3 段階の共役**で順に合わせればよい:

1. **`Q` を合わせる** — `π(Q∩U)` が Sylow 2 なら Sylow 共役で `Q̄ = Q'`。
   このとき `M̄ = N(Q̄) = N(Q') = H'` も自動 (**`normalizer_Q_eq_H`**, `Basic.lean:610`;
   setup 版も同じ論法で出る)。
2. **`D` を合わせる** — `Q̄` と `M̄` が一致した時点で `D̄`, `D'` はどちらも
   `M̄ = Q̄ ⋊ ?` の補群。位数が互いに素 (`Q` even / `D` odd) なので
   **Schur–Zassenhaus の共役性**で `u ∈ Q̄` により `D̄^u = D'`。⚠ `u ∈ Q̄` は
   `Q̄` と `M̄` を保つので段 1 を壊さない。
3. **`t` を合わせる** — ここが (109) で詰まっていた所。段 1-2 の後:
   * `D = M ⊓ M^t` (**今回 landing した `Setup.D_eq_inf_map_conj`**) が両方に成り立つので
     `M^{π t} = M^{t'}` ⟹ `t' (π t)⁻¹ ∈ N(M) = M` (`normalizer_H_eq_H`)。
     さらに 2 点安定化群が一致するので `π t = d · t'` なる **`d ∈ D`** が取れる。
   * `π t` も `t'` も**対合**なので `(d t')² = d · (t' d t') = d · d^{t'} = 1`、
     すなわち **`d ∈ K`** (`KSet = {x ∈ D : x^t = x⁻¹}`)。
   * 一方 `e ∈ D` による共役は `t'` を `e⁻¹ t' e = (e⁻¹ e^{t'}) t'` に送るので、
     達成できる `d` の範囲は写像 **`e ↦ e⁻¹ e^{t'}`** の像。像は `K` に含まれ、
     ファイバーは `V = C_D(t')` の剰余類なので**像の位数 = `|D|/|V|`**。
   * ⟹ **`|K| = |D|/|V|`**、すなわち **`D = K V`** (`V = W` の分岐では
     `exists_mem_K_mem_W_mul` が既に与える形) が言えれば写像は `K` へ**全射**、
     よって `e ∈ D` で `t` を合わせられる。⚠ 段 1-2 は `e ∈ D ≤ M̄` が
     `Q̄`(正規) と `M̄` を保つので壊れない。

⟹ 未証明の核は **`|K| = |D|/|V|` (= `D = K V`)** 1 本に落ちた。
`h_mem_W` (`PSU3StepEighteen.lean:200`) が `hyp.exists_mem_K_mem_W_mul hVW` で
`D = K W` の分解を実際に使っているので、**素材は在る**。

### ⚠ 次セッションはここから

1. `exists_mem_K_mem_W_mul` の正確な形と `K ⊓ W = 1` の有無を実測
   (⟹ `|D| = |K||V|`)。
2. `e ↦ e⁻¹ e^{t}` が `D → K` へ全射であることを (1) から示す
   (ファイバー = `V`-剰余類、像 ⊆ `K`、位数勘定)。
3. 段 1 の `π(Q∩U)` が Sylow 2 (位数 `|C_Q(P)| = ℓ³`) を
   `natCard_cQ_eq_baseField_cube` と `natCard_residualQuotientHypothesis_Q` で示す。
4. 段 1-3 を合成 ⟹ `Hypothesis.conjugate` で三つ組が完全に一致 ⟹
   `IsFGH.map` + `corollaryTwo_of_sectionThree` + `IsFGH.eq_of_le` ⟹ **段 (2) 完了**。

## 2026-08-02 (111): 段 3 の核が landing — **数え上げは要らなかった**

`exists_mem_K_conj_t_eq` : `d ∈ K` ⟹ `∃ e ∈ K, e⁻¹ t e = d t`。

(110) で「核は `|K| = |D|/|V|` (= `D = K V`) 1 本」と書いたが、**それは不要**だった。
`e ∈ K` による共役は `e⁻¹ t e = e⁻² t` (K の定義 `t e t = e⁻¹` から直接) なので、
必要なのは「**平方が `K` 上全射**」だけ。`K ≤ D` は奇位数の部分群なので
各元は自分の冪の平方 ⟹ 自明。

⚠ しかも `exists_sq_eq_of_mem_K` は **`PSU3Preliminary.lean:749` に既にあった**
(重複を書いて "already been declared" で気付いた)。着手前 grep の教訓
= [[grep-concept-names-not-book-notation]] の再確認。

### 段 (2) の残り (更新)

| 段 | 内容 | 状態 |
|---|---|---|
| 1 | `π(Q∩U)` が Sylow 2 ⟹ Sylow 共役で `Q̄ = Q'`、`M̄ = N(Q̄) = H'` | ⚠ 未 (位数計算) |
| 2 | Schur–Zassenhaus の共役性で `u ∈ Q̄` により `D̄ = D'` | ⚠ 未 |
| 3 | `π t = d t'` (`d ∈ K`) を `e ∈ K` 共役で吸収 | ✅ **今回** |
| 4 | 合成 ⟹ `IsFGH.map` + `corollaryTwo_of_sectionThree` + `IsFGH.eq_of_le` | ⚠ 未 |

⚠ 段 3 の前段 (「`π t` と `t'` は `D` の元だけ違い、対合性から差は `K` に入る」) は
`Setup.D_eq_inf_map_conj` (110) と `normalizer_H_eq_H` から出る — これも未 landing。

### ⚠ 次セッションはここから

1. **段 3 の前段**: `M ⊓ M^{t₁} = M ⊓ M^{t₂} = D` かつ `t₁, t₂ ∉ M` 対合 ⟹
   `t₁ = d t₂` なる `d ∈ D`、さらに対合性から `d ∈ KSet`。
   (`normalizer_H_eq_H` (`Basic.lean:628`) + `D_eq_inf_map_conj`。)
2. 段 1 の位数計算 (`natCard_cQ_eq_baseField_cube` と
   `natCard_residualQuotientHypothesis_Q`)。
3. 段 2 の Schur–Zassenhaus 共役性 (mathlib の `IsComplement`/`SchurZassenhaus` を実測)。

## 2026-08-02 (112): 経路 B に舵を切った — `Setup` から 2-推移性が出る

(110)(111) の経路 A (共役で三つ組を合わせる) は段 3 が landing したが、段 1-2
(Sylow 共役 + Schur–Zassenhaus) と「`π t` と `t'` の差が `K` に入る」前段が残る。
一方 **経路 B (降下 setup から `U/Z(U)` 自身の `Hypothesis` を作る)** の主要部品が
安く出ることが分かったので、そちらへ切り替える。

* `Setup.exists_mem_M_smul_eq` — `M` は `L ⧸ M` の基点以外に推移的。
  `coords_smul_some_of_mem_M` が `Q` の作用を「`Q` 上の右移動」として読むので
  `b⁻¹a` を取るだけ (**新しい数学ゼロ**)。
* `Setup.isMultiplyPretransitive_two` — ⟹ **`L` は `L ⧸ M` に 2-重推移的**。

⟹ `Hypothesis.rankOneSetup` の逆向き (`Setup ⟹ Hypothesis`) の (A1) 部分が完了。

### `Setup ⟹ Hypothesis` の残りフィールド (全部安い見込み)

| フィールド | 出どころ |
|---|---|
| `basept` / `doubly_transitive` | `(1 : L ⧸ M)` / **今回** |
| `H_def` | `MulAction.stabilizer_quotient` (`stabilizer L ↑1 = M`) |
| `D_def` | **`Setup.D_eq_inf_map_conj`** (110) |
| `Q_le_H` / `Q_inf_D_eq_bot` / `Q_mul_D_eq_H` | `QM` / `split` の一意性 / `split` |
| `Q_normal_in_H` | `DQ` (`d⁻¹`版) + `Q` 内共役 |
| `t_sq` / `t_not_mem_H` | `invol` / `tnotmem` |
| `t_ne_one` | `tnotmem` + `1 ∈ M` |
| `faithful` | ⚠ 仮説 (`M.normalCore = ⊥`; `permHom_ker` 経由) |
| `Q_even` / `D_odd` / `two_rank_ge_two` | ⚠ 仮説 |

### ⚠ 次セッションはここから

1. **`Setup.toHypothesis`** を書く (上表; 仮説は faithful / Q even / D odd / 2-rank)。
2. `U/Z(U)` の降下 setup にそれを当てる — 各仮説の供給:
   * `Q̄` even: `π(Q∩U) ≅ C_Q(P)` が非自明 2-群 (`cQ_isPGroup`)。
   * `D̄` odd: `D∩U` の商で `D_odd` から。
   * 2-rank: §4 の `hA3`。
   * faithful: `M̄.normalCore = ⊥` — ⚠ ここだけ要調査
     (`normalCore_subgroupOf_normalClosure_cQ_eq_center` が近い形)。
3. そのうえで §2/§3 の数値仮説を内在版で供給
   (`|Q̄| = |C_Q(P)| = ℓ³` は `natCard_cQ_eq_baseField_cube`、
   `|Q̄₀| = ℓ` は `natCard_cQ0_eq_baseField`、Suzuki 2-群性は `cQ_isSuzuki2Group`)。

## 2026-08-02 (113): 🎯 `Hypothesis.ofRankOneSetup` — 経路 B の主定理が landing

`rankOneSetup` の**逆**: `Setup M Q D t` + (`M.normalCore = ⊥` / `|Q|` even /
`|D|` odd / (A3)) ⟹ `Hypothesis L (L ⧸ M)`。

2-推移性は (112) の `Setup.isMultiplyPretransitive_two` がそのまま与え、
残りは全部 `Setup` のフィールドから出た:

| フィールド | 出どころ |
|---|---|
| `H_def` | `MulAction.stabilizer_quotient` |
| `D_def` | `Setup.D_eq_inf_map_conj` (110) |
| `Q_normal_in_H` | `split` + `DQ` (`d⁻¹` 版) |
| `Q_inf_D_eq_bot` | `split` の一意性 (`x·1` と `1·x` の 2 通り) |
| `Q_mul_D_eq_H` | `split` |
| `faithful` | `Subgroup.normalCore_eq_ker` + 仮説 |

⟹ **経路 A (transported `hyp'` との三つ組照合) は不要になった**。
`U/Z(U)` は `setup_residualQuotient` (109) から**自前の** `Hypothesis` を持つ。

⚠ 実測メモ (2 回目、記憶に残すこと): `∃!` を `obtain ⟨-, -, huniq⟩` で受けると
**証人を `-` で捨てるため `huniq` ごと消える** (`huniq` の型が証人に依存)。
証人には必ず名前を付ける。

### ⚠ 次セッションはここから — `ofRankOneSetup` を `U/Z(U)` に当てる

供給すべき 4 仮説:

| 仮説 | 見込み |
|---|---|
| `\|Q̄\|` even | `π(Q∩U) ≅ C_Q(P)` が非自明 2-群 (`cQ_isPGroup` + `C_Q(P) ≠ 1`) |
| `\|D̄\|` odd | `D∩U` の商、`D_odd` から (商の位数は約数) |
| (A3) | §4 の `hA3` を `U/Z(U)` へ (⚠ 像が位数 4 の初等可換のままか要確認) |
| `M̄.normalCore = ⊥` | ⚠ **要調査**。`normalCore_subgroupOf_normalClosure_cQ_eq_center` (`CentralizerResidual.lean:72`) が近い形 — `U/Z(U)` の忠実性はまさに `Z(U)` で割った理由なので出るはず |

そのうえで §2/§3 の数値仮説を内在版で供給:
`\|Q̄\| = \|C_Q(P)\| = ℓ³` (`natCard_cQ_eq_baseField_cube`)、
`\|Q̄₀\| = ℓ` (`natCard_cQ0_eq_baseField`)、Suzuki 2-群性 (`cQ_isSuzuki2Group`)。
⚠ `Q̄₀` は内在 `Hypothesis` から導かれる量なので、`π(Q₀∩U)` と一致するかを先に確認する。

## 2026-08-02 (114): 忠実性の核 `Setup.normalCore_le_center` が landing

(113) の `ofRankOneSetup` が要求する 4 仮説のうち、唯一「要調査」だった
`M.normalCore = ⊥` の実質が出た:

**`Setup.normalCore_le_center`** — `⟨Q ∪ Q^t⟩ = ⊤` (= `L` が `Q` の共役で生成)
ならば `M.normalCore ≤ Z(L)`。

論法 (新しい数学ゼロ、既存の一意性の組み合わせ):
* `N := M.normalCore` は `t` 共役で安定 ⟹ `N ≤ M ⊓ M^t = D` (`D_eq_inf_map_conj`)。
* `[N, Q] ≤ N ⊓ Q ≤ D ⊓ Q = 1` (`Q_inf_D_eq_bot`、今回切り出した) ⟹ `N` が `Q` を中心化。
* `t` 共役で `Q^t` も中心化 ⟹ `⟨Q ∪ Q^t⟩ = L` 全体を中心化。

⟹ **`U/Z(U)` で中心が自明になる理由がそのまま忠実性になる** (中心で割ったから)。

⚠ 実測メモ: `hS.DQ d hd q hq : d⁻¹ * q * d ∈ Q` — 欲しい形が `n⁻¹ q⁻¹ n` なら
`d := n` を渡す。`t` 共役の calc は `group` が `t*t = 1` を知らないので
`hconj : (t a t)(t b t) = t (a b) t` を先に用意する。

### `ofRankOneSetup` を `U/Z(U)` に当てる — 残り

| 仮説 | 状態 |
|---|---|
| `M̄.normalCore = ⊥` | **今回で道具完成**。あとは (a) `⟨Q̄ ∪ Q̄^t̄⟩ = ⊤` (= `U/Z(U)` が `π(Q∩U)` の共役で生成) と (b) `Z(U/Z(U)) = ⊥` を供給 |
| `\|Q̄\|` even | `π(Q∩U) ≅ C_Q(P)` が非自明 2-群 |
| `\|D̄\|` odd | `D∩U` の商 |
| (A3) | §4 の `hA3` |

⚠ (a) は `Setup.closure_conj_Q` + 「`U = O^{2'}(U)`」から:
`⟨Q_U^x : x ∈ U⟩ = primeComplementResidual 2 U` (`RankOneBNPairRigidity.lean:217`)
で、`O^{2'}` の冪等性 (`C/U` と `U/O^{2'}(U)` がともに奇位数 ⟹ `C/O^{2'}(U)` も奇
⟹ `U = O^{2'}(C) ≤ O^{2'}(U)`) から `= U` (商では `⊤`)。
⚠ (b) `Z(U/Z(U)) = ⊥` は一般には偽 (`U` が冪零なら偽) だが、ここでは
`U/Z(U) ≅ PSU(3,ℓ)` が中心を持たないことから出る — **`residualQuotientEquiv` を
使ってよい** (三つ組の照合とは違い、中心の自明性は同型不変)。

### ⚠ 次セッションはここから

1. `O^{2'}` の冪等性 (⟹ (a))。
2. `Z(U/Z(U)) = ⊥` を `residualQuotientEquiv` + 標準 `PSU(3,ℓ)` の中心自明性から
   (`ProjectiveUnitary` 側に中心の計算が在るか実測)。
3. ⟹ `ofRankOneSetup` を当てて `U/Z(U)` の内在 `Hypothesis` を得る。

## 2026-08-02 (115): `O^{p'}` の冪等性 — 生成条件の核

`Subgroup.primeComplementResidual_self_eq_top` : `O^{p'}(O^{p'}(G)) = ⊤`。

⚠ (114) では「位数計算 (`|C:U|` が奇 等) が要る」と見積もったが**不要**だった:
`G` の Sylow `p` はすべて `U = O^{p'}(G)` に入るので、`U` の中でも Sylow `p` に
含まれ、したがって `O^{p'}(U)` に入る。⟹ 像が `U` 全体 ⟹ `map` の単射性で `⊤`。

⟹ `Setup.normalCore_le_center` (114) の仮説「`⟨Q ∪ Q^t⟩ = ⊤`」が、
`closure_conj_Q` + `closure_iUnion_conj_eq_primeComplementResidual`
(`RankOneBNPairRigidity.lean:217`) と併せて `U` について供給できる
(`Q_U = C_Q(P)` が `↥U` の Sylow 2 であることが前提)。

### 段 (2) の在庫 (更新)

| 必要物 | 状態 |
|---|---|
| `U` の Setup | ✅ (107) |
| `U/Z(U)` の降下 Setup | ✅ (109) |
| `Setup ⟹ Hypothesis` | ✅ (113) |
| 忠実性の核 (`normalCore ≤ Z`) | ✅ (114) |
| 生成条件 (`⟨Q ∪ Q^t⟩ = ⊤`) の核 | ✅ **今回** |
| `Q_U = C_Q(P)` が `↥U` の Sylow 2 | ⚠ 未 (`exists_sylow_two_eq_cQ_of_isPGroup` が `↥C` 版で在る — `↥U` へ移す) |
| `Z(U/Z(U)) = ⊥` | ⚠ 未 (中心の自明性は同型不変なので `residualQuotientEquiv` 経由でよい) |
| `\|Q̄\|` even / `\|D̄\|` odd / (A3) | ⚠ 未 (どれも既存の材料から) |

### ⚠ 次セッションはここから

1. `C_Q(P)` が `↥U` の Sylow 2 — `exists_sylow_two_eq_cQ_of_isPGroup`
   (`CentralizerResidual.lean:269`) は `↥C` の Sylow として与える。`C_Q ≤ U` なので
   `↥U` の Sylow でもある (位数が同じ) — `Sylow.subtype` 系の補題を実測。
2. `Z(U/Z(U)) = ⊥` — 標準 `PSU(3,ℓ)` の中心自明性を `ProjectiveUnitary` 側で実測
   (`PSUCentre.lean` が在る)。
3. ⟹ `ofRankOneSetup` を当てる。

## 2026-08-02 (116): 忠実性が仮説 3 本に還元 — `Setup.normalCore_eq_bot`

`ofRankOneSetup` の `M.normalCore = ⊥` を、**`Q` が Sylow `p`** /
**`O^{p'}(L) = ⊤`** / **`Z(L) = ⊥`** の 3 条件に還元:

* `Setup.closure_Q_union_conj_eq_top` — 前 2 条件 ⟹ `⟨Q ∪ Q^t⟩ = ⊤`
  (`closure_conj_Q` + `closure_iUnion_conj_eq_primeComplementResidual`)。
* `Setup.normalCore_eq_bot` — それを `normalCore_le_center` (114) に食わせ、
  第 3 条件で `⊥`。

### `ofRankOneSetup` を `U/Z(U)` に当てるための供給表 (これが残り全部)

| 供給物 | 見込み / 材料 |
|---|---|
| `Q̄ = π(C_Q(P))` が `U/Z(U)` の Sylow 2 | `C_Q(P)` が `↥C` の Sylow 2 (`exists_sylow_two_eq_cQ_of_isPGroup`) ⟹ `Sylow.subtype` で `↥U` の Sylow 2 ⟹ `π` の像 (核 `Z(U)` は奇位数なので Sylow を保つ) |
| `O^{2'}(U/Z(U)) = ⊤` | `primeComplementResidual_map_of_surjective` + `O^{2'}(U) = ⊤` (115) |
| `Z(U/Z(U)) = ⊥` | ⚠ 要調査。`PSUCentre.lean` に標準 `PSU(3,ℓ)` の中心の計算が在るか実測 (中心の自明性は同型不変なので `residualQuotientEquiv` 経由でよい) |
| `\|Q̄\|` even | `C_Q(P) ≠ 1` かつ 2-群 |
| `\|D̄\|` odd | `D∩U` の商 (`D_odd` の約数) |
| (A3) | §4 の `hA3` |

⟹ **`Z(U/Z(U)) = ⊥` だけが未調査**。他は全部既存材料の組み合わせ。

### ⚠ 次セッションはここから

1. `StructureOfH/PSUCentre.lean` と `ProjectiveUnitary/` に標準 `PSU(3,ℓ)` の
   中心自明性が在るか実測。無ければ `residualQuotientEquiv` を使わず、
   `Z(U/Z(U)) = ⊥` を「`Z(U)` が `U` の中心の完全な引き戻し」から直接出せるか検討
   (⚠ 一般には偽なので、モデル側の事実が要る)。
2. 上表の他の 5 つを landing。
3. ⟹ `ofRankOneSetup` を当てて `U/Z(U)` の内在 `Hypothesis` を得る ⟹ 段 (2)。

## 2026-08-02 (117): 🎯 `U/Z(U)` の**内在**標準仮説が landing — `intrinsicResidualQuotient`

新 leaf `OddOrder/Peterfalvi/Appendices/Suzuki/PSU3SectionFourIntrinsic.lean`
(224 行, sorry 0, `OddOrder.lean` 配線済)。段 (2) の主目的物が出た。

### ⚠ (116) の供給表が半分不要になった — 単純性 1 本で忠実性が出る

(114)-(116) は `M̄.normalCore = ⊥` を「`normalCore ≤ Z(L)`」経由で攻めていたので、
`Q̄` が Sylow 2 / `O^{2'}(U/Z(U)) = ⊤` / `Z(U/Z(U)) = ⊥` の 3 本を要求していた。
**`L` が単純ならその 3 本は全部要らない**:

* `Setup.normalCore_eq_bot_of_isSimpleGroup` (`RankOneBNPairRigidity.lean`) —
  `t ∉ M` (Setup の field) ⟹ `M ≠ ⊤` ⟹ `M.normalCore` は正規で `⊤` になれない ⟹ `⊥`。
* `U/Z(U)` の単純性 = Ch. I §3 Lemma 1 (`standardPermGroup_isSimpleGroup`) を
  Proposition 1(c) の同一視で引き戻すだけ (`isSimpleGroup_residualQuotient`)。

⟹ **`Z(U/Z(U)) = ⊥` (116) が「唯一未調査」としていた項目は、そもそも要らなかった**。
(`normalCore_le_center` / `normalCore_eq_bot` / `O^{p'}` 冪等性 (114)-(116) は
汎用定理として残るが、この経路では使わない。)

### 供給した 4 本

| 仮説 | 実装 |
|---|---|
| `M̄.normalCore = ⊥` | `Setup.normalCore_eq_bot_of_isSimpleGroup` + `isSimpleGroup_residualQuotient` |
| `\|Q̄\|` even | `natCard_map_Q_residualQuotient` (= `\|C_Q(X)\|`) + `natCard_cQ_eq_baseField_cube` (= `ℓ³`) |
| `\|D̄\|` odd | `D̄` は `U ∩ D ≤ D` の商、`\|D\|` 奇 (A2) |
| (A3) | 群だけの性質ゆえ同一視で移送 (`two_rank_ge_two_residualQuotient`) |

**`|Q̄| = |C_Q(X)|` の要点**: 商写像の核 `Z(U)` は `D` の中 (`hZD`)、かつ rank-one setup で
`Q ⊓ D = 1` ⟹ `π` は `U ∩ Q` 上で単射。さらに `U ∩ Q = C_Q(X)`
(`Q_inf_residualImage_eq`; `U ≤ C` と「2-群は `2'`-residual に入る」の両包含) ⟹
**§2/§3 が欲しい `|Q̄| = ℓ³` がそのままの形で出る**。

### 橋渡し (今後も毎回要る)

モデル側の同一視 `residualQuotientEquiv` は `residual X : Subgroup ↥C_G(X)` について
述べられ、setup は `G` の中の像 `residualImage X` に住む。両者を繋ぐのが

* `residualImageMulEquiv` = `Subgroup.equivMapOfInjective`
* `residualQuotientMulEquiv` = `quotientCenterCongr` (新設, `SubgroupInAmbient`)

汎用部品として `map_center_mulEquiv` / `quotientCenterCongr` /
`natCard_subgroupOf` / `natCard_map_mk'_of_inf_eq_bot` を `SubgroupInAmbient` に置いた。

### ⚠ 次セッションはここから — §2/§3 の数値仮説を内在版で

1. `\|Q̄\| = ℓ³` を名前付きで (`natCard_map_Q_residualQuotient` +
   `natCard_cQ_eq_baseField_cube` + `natCard_baseField`; ほぼ書くだけ)。
2. **`Q̄₀ = π(Q₀ ∩ U)` の同定** — ここだけ本物の論法が要る。`Q̄₀ = {x̄ ∈ M̄ | x̄² = 1}`
   なので `x̄² = 1` から `U` 側の対合を作る必要がある: `m := |Z(U)|` は**奇数**
   (`CentralizerPSUData.odd_natCard_center_residual`, `PSUCentre.lean:61`) なので
   `y := x^m` が `(x²)^m = 1` かつ `π(y) = x̄^m = x̄` を満たす。
   ⟹ `\|Q̄₀\| = \|C_{Q₀}(X)\| = ℓ` (`natCard_cQ0_eq_baseField`;
   単射性は `Q₀ ≤ Q` と `Q ⊓ D = 1` から前項と同じ)。
3. `Q̄` の Suzuki 2-群性 — `cQ_isSuzuki2Group` を `Q̄ ≅ C_Q(X)` に沿って移送。
4. ⟹ `corollaryTwo_of_sectionThree` を内在 `Hypothesis` に当て、
   `IsFGH.map` (π : U → U/Z(U)) → `IsFGH.eq_of_le` で ambient へ。

## 2026-08-02 (118): §2/§3 の入力を内在版で — 残りは `W̄` と `s̄ t̄`

(117) の内在 `Hypothesis` に対して、Ch. I §3 Lemma 5
(`lemmaFiveSetup_of_orderThree_of_mem_W`) の 7 入力を埋めていく作業。

| 入力 | 状態 | 実装 |
|---|---|---|
| `\|Q̄₀\| = 2ⁿ` | ✅ | `natCard_Q0_intrinsicResidualQuotient` |
| `\|Q̄\| = \|Q̄₀\|³` | ✅ | `natCard_Q_intrinsicResidualQuotient` |
| `n ≠ 0` | ✅ | `data.one_lt_n` |
| `Q̄` が Suzuki 2-群 | ✅ | `isSuzuki2Group_Q_intrinsicResidualQuotient` |
| `TheoremAInductionBelow` | ✅ | `theoremAInductionBelow_intrinsicResidualQuotient` |
| `∃ w ∈ W̄, w ≠ 1` | ⚠ 未 | |
| `orderOf (s̄ · t̄) = 3` | ⚠ 未 | distinguished involution の同定 |

### `Q̄₀ = π(U ∩ Q₀)` — 唯一の本物の論法

`Q̄₀ = {x̄ ∈ M̄ | x̄² = 1}` なので `x̄² = 1` から `U` 側の対合を作る必要がある。
`x̄² = 1` は `x² ∈ Z(U)` しか言わない。**`|Z(U)|` が奇数** (Ch. I §3 Prop 1(c)
`odd_natCard_center_residual`) なので `m := |Z(U)| = 2k+1` と置くと
`y := x^m = x·(x²)^k` が `y² = (x²)^m = 1` かつ `x⁻¹y = (x²)^k ∈ Z(U)`。
汎用補題 `OddOrder.GroupTheory.sq_pow_natCard_eq_one_of_sq_mem` (`OddOrderInvolution.lean`)
として切り出した。

### ⚠ universe の障害 (formalization 固有、記憶に残すこと)

`TheoremAInductionBelow G Ω` は `∀ {A : Type u} {Λ : Type v}` という量化子なので、
**そこに食わせる標準仮説の点集合は `Ω` と同じ universe に無ければならない**。
`ofRankOneSetup` の点集合は `L̄ ⧸ M̄ : Type u` (群と同じ側) なので不適合
(`ULift.{v} (L̄ ⧸ M̄) : Type (max u v)` も不可)。transported 版が
`ULift.{v} (Unital n)` を使っているのはこの理由だった。

解決 = **点集合を小さい型へ貼り替える** (群・部分群は不変):
`ofRankOneSetupOfEquiv` (`RankOneSetup.lean`, 汎用) + `intrinsicPointEquiv`
(`coordsEquiv : L̄ ⧸ M̄ ≅ Q̄ ∪ {a}` と `Q̄ ≅ C_Q(X) ≅ RootGroup ℓ` の合成) で
`L̄ ⧸ M̄ ≃ Unital ℓ`、`Unital ℓ : Type 0` は任意の universe へ lift できる。
⟹ `intrinsicResidualQuotientULift`。

### ⚠ 次セッションはここから

1. `∃ w ∈ W̄, w ≠ 1` — 書籍 p.133 の該当箇所は
   「`|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` since `ℓ > 2`」で、
   `V ∩ U ⊆ P × C_W(P)` (Galois の定理) から `W̄` の非自明元を取っている。
   まず `W̄` (内在版の `W`) と `W ∩ U` の関係を実測すること。
2. `orderOf (s̄ · t̄) = 3` — `distinguishedInvolution` は `Classical.choose` なので
   `eq_distinguishedPair_of_structure` の一意性で同定する
   (`ofMulEquiv_distinguishedInvolution` が transported 版の手本)。
   ⚠ 内在版の `t̄ = π(t)` は transported 版の `t` と**一致しない**可能性があり、
   その差は `K̄` の元 (`exists_mem_K_conj_t_eq` (110) が扱う) — ここが段 (2) の
   「二つの distinguished involution の照合」。
3. ⟹ Lemma 5 → `QuotientFieldModel` → `exists_standardModel` → `corollaryTwo_of_sectionThree`
   を内在版に当て、`IsFGH.eq_of_le` (canonical form の一意性) で ambient へ戻す
   (書籍 p.133 の「By the uniqueness of the canonical form … f(ω) = f₁(ω)」)。

## 2026-08-02 (119): 段 (2) の**転送が両方向揃った** — 残りは中央の 2 仮説だけ

段 (2) の骨格は「`G` ← `U` ← `U/Z(U)`」の 2 段転送で、その両端が landing:

| 向き | 定理 | 書籍 p.133 の対応 |
|---|---|---|
| `G ← U` | `exists_fgh_residual_eq` | 「By the uniqueness of the canonical form of an element of `G − H`, `f(ω) = f₁(ω)` … and `h(ω) = h₁(ω)`」 |
| `U ← U/Z(U)` | `fgh_map_residualQuotient` | §3 Corollary 2 の結論を「核 (`P ∩ U = Z(U)`) を法として」`U` へ戻す |

道具:
* `liftMap` / `IsFGH.ofSubtype` (`RankOneBNPair.lean`, 汎用) — 部分群 `K` 上の三つ組
  `↥K → ↥K` を ambient の `L → L` として読む。`IsFGH` は元についての主張なので
  `K.subtype` で押し出すだけでよく、`M'.subgroupOf K` が `M' ⊓ K` になって
  `IsFGH.eq_of_le` が取る形にちょうど落ちる。
* `IsFGH.map` は既存 (357 行目) — `π = mk' Z` に当てるだけだった。

⟹ **残るのは中央の「§3 Corollary 2 を内在 `Hypothesis` に当てる」1 点**で、その入力は
Ch. I §3 Lemma 5 の 7 本中 2 本:

1. `∃ w ∈ W̄, w ≠ 1`
2. `orderOf (s̄ · t̄) = 3`

### ⚠ この 2 本は PSU(3,ℓ) の構造を使う — 経路 A (照合) が戻る可能性

書籍は `∃ w ∈ W̄, w ≠ 1` を「**By the structure of PSU(3,ℓ)**, `(V ∩ U)/(P ∩ U)`
centralizes `C_{Q₀}(P)` … `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` since `ℓ > 2`」で出す。
`W̄ = V̄ ⊓ C(K̄Set)` は内在的に定義されるが、`π(W ∩ U) ≤ W̄` は自明でない
(`C(K̄Set)` の側の包含が逆向き)。よって

* (113) で「経路 A (transported `hyp'` との三つ組照合) は不要」と書いたのは、
  **`|Q̄|`・`|Q̄₀|`・Suzuki 2-群性のような「群だけの量」については正しかった**が、
  `W̄` と distinguished involution については**戻ってくる可能性が高い**。
* 照合の中身: `M̄` と transported `H` はどちらも指数 `1+ℓ³` の点安定化群なので
  `L̄` の中で共役なはず。これを Lean で出すのが素直かは要検討 (PSU(3,ℓ) の
  2-推移作用の一意性)。もう一方の候補は `V ∩ U` の指数計算を直接やること。

### ⚠ 次セッションはここから

1. まず**実測**: `W̄` (内在) と transported `W` の関係、`residualQuotientHypothesis` の
   `H`/`Q`/`D` が `M̄`/`Q̄`/`D̄` と一致するか (`residualQuotientEquiv` の作り方
   `centralizerResidualQuotientEquiv` を読む — 同一視が `C_Q(X)` から作られていれば
   `Q` は一致する見込みがある)。
2. 一致するなら照合は安く済む。しないなら `V ∩ U` の指数計算 (書籍の Galois の定理
   経由) を正面から形式化する。

### (119) 追記: 同一視の作り方を実測した

`residualQuotientEquiv = (centralizerResidualQuotientEquiv hXV hCQ).trans eTarget`
(`CentralizerTrichotomy.lean:334`) で、

* `centralizerResidualQuotientEquiv` (`CentralizerResidual.lean:312`) —
  `O^{2'}(C) ⧸ Z(O^{2'}(C)) ≃* O^{2'}(C ⧸ (H.subgroupOf C).normalCore)`。
  **`H` の normal core で割った商**を経由する。
* `eTarget = data.groupEquiv` — 帰納法の結論が与える
  `O^{2'}(C/core) ≃* standardPermGroup n`。これは `data.actionEquiv`
  (`Fix(X) ≃ Unital n`, equivariant) と対になっている。

⟹ transported 仮説の `H` は「`actionEquiv` が `infinity` に送る点の安定化群」で、
内在の `M̄ = π(H ∩ U)` は「`basept` の安定化群の像」。**どちらも `L̄` の点安定化群**だが
`actionEquiv` は任意の同変全単射なので `actionEquiv(basept) = infinity` は自明でない。
推移性から**共役**にはなるはずで、そこが照合の要点になる見込み。

⚠ ただし `M̄` が本当に `Fix(X)` 上の作用の点安定化群かは要確認 (`Z(U)` が `Fix(X)` に
自明に作用するか)。次セッションはまずここを実測すること。

## 2026-08-02 (120): `s̄ = π(s)` が landing — Lemma 5 の入力は残り 1 本

⚠ (119) では「distinguished involution の同定には照合 (経路 A) が要るかも」と書いたが
**不要だった**。Ch. I §3 が既に持っていた 2 本が効いた:

* `distinguishedInvolution_mem_centralizer_of_le_V` /
  `structureConjugator_mem_centralizer_of_le_V` (`CentralizerDistinguishedBridge.lean`)
  — `X ≤ V` なら `s` も `r` も `C_G(X)` に入る。

⟹ `s` は対合なので `U` に入り (`sq_eq_one_mem_residual`)、`r ∈ Q ∩ C ≤ U`。構造方程式
`t s t = r⁻¹ t r` が `U` の中で成り立つので `π` で落とせて、
`eq_distinguishedPair_of_structure` の一意性で `s̄ = π(s)`。
`π(s) ≠ 1` は **`|Z(U)|` が奇数** (対合は中心に入れない) から。

`|s̄ t̄| = 3` は `|s t| = 3` (`details.distinguishedProduct_order`) から `∣ 3`、
`= 1` は `t̄ ∉ M̄` に反する (3 が素数なので二択)。

### Lemma 5 の入力 (更新)

| 入力 | 状態 |
|---|---|
| `\|Q̄₀\| = 2ⁿ` / `\|Q̄\| = \|Q̄₀\|³` / `n ≠ 0` | ✅ |
| `Q̄` が Suzuki 2-群 | ✅ |
| `TheoremAInductionBelow` | ✅ |
| `orderOf (s̄ · t̄) = 3` | ✅ **今回** |
| `∃ w ∈ W̄, w ≠ 1` | ⚠ **残り 1 本** |

### ⚠ 次セッションはここから — `∃ w ∈ W̄, w ≠ 1`

書籍 p.133 は「`(V ∩ U)/(P ∩ U)` が `C_{Q₀}(P)` を中心化 → Galois の定理で
`V ∩ U ⊆ P W` → `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1 since ℓ > 2`」。

内在版で狙うなら:
* `W̄ = V̄ ⊓ C(K̄Set)`, `V̄ = D̄ ⊓ C(t̄)`。`π(V ∩ U) ≤ V̄` と `π(K ∩ U) ⊆ K̄Set` は
  どちらも自明 (`t̄ = π(t)`, `D̄ = π(D ∩ U)`)。⚠ 問題は `W̄` 側で、`C(K̄Set)` の包含が
  逆向きになる点。
* 別ルート候補: `V̄ = W̄` を内在的に出せれば `V̄ ≠ 1` に落ちる
  (transported 版では `residualQuotientHypothesis_V_eq_W` が在る)。
* さらに別ルート: `|D̄|` と `|K̄|` を数え、`D̄ = V̄ · K̄` (奇位数群への対合作用の分解)
  から `V̄ ≠ 1`。`|D̄|` は `|D ∩ U|` の商だが、モデル側では `(ℓ²-1)/(ℓ+1,3)`。

まず transported 版 `residualQuotientHypothesis_V_eq_W` の証明を読んで、内在版に
移せるか実測すること。

## 2026-08-02 (121): ⚠ 重要な実測 — §2/§3 は既に**中心化群商 `C/𝒩(C)` の内在仮説**で走っている

`∃ w ∈ W̄, w ≠ 1` を探して §4 の setup を読んだところ、`PSU3SectionFourSetup.lean` に
**`SectionFourSetup.standingData_centralizerQuotient`** (1163 行) が既にあり、
`hyp.centralizerQuotientHypothesis s4.P_le_V hA3` (= `C/𝒩(C)` 上の**内在**標準仮説;
`H`,`Q`,`D` は `C_H(P)`,`C_Q(P)`,`C_D(P)` の像) について

* `n ≠ 0` / `|Q̄₀| = 2ⁿ` / `|Q̄| = |Q̄₀|³` / `|s̄ t̄| = 3` / `Q̄` が Suzuki 2-群
* `Nonempty (LemmaFiveSetup n)` / `Nonempty (QuotientFieldModel n)`

を**§4 の ambient 仮説だけから**与えている。つまり Ch. I §3 Lemma 5 の入力一式は
`C/𝒩(C)` については既に揃っている。

とくに、私が探していた `∃ w ∈ W̄, w ≠ 1` に対応するものは
* `s4.exists_ne_one_mem_W_centralizer` — `∃ w ∈ W, w ≠ 1 ∧ w ∈ C_G(P)`
  (書籍の `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1`)
* `s4.exists_ne_one_mem_quotient_W` — その `C/𝒩(C)` への降下

として**既に landing 済**だった。

### ⚠ 戦略上の含意 (次セッションの最初の判断)

`O^{2'}(C/𝒩(C)) ≅ U/Z(U)` (`centralizerResidualQuotientEquiv`) なので、`C/𝒩(C)` は
`U/Z(U)` を奇指数で含む群。書籍は「`U`, `U ∩ H`, `t` についての `f₁`, `h₁`」と書くが、
**`C`, `C ∩ H`, `t` についての三つ組でも同じ転送 (`IsFGH.eq_of_le`) が効く** はず
(`rankOneSetup_subgroup` は `K = C` にも当たる)。だとすると

1. `C/𝒩(C)` 経由で §3 Corollary 2 を当てるほうが**入力が既に揃っている分だけ近道**。
2. 私が (117)-(120) で作った `U/Z(U)` の内在仮説は無駄ではない (書籍の `U` そのもので、
   `mem_center_primeComplementResidual_of_mem_P` 等 §4 は `U` を実際に使う) が、
   段 (2) を閉じる最短路ではないかもしれない。

**次セッションはまずここを裁定する**: `corollaryTwo_of_sectionThree` を
`centralizerQuotientHypothesis` に当てるのに何が足りないかを実測し
(`hVW` / `hZc` / `hmu` / `hKcard` / `hWdvd` / `hW1` / bilinear package /
`IsStandardModel`)、`C/𝒩(C)` 経路と `U/Z(U)` 経路のどちらが短いかを決める。
⚠ どちらにせよ (119) の 2 方向の転送 (`exists_fgh_residual_eq` /
`fgh_map_residualQuotient`) は `U` 版なので、`C` 版が要るなら同じ形で作り直す
(`rankOneSetup_subgroup` に `K = C` を当てるだけ)。

## 2026-08-02 (122): 裁定 — 段 (2) は `C/𝒩(C)` 経路で閉じる

(121) の実測を受けて裁定した。**`C/𝒩(C)` 経路を採る**。

| | `U/Z(U)` 経路 | `C/𝒩(C)` 経路 |
|---|---|---|
| 内在仮説 | (117) で新造 | `centralizerQuotientHypothesis` (既存) |
| Lemma 5 の 7 入力 | 6/7 ((118)-(120)) | **7/7** (`standingData_centralizerQuotient`) |
| `LemmaFiveSetup` / `QuotientFieldModel` | 未 | **済** (同上) |
| 点集合の universe | ⚠ `L̄ ⧸ M̄ : Type u` ゆえ `Unital ℓ` へ貼り替えが必要だった | `Fix(X) : Type v` で**問題なし** |
| 転送 (`G ← · ← 商`) | (119) | **今回** |

⟹ 今回 `C` 版の転送 4 本を landing:
* `rankOneSetup_centralizer` (`rankOneSetup_subgroup` の `K = C`)
* `setup_centralizerQuotient` — `𝒩(C) = C_D(X) ⊓ C_C(C_Q(X))` (`normalCore_cH_eq_centralizer_cQ`)
  が `C_D(X)` に入るので `Setup.quotient` が効く。**3 像は `centralizerQuotientHypothesis` の
  `H`,`Q`,`D` そのもの**なので `Setup.exists_fgh` はその仮説の `f`,`g`,`h` を返す。
* `exists_fgh_centralizer_eq` (`G ← C`) / `fgh_map_centralizerQuotient` (`C ← C/𝒩(C)`)

`U/Z(U)` 側 (117)-(120) は破棄しない — 書籍の `U` そのもので §4 は実際に `U` を使う
(`mem_center_primeComplementResidual_of_mem_P` 等)。`∃ w ∈ W̄_{U/Z(U)}, w ≠ 1` だけが
未証明で残るが、これは段 (2) の critical path から外れた。

### ⚠ 次セッションはここから

`corollaryTwo_of_sectionThree` を `centralizerQuotientHypothesis` に当てる。
`standingData_centralizerQuotient` が `sfive`/`M`/数値を与えるので、残りは
`exists_standardModel` を回して `IsStandardModel` を得ること、および
`corollaryTwo_of_sectionThree` の残り仮説:
`hC2` (`t̄s̄t̄ = s̄t̄s̄`, `|s̄t̄| = 3` から) / `hZc` / `hmu` / `hVW` / `hcard` /
`hKcard` / `hWdvd` / `hW1` / `hfQ` / `hhW` / bilinear package (`IsStandardModel` から分解)。
**まず `PSU3SectionFourSetup.lean` を grep して、これらのうち既に
centralizer quotient 版が在るものを列挙すること** (`natCard_quotient_*`,
`isSuzuki2Group_quotient_Q`, `psu3Numerics_and_standingData_centralizerQuotient` の
周辺に固まっている)。

## 2026-08-02 (123): 🎯 §3 の Proposition が `C/𝒩(C)` で成立 — 段 (2) の中央が埋まった

`SectionFourSetup.isStandardModel_centralizerQuotient` (`PSU3SectionFourIntrinsic.lean`)。
`centralizerQuotientHypothesis` について `IsStandardModel` を得た。**必要な入力は
全部既に在った**:

* `standingData_centralizerQuotient` — 2 bundle + 数値 4 本
* `theoremAInductionBelow_centralizerActionQuotient` — 帰納法仮説の制限
* `exists_center_Q_ne_one` — `x₀ ∈ Z(Q̄), ≠ 1` (任意の `Hypothesis` に generic)

⚠ 実務メモ: `exists_standardModel` は section variable の `s : LemmaFiveSetup m` と
`M : QuotientFieldModel m` を**先頭の explicit 引数**として取る (`include s in` +
自動 include)。`hst` から渡すと型不一致になる。

### 段 (2) の 3 ピース

| ピース | 定理 | 状態 |
|---|---|---|
| `G ← C` | `exists_fgh_centralizer_eq` | ✅ (122) |
| 中央 (§3 Corollary 2) | `isStandardModel_centralizerQuotient` → `corollaryTwo_of_sectionThree` | ✅ 前半 / ⚠ 後半 |
| `C ← C/𝒩(C)` | `fgh_map_centralizerQuotient` | ✅ (122) |

### ⚠ 次セッションはここから — `corollaryTwo_of_sectionThree` を当てる

`IsStandardModel` は得たので、残りは `corollaryTwo_of_sectionThree` の**それ以外**の
仮説を `C/𝒩(C)` について供給すること:

`H` (= `IsFGH`, `setup_centralizerQuotient` + `Setup.exists_fgh` で出る) /
`hC2` (`t̄s̄t̄ = s̄t̄s̄`; `|s̄t̄| = 3` と対合性から) / `hZc` (`Z(Q̄) = Q̄₀ ∩ Q̄`) /
`hmu` / `hVW` (`V̄ = W̄`) / `hcard` (`5 ≤ |frobFixedSubfield|`) /
`hKcard` (`|actualKActor| = 2ᵐ - 1`) / `hWdvd` / `hW1` / `hfQ` / `hhW` /
bilinear package (`Φ`, `φ`, `θm`, `Θ`, `ι`, `hker`, `hquot`, `hW`, `hΘq`, `hΘc`)。

⚠ **bilinear package は `IsStandardModel` の分解で出るはず** — `IsStandardModel` の
定義を読んで、`corollaryTwo_of_sectionThree` の引数と 1:1 に対応するか確認すること
(`isStandardModel_residualQuotient` の呼び出し側 = 未だ無い、が
`PSU3CorollaryTwo.lean` に `corollaryTwo_of_standardModel` が在るのでそちらが
package 済みの入口かもしれない — **まずそれを grep**)。

### (123) 追記: `corollaryTwo_of_standardModel` の残り引数の棚卸し

`IsStandardModel` は**存在命題**で、`corollaryTwo_of_standardModel` が取る
bilinear package (`φ`,`θ`,`Φ`,`Θ`,`u`,`ι` + 8 条件) を**そのまま bundle している**
(`ModelAction.lean:724`)。つまり分解して渡すだけ。

`C/𝒩(C)` について残るのは以下 7 本 (数値 `hm`/`hQ0card`、`sfive`/`M`、`H` (=`IsFGH`,
`setup_centralizerQuotient` + `Setup.exists_fgh`) は済):

| 引数 | 見込み |
|---|---|
| `hC2` (`t̄s̄t̄ = s̄t̄s̄`) | `\|s̄t̄\| = 3` + 対合性から初等的 |
| `hZc` (`Z(Q̄) = Q̄₀ ∩ Q̄`) | `ActualCenter.lean:143` `center_Q_eq_Q0_subgroupOf_of_sq_eq_one` が近い |
| `hmu` | `QuotientKWField.lean:504` `Hypothesis.mu_injective` が generic (`hst`/`hn`/`hQ0card`/`hcardQ`/`ih` を取る — 全部 in hand) |
| `hVW` (`V̄ = W̄`) | ⚠ 要調査。`V_eq_W_iff_le_centralizer_Q0` (内在判定) が使える見込み |
| `hKcard` (`\|K̄\| = 2ᵐ-1`) | ⚠ 要調査。`ModelIsomorphism.lean:91` `exists_actualKActor_mu_eq` の周辺 |
| `hWdvd` (`\|W̄\| ∣ 2ᵐ+1`) / `hW1` | `hW1` は `exists_ne_one_mem_quotient_W` から。`hWdvd` は要調査 |
| `hfQ` / `hhW` | 三つ組の性質。`hfQ` は `IsFGH.f_mem`。`hhW` は §2 の結果 (`h ρ ∈ W` for `ρ ∉ Q₀`) を探す |

⟹ 次セッションは上表を上から順に埋める。`hVW` / `hKcard` / `hWdvd` / `hhW` の 4 本が
実測待ちで、それ以外は既存資産の組み合わせ。

## 2026-08-02 (124): Corollary 2 の残り引数 — 依存を解いた結果、primitive は 3 本

(123) の 7 引数のうち 2 本を landing:
* `hC2` = `Hypothesis.braid_of_orderOf_mul_eq_three` (`DistinguishedInvolution.lean`)
* `hfQ` の下準備 = `Setup.exists_fgh_one` (`RankOneBNPair.lean`) — `IsFGH` は `Q^#` 上しか
  制約しないので `f 1` が野放しだった。`f 1 = g 1 = h 1 = 1` の正規化版。

残りを実測したところ、**`hhW` は独立ではなく `hVW`/`hWdvd`/`hZc`/`hmu` から出る**
(`PSU3StepEighteen.h_mem_W` (159 行) がまさにそれで、`hC2`/`M`/`hZ`/`hmu`/`hVW`/`hm`/
`hQ0card`/`hWdvd` を取る §2 の結果)。⟹ 本当の primitive は:

| 引数 | 状態 |
|---|---|
| `hZc` (`Z(Q̄) = Q̄₀ ∩ Q̄`) | `ActualCenter.center_Q_eq_Q0_subgroupOf_of_sq_eq_one` に `Z(Q̄)` の指数 2 を与えればよい (`Q̄` は Suzuki 2-群なのでその中心は初等可換 — `Higman` 側に在るはず) |
| `hmu` | `QuotientKWField.mu_injective` が generic。`hst`/`hn`/`hQ0card`/`hcardQ`/`ih` は全部 in hand ⟹ **ほぼ書くだけ** |
| `hVW` (`V̄ = W̄`) | ⚠ 本物。`V_eq_W_iff_le_centralizer_Q0` で `V̄ ≤ C(Q̄₀)` に還元できる |
| `hKcard` (`\|K̄\| = 2ᵐ-1`) | ⚠ 本物 |
| `hWdvd` (`\|W̄\| ∣ 2ᵐ+1`) | ⚠ 本物 (`hW1` は `exists_ne_one_mem_quotient_W` から出る) |

### ⚠ 次セッションはここから

1. `hmu` — `mu_injective` を `centralizerQuotientHypothesis` に当てる (機械的)。
2. `hZc` — `Q̄` の中心が指数 2 であること。`Q̄` が Suzuki 2-群であることは
   `isSuzuki2Group_quotient_Q` で在るので、`Higman/Suzuki2Groups/CenterInvolutions.lean`
   あたりに「Suzuki 2-群の中心は初等可換」が在るか実測。
3. `hVW` / `hKcard` / `hWdvd` — この 3 本が段 (2) の実質的な残り。transported 版
   (`residualQuotientHypothesis_V_eq_W` 等) がモデルからどう出しているかを読み、
   `centralizerQuotientHypothesis` へ移せるか (= `C/𝒩(C)` と `PSU(3,ℓ)` の
   同一視をどう使うか) を裁定する。⚠ `C/𝒩(C)` は `PSU(3,ℓ)` を奇指数で含むので
   `PSU(3,ℓ)` そのものではない点に注意 — `V`,`K`,`W` は `D̄` の中で測るので、
   `D̄` と `PSU(3,ℓ)` の torus の関係が要る。

## 2026-08-02 (125): `hmu` と `hZc` が landing — Corollary 2 の残りは 3 本

| 引数 | 状態 |
|---|---|
| `hC2` | ✅ `braid_of_orderOf_mul_eq_three` |
| `hfQ` の下準備 | ✅ `Setup.exists_fgh_one` |
| `hmu` | ✅ `isStandardModel_centralizerQuotient` に同梱 |
| `hZc` | ✅ `center_Q_eq_Q0_centralizerQuotient` |
| `hVW` / `hKcard` / `hWdvd` | ⚠ **残り 3 本** (`hW1` は `exists_ne_one_mem_quotient_W`、`hhW` は `h_mem_W` 経由) |

`hZc` は根群の事実だけで済んだ: `Z(Q̄)` の指数 2 に還元 (`ActualCenter`) →
`Q̄ ≅ C_Q(X) ≅ RootGroup ℓ` → **`RootGroup.center_eq_centerLine`** (既存,
`RootGroupSuzukiType.lean:46`)。

### ⚠ instance の罠 (記憶に残すこと)

`Model` section の抽象 `[MulAction (hyp.centralizerActionQuotient X) ↥(Fix X Ω)]` と
`hyp.centralizerQuotientMulAction hXV` の `letI` は**別インスタンス**として扱われる。
`CentralizerPSUData` (前者を使う) と `centralizerQuotientHypothesis` (後者を使う) を
同じ文に混ぜると `synthesized type class instance is not definitionally equal` が出る。
⟹ **同一視は `details` から読まずパラメータ (`eRoot : C_Q(X) ≃* RootGroup n`) で受ける**。

### ⚠ 次セッションはここから — `hVW` / `hKcard` / `hWdvd`

3 本とも `D̄` の内部構造 (`V̄`, `K̄`, `W̄` の位数) についての主張。⚠ **`C/𝒩(C)` は
`PSU(3,ℓ)` を奇指数で含むだけ**なので、`RootGroup` のようにモデルから直に読めない。
まず transported 版 (`PSU3SectionFourModel.residualQuotientHypothesis_V_eq_W` および
`standardHypothesis_V_eq_W`) がモデルからどう出しているかを読み、`D̄` と
`PSU(3,ℓ)` の torus の関係を実測すること。

候補: `V_eq_W_iff_le_centralizer_Q0` で `hVW` を `V̄ ≤ C(Q̄₀)` に還元し、
`Q̄₀ = π(C_{Q₀}(X))` (`map_centralizer_Q0_eq_quotient_Q0`) を使って ambient の
`C_D(X) ≤ C(C_{Q₀}(X))` に落とせないか (= §4 の `centralizer_V_centralizer_Q0`
= Galois の定理の周辺)。

## 2026-08-02 (126): `hVW` の核 — 「モデルから読む中心化」が §4 では既に**仮説として孤立**している

`commute_of_commute_mk'_of_mem_D_of_mem_Q` (今回) で `hVW` は次に還元される:

`hVW` ⟸ `V̄ ≤ C(Q̄₀)` (`V_eq_W_iff_le_centralizer_Q0`)
      ⟸ 「`π(v) ∈ V̄` なる `v ∈ C_D(X)` は `C_{Q₀}(X)` を中心化する」(本補題で核が落ちる)

⚠ **重要な実測**: この形の主張は §4 では既に**孤立した仮説**として扱われている。
`SectionFourSetup.inf_le_sup_W_of_centralizes` (`PSU3SectionFourSetup.lean:918`) は

```
(hcent : V ⊓ U ≤ centralizer (Q₀ ⊓ C(P)))  →  V ⊓ U ≤ P ⊔ W
```

で、docstring が「**the hypothesis here is the centralizing statement the book reads off
the structure of `PSU(3, ℓ)`**」と明記している。Galois の定理
(`centralizer_V_centralizer_Q0 : V ⊓ C(Q₀ ⊓ C(P)) = P ⊔ W`) は逆向きの計算で、
中心化そのものは与えない。

`exists_ne_one_mem_W_centralizer` はこれを**モデルから**取っている:
`details.exists_mem_residual_commute_Q0` が `C_{Q₀}(P)` と可換な `x ∈ O^{2'}(C)` を与え、
その `V`-成分に Galois を当てて `v ∈ P ⊔ W` を得る (証明 1015-1030 行)。

⟹ `hVW` も同種の**モデル入力**を要する。次セッションはまず
`CentralizerPSUData.exists_mem_residual_commute_Q0` の statement を読み、
`V̄` の元の持ち上げ全体について同じ中心化が言えるか (= `PSU(3,ℓ)` で
`C_{D̄}(t̄) ≤ C(Q̄₀)` = torus の中で `V = W`) を実測すること。

### 今の在庫 (Corollary 2 の引数)

| 引数 | 状態 |
|---|---|
| `hC2` / `hfQ` 下準備 / `hmu` / `hZc` | ✅ |
| `hW1` / `hhW` | ✅ 導出可 |
| `hVW` | ⚠ 上記の還元まで。モデル入力が要る |
| `hKcard` / `hWdvd` | ⚠ 未着手 |

### (126) 追記: 既存のモデル入力は「1 点」で `hVW` には足りない

`CentralizerPSUData.exists_mem_residual_commute_Q0` (`StructureOfH/PSUCentre.lean:111`) は

```
∃ x ∈ O^{2'}(C), π(x) ≠ 1 ∧ Odd (orderOf π(x)) ∧ ∀ y ∈ Q₀ ∩ C, Commute x y
```

で、**`C_{Q₀}(X)` を中心化する元を 1 つ**しか与えない。`hVW` (`V̄ ≤ C(Q̄₀)`) は
`V̄` の**全元**についての主張なので、これでは足りない。

必要なモデル入力は「`PSU(3,ℓ)` の torus で `C_D(t) ≤ C(Q₀)`」= 標準モデルの
`standardHypothesis_V_eq_W` (`StandardModelHypothesis.lean:271`; 証明は
`V ≤ D = psuTorusHom.range` が可換であることによる) を `C/𝒩(C)` へ移すこと。
⚠ `C/𝒩(C)` は `PSU(3,ℓ)` を奇指数で含むので `D̄` は torus より大きくてよい —
`D̄` が可換かどうかから調べる必要がある (`D̄ = π(C_D(X))`)。

⟹ **`hVW`/`hKcard`/`hWdvd` は 3 本まとめて「`D̄` の構造」の問題**。次セッションは
`D̄` (= `π(C_D(X))`) と `PSU(3,ℓ)` の torus の関係を実測することから始める
(`C/𝒩(C)` と `O^{2'}(C/𝒩(C)) ≅ U/Z(U)` の指数が奇であることが効くはず)。

## 2026-08-02 (127): ⚠ (122) の裁定を訂正 — Corollary 2 は `U/Z(U)` でないと当たらない

`hVW` を追ったところ、(122) の「段 (2) は `C/𝒩(C)` 経路で閉じる」は
**Corollary 2 の段では誤り**だと分かった。

### 理由: `V = W` は `PSU(3,ℓ)` そのものの事実で、`C/𝒩(C)` では成り立つ保証がない

* `O^{2'}(C/𝒩(C)) ≅ U/Z(U) ≅ PSU(3,ℓ)` は `C/𝒩(C)` の**奇指数**正規部分群
  (Theorem A の結論の形)。つまり `C/𝒩(C)` は `PSU(3,ℓ)` を真に含みうる
  (差分は奇位数の体自己同型)。
* `V = W` は `V ≤ C(Q₀)` と同値 (`V_eq_W_iff_le_centralizer_Q0`)。torus の元は
  `Q₀` を norm-1 のときだけ中心化するが、**体自己同型は `Q₀` を中心化しない**。
  ⟹ `D̄ = π(C_D(X))` が torus より大きいと `V̄ ⊋ W̄` になりうる。
* 実測: repo に `V = W` は **`standardHypothesis_V_eq_W`** (標準モデル) と
  **`residualQuotientHypothesis_V_eq_W`** (`U/Z(U)` へ移送) の 2 本しかなく、
  `centralizerQuotientHypothesis` 版は**無い**。これは上の分析と整合する。
* 書籍も「**relative to `U`, `U ∩ H` and `t`** … by Corollary 2 of the proposition of §3」
  と書いており、Corollary 2 は `U` について当てている (p. 133)。

### 訂正後の像

| 段 | 場所 | 根拠 |
|---|---|---|
| Lemma 5 / §3 の Proposition (`IsStandardModel`) | `C/𝒩(C)` で**可** (実際 (123) で landing) | `V = W` を要求しない |
| **Corollary 2** | **`U/Z(U)` が必要** | `hVW` を要求する |

⟹ (117)-(120) の `U/Z(U)` 内在仮説は**critical path に戻る**。(122) で作った
`C`/`C/𝒩(C)` の転送 4 本と (123) の `isStandardModel_centralizerQuotient` は
genuine な結果として残る (§3 の Proposition は実際に `C/𝒩(C)` で成り立つ) が、
段 (2) を閉じるのは `U/Z(U)` 側。

### ⚠ 次セッションはここから

`U/Z(U)` の**内在**仮説について Corollary 2 の引数を揃える。今の在庫:

| 引数 | `U/Z(U)` 内在版の状態 |
|---|---|
| `hm` / `hQ0card` / `hcardQ` / `hst` | ✅ (118)(120) |
| `hQsuz` (Lemma 5 用) / `ih` | ✅ (118) |
| `hC2` | ✅ `braid_of_orderOf_mul_eq_three` (generic) |
| `hZc` | 同じ論法で行けるはず — `Q̄ ≅ C_Q(X) ≅ RootGroup ℓ` は `cQMulEquivMapQ` + `cQEquivRoot` で在る (125 の `C/𝒩` 版をそのまま移す) |
| `hmu` | generic な `mu_injective` (入力は全部在る) |
| `∃ w ∈ W̄, w ≠ 1` / `hVW` / `hKcard` / `hWdvd` | ⚠ 未。**`U/Z(U)` では `V̄ = W̄` が真**なので、transported 版 `residualQuotientHypothesis_V_eq_W` を内在版へ移せるかが鍵 = (119) で保留した「内在 vs transported の照合」 |

⟹ 照合 (経路 A) が本当に必要なのはここ。`M̄` と transported `H` はどちらも
`L̄` の点安定化群なので共役 (121 の実測) — その共役で `V`,`K`,`W` も対応する。

## 2026-08-02 (128): `∃ w ∈ W̄, w ≠ 1` を ambient の言葉に還元

`commute_of_commute_mk'_center_of_mem_D_of_mem_Q` (今回) + `W_eq_inf_centralizer_Q0`
(generic) + `Q0_intrinsicResidualQuotient_eq` ((118)) で:

> **`∃ w ∈ W̄, w ≠ 1`  ⟺  `∃ v ∈ D ∩ U` with `v ∉ Z(U)` centralizing `C_{Q₀}(X)`**

(核 `Z(U)` は `Q`-側で落ちる: `[v,u] ∈ Q ⊓ Z(U) ≤ Q ⊓ D = 1`。)

⚠ 残るのは**その `v` を `U` の中で作ること**。ambient の
`SectionFourSetup.exists_ne_one_mem_W_centralizer` は `ζ ∈ W ⊓ C_G(X)`, `ζ ≠ 1` を
与えるが `ζ ∈ U` は言わない (`ζ` は奇位数で、`U = O^{2'}(C)` は `C` の奇位数商を持つ)。
書籍が `ζ₁ ∈ (V ∩ U) − (P ∩ U)` を `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` で
作っているのはまさにここ。

### ⚠ 次セッションの選択肢 (どちらかを裁定する)

**(a) 指数計算を正面から** — `|(V ∩ U)/(P ∩ U)|` をモデルから計算する。
`U/Z(U) ≅ PSU(3,ℓ)` の中で `V̄ = W̄` の位数が `(ℓ+1)/(ℓ+1,3)` であることを使う。
⟹ transported 版の `W` の位数が要る (`standardHypothesis` 側に在るか実測)。

**(b) 照合 (経路 A)** — `M̄` と transported `H` が `L̄` の点安定化群として共役
((121) の実測) であることを使い、`V`,`K`,`W` の対応を出す。これが取れれば
`∃ w ∈ W̄` だけでなく `hVW` / `hKcard` / `hWdvd` も**まとめて**移送できる
(transported 版には `residualQuotientHypothesis_V_eq_W` が在る)。

⟹ **(b) のほうが 4 本まとめて片付くので有利**に見える。次セッションは (b) の
実現可能性を実測する: `L̄` の 2 つの 2-推移作用 (`L̄ ⧸ M̄` と `ULift (Unital ℓ)`) が
同値であること (= 点集合の同変全単射) をどう作るか。(119) の `intrinsicPointEquiv` は
集合としての全単射までは作っているので、それが**同変**になるよう取り直せるかが鍵。

## 2026-08-02 (129): 標準仮説の**剛性** — `Q` は Sylow 2、`M = N_L(Q)`

照合 (経路 A) の骨格 2 本が landing。⚠ **どちらもモデルを一切使わない汎用の `Setup` の定理**。

* `Setup.natCard_M` / `Setup.index_M` / `Setup.natCard_L` —
  **`|L| = |Q| · |D| · (1 + |Q|)`**。`M = Q ⋊ D` の一意分解が全単射 `Q × D ≃ M` を与え、
  `L ⧸ M ≅ Q ∪ {a}` (`coordsEquiv`, Ch. IV §1 p.123) が `[L:M] = 1 + |Q|` を与える。
* `Setup.exists_sylow_two_eq` — `Q` が 2-群 / `|D|` 奇 / `|Q|` 偶 ⟹ **`Q` は Sylow 2**
  (残り 2 因子が奇なので `[L:Q]` が奇)。
* `Setup.normalizer_Q_eq` — `Q ≠ 1` ⟹ **`N_L(Q) = M`**。極大性も単純性も使わない:
  `x ∉ M` を `a·t·b` と分解すると `t` も `Q` を正規化することになり、
  `t q t ∈ Q ≤ M` が `Setup.tconj` (`Q^t ∩ M = 1`) に反する。

⟹ **同じ `L` 上の 2 つの setup は `Q` が Sylow 2 ゆえ共役、`M = N_L(Q)` ゆえ `M` も
同じ共役で移る**。

### ⚠ 次セッションはここから — 照合の残り 3 段

1. **`Setup.exists_conj_eq`** (組み立て) — 上 2 本 + Sylow の共役性
   (`MulAction.exists_smul_eq` on `Sylow 2 L`, `Sylow.coe_subgroup_smul`) +
   `Subgroup.map_equiv_normalizer_eq` で
   `∃ c, Q.map (conj c) = Q' ∧ M.map (conj c) = M'`。
   ⚠ `Subgroup.normalizer` はこの mathlib では `Set` 引数なので、
   `map`/`normalizer` の交換補題の形に注意 (`map_equiv_normalizer_eq` を実測すること)。
2. **`D` の照合** — `D`, `D'` は `M` の中の `Q` の補群で位数が互いに素なので
   Schur–Zassenhaus で共役。`M` の元でさらに共役を取る。
3. **`t` の照合** — `exists_mem_K_conj_t_eq` (110) が「2 つの distinguished involution は
   `K` の元だけずれる」を扱う。

⟹ 3 段が揃えば `L̄` の自己同型 `φ` で
`φ(H_tr, Q_tr, D_tr, t_tr) = (M̄, Q̄, D̄, t̄)` が取れ、transported 側の
`residualQuotientHypothesis_V_eq_W` 等から **`hVW` / `hKcard` / `hWdvd` / `∃w∈W̄` が
まとめて移送できる**。

## 2026-08-02 (130): 🎯 `Setup.exists_conj_eq` — 照合の前半が landing

`Setup.exists_conj_eq` (`RankOneBNPairRigidity.lean`) — 同じ群 `L` 上の 2 つの
rank-one setup について `∃ c, Q^c = Q' ∧ M^c = M'`。⚠ **モデルを一切使わない**:
`Q`, `Q'` はどちらも Sylow 2 ((129)) ゆえ共役 (`MulAction.exists_smul_eq` on `Sylow 2 L`)、
`M = N_L(Q)` ((129)) ゆえ `Subgroup.map_equiv_normalizer_eq` で `M` も移る。

### ⚠ 次セッションはここから — `D` の照合 (道具は repo に在る)

`Q^c = Q'`, `M^c = M'` まで来たので、`↥M'` の中で `D^c` と `D'` はどちらも `Q'` の補群。
位数は互いに素 (`|Q'|` は 2 冪、`[M' : Q'] = |D'|` は奇) で `Q'` は 2-群ゆえ可解。

⟹ **`Subgroup.IsComplement'.exists_conj_of_coprime`**
(`OddOrder/Mathlib/SchurZassenhausConj.lean:1292`, 既存!) がそのまま使える:

```
(hN : Coprime (card N) N.index) (hSolv : IsSolvable N ∨ IsSolvable (G ⧸ N))
(hK : IsComplement' N K) (hK' : IsComplement' N K') :
  ∃ n ∈ N, K.map (MulAut.conj n) = K'
```

実装の要点:
* `↥M'` の中で作業する (`N := Q'.subgroupOf M'`, `K := (D.map (conj c)).subgroupOf M'`,
  `K' := D'.subgroupOf M'`)。
* `IsComplement'` は `Setup` の `split` (一意分解 `M = Q ⋊ D`) から出る
  — `Q ⊓ D = ⊥` (`Setup.Q_inf_D_eq_bot`) と `Q * D = M` (`split` の全射性)。
* 得た `n ∈ Q'` でさらに共役を取ると `Q'`, `M'` は不変 (`Q' ⊴ M'`) なので
  `Q^{cn} = Q'`, `M^{cn} = M'`, `D^{cn} = D'` が同時に成り立つ。

その後 `t` の照合 (`exists_mem_K_conj_t_eq` (110)) で四つ組が揃い、
`hVW` / `hKcard` / `hWdvd` / `∃w∈W̄` が transported 側からまとめて移送できる。

## 2026-08-02 (131): 🎯 照合の主定理 `Setup.exists_conj_eq_triple` — 残りは `t` のみ

同じ群 `L` 上の 2 つの rank-one setup について
**`∃ c, Q^c = Q' ∧ M^c = M' ∧ D^c = D'`**。⚠ **モデルを一切使わない汎用定理**。

| 部品 | 内容 |
|---|---|
| `Setup.exists_conj_eq` ((130)) | `Q` は Sylow 2 ゆえ共役、`M = N_L(Q)` ゆえ `M` も移る |
| `Setup.exists_conj_D_eq` (今回) | `Q'` の補群で位数が合うものは `Q'` の元で `D'` に共役 |
| `map_conj_self` / `map_conj_mul` (今回) | 共役の合成・自明化の小道具 |

`exists_conj_D_eq` の中身: `Q'` は `M'` の正規 2-部分群で指数 `|D'|` が奇 ⟹
**Schur-Zassenhaus 共役** `Subgroup.IsComplement'.exists_conj_of_coprime`
(`OddOrder/Mathlib/SchurZassenhausConj.lean:1292`, 既存) が当たる。`IsComplement'` は
`isComplement'_of_card_mul_and_disjoint` (位数積 + disjoint) で作った。得た `n ∈ Q'` で
さらに共役しても `Q'`,`M'` は動かない (`n ∈ Q' ≤ M'`) ので 3 つ同時に揃う。

### ⚠ 次セッションはここから — `t` の照合

四つ組の最後。`c` で `Q,M,D` を合わせた後、`t^c` と `t'` はどちらも `L − M'` の対合で
`D' = M' ⊓ M'^{t'}` を与える。書籍 p.133 の「2 つの distinguished involution は
`K` の元だけずれる」がこれで、道具は `Hypothesis.exists_mem_K_conj_t_eq` ((110)):
`d ∈ K` に対し `∃ e ∈ K, e⁻¹ t e = d t`。

⟹ 揃えば `L̄` の自己同型 `φ` で `φ(H_tr,Q_tr,D_tr,t_tr) = (M̄,Q̄,D̄,t̄)` が取れ、
`V`,`K`,`W`,`Q₀` はすべて `H,Q,D,t` から定義されるので対応する。⟹ transported 側の
`residualQuotientHypothesis_V_eq_W` 等から **`hVW` / `hKcard` / `hWdvd` / `∃w∈W̄` が
まとめて移送**でき、Corollary 2 が `U/Z(U)` に当たって段 (2) が閉じる。

## 2026-08-02 (132): `t` の照合 — 欠けている 1 文を特定

`exists_conj_eq_triple` ((131)) で `Q,M,D` が揃った後、残るのは
`Setup M Q D t₁` と `Setup M Q D t₂` (同じ `M,Q,D`!) の `t` を合わせること。

書籍 p.133 の該当文:

> Once `H`, `Q` and `D` are matched, the two involutions differ by an element of `K` —
> both being involutions forces `t' = d t` with `d^t = d⁻¹` — and conjugating by `K`
> covers exactly those differences, because squaring is onto `K`.

⟹ 分解すると:

| 段 | 状態 |
|---|---|
| (i) `t₂ t₁ ∈ K₁` (= `t₂ = d t₁` with `d ∈ D`, `t₁ d t₁ = d⁻¹`) | ⚠ **これが欠けている 1 文** |
| (ii) `∃ e ∈ K, e⁻¹ t₁ e = d t₁` | ✅ `Hypothesis.exists_mem_K_conj_t_eq` ((110)) |
| (iii) `e ∈ K ≤ D ≤ M` による共役は `M`,`Q`,`D` を動かさない | 自明 (`Q ⊴ M`, `D` は自身を正規化) |

### ⚠ 次セッションはここから — (i) の証明

`t₁`, `t₂` はどちらも `L − M` の対合で、**同じ** `D = M ⊓ M^{t₁} = M ⊓ M^{t₂}`
(`Setup.D_eq_inf_map_conj`) を与える。ここから `t₂ t₁ ∈ D` と `t₁ (t₂t₁) t₁ = (t₂t₁)⁻¹`
を出すのが目標。

⚠ **有用な観察** (逆向きの依存): `g` が `M` を正規化して `g t₁ g⁻¹ = t₂` なら
`D₂ = M ⊓ M^{t₂} = g (M ⊓ M^{t₁}) g⁻¹ = g D₁ g⁻¹` が**自動**。つまり `t` を合わせれば
`D` は付いてくる。(131) で `D` を先に合わせたのは Schur-Zassenhaus が使えたからで、
`t` 側から攻める設計も可能 — どちらが短いかは (i) の難易度次第。

## 2026-08-02 (133): ⚠ 4 本のうち **3 本は `t` の照合を要しない**

(132) の `t` 照合に着手する前に依存を洗ったところ、移送したい 4 本のうち 3 本は
`H`,`Q`,`D` の対応だけで済むことが分かった。

| 移送したい主張 | 依存 | `t` が要るか |
|---|---|---|
| `∃ w ∈ W̄, w ≠ 1` | `W = D ⊓ C(Q₀)` (`W_eq_inf_centralizer_Q0`)、`Q₀ = {x ∈ H \| x²=1}` | **不要** |
| `hW1` (`1 < \|W̄\|`) | 同上 | **不要** |
| `hWdvd` (`\|W̄\| ∣ 2ᵐ+1`) | 同上 | **不要** |
| `hVW` (`V̄ = W̄`) | `V = D ⊓ C(t)` | ⚠ 要る |
| `hKcard` (`\|K̄\| = 2ᵐ-1`) | `K = {x ∈ D \| t x t = x⁻¹}` | ⚠ 要る |

⟹ **`exists_conj_eq_triple` ((131)) だけで `∃ w ∈ W̄, w ≠ 1` が移送でき、
`U/Z(U)` 内在版の Ch. I §3 Lemma 5 が 7/7 になる**。これが次セッションの最優先。

### ⚠ `t` の照合 (i) についての実測 — 追加仮説 `C_Q(D) = 1` が要る

(132) の (i) `t₂t₁ ∈ K₁` は、点集合で見ると「`t₁`,`t₂` が基点 `a` を**同じ点**へ送る」
ことと同値 (そのとき `t₂t₁` は `a` と `b` を固定するので `D` に入り、対合 2 つの積なので
`t₁` で反転される)。`D_i = Stab(a) ⊓ Stab(t_i·a)` なので、必要なのは

> `b ↦ Stab_M(b)` が `X − {a}` 上で単射

で、`Stab_M(b_q) = D^q` (`q ∈ Q` が `b` の座標) ゆえ **`N_Q(D) = 1`** と同値。
`N_Q(D) = C_Q(D)` は容易 (`[q,d] ∈ Q ⊓ D = 1`)。⟹ 追加仮説は **`C_Q(D) = ⊥`**。

⚠ **反例で確認済**: `A₅ ≅ PSL(2,4)`, `M = Stab(5) = A₄`, `Q = V₄`, `|D| = 3` で
`t₁ = (15)(23)`, `t₂ = (25)(34)` はどちらも `M` 外の対合だが `t₂t₁ = (12435)` は
位数 5 で `M` に入らない。このとき `D₂ = Stab({2,5}) ≠ Stab({1,5}) = D₁` で、
確かに `D` が違う。`t₂ = (15)(24)` なら `D₂ = D₁` で `t₂t₁ = (234) ∈ D₁` ✓。

`C_Q(D) = ⊥` は本適用では真 (`PSU(3,ℓ)` の torus は根群を固定点自由に近く動かす;
`q > 2` で `C_{Q₀}(D) = 1`) だが、`Setup` から出るかは未確認 — 次セッションで検討。

## 2026-08-02 (134): `Q₀`/`W` の共役移送 — `t` 抜きの経路が Lean に

(133) の実測を landing (`PSU3SectionFourIntrinsic.lean`, section `ConjMatch`):

* `map_Q0_of_conj` — `H` を合わせる共役は `Q₀` を合わせる (`Q₀ = {x ∈ H | x²=1}`)。
* `map_W_of_conj` — `H` と `D` を合わせる共役は `W` を合わせる
  (`W = D ⊓ C(Q₀)`, `W_eq_inf_centralizer_Q0`)。**`t` は不要**。
* `exists_ne_one_mem_W_of_conj` — したがって `1 ≠ w ∈ W` も移る。

### ⚠ 次セッションはここから — 2 つの仮説を同じ群に載せる配線

`exists_conj_eq_triple` と `map_W_of_conj` を繋ぐには、内在版と transported 版が
**同じ群の上**に無ければならない。現状:

* 内在: `intrinsicResidualQuotient` on `↥(residualImage X) ⧸ Z`
* transported: `residualQuotientHypothesis` on `↥(residual X) ⧸ Z`

⟹ `Hypothesis.ofMulEquivPullback` で transported 側を
`residualQuotientMulEquiv X : (↥(residual X) ⧸ Z) ≃* (↥(residualImage X) ⧸ Z)` に沿って
引き戻せばよい (点集合は `ULift (Unital ℓ)` のまま動かない)。

その後 `exists_conj_eq_triple` に食わせる 8 仮説:

| 仮説 | 内在版 | transported 版 |
|---|---|---|
| `IsPGroup 2 Q` | `isSuzuki2Group_Q_intrinsicResidualQuotient` の第 1 成分 | 標準モデル (`Q = standardRootSubgroup`) |
| `Odd \|D\|` | `Hypothesis.D_odd` (フィールド) | 同左 |
| `Even \|Q\|` | `Hypothesis.Q_even` (フィールド) | 同左 |
| `Q ≠ ⊥` | `\|Q̄\| = ℓ³ > 1` ((118)) | `\|Q\| = ℓ³ > 1` |

⟹ 揃えば `∃ w ∈ W̄, w ≠ 1` が出て **`U/Z(U)` 内在版の Lemma 5 が 7/7**。

## 2026-08-02 (135): 配線の設計判断 — `Setup.map` が要る

(134) の `map_W_of_mulEquiv` は任意の `φ : L ≃* L'` で使えるので、内在版と transported 版が
別の群に居ても `H`,`D` さえ対応すればよい。問題はその**対応を作る側**:
`Setup.exists_conj_eq_triple` ((131)) は**同じ群上の 2 つの `Setup`** を要求する。

⟹ transported 側の `Setup` を `residualQuotientMulEquiv` に沿って
`↥(residualImage X) ⧸ Z` へ移す必要がある。選択肢は 2 つ:

**(a) `Setup.map` を新設** (`RankOneBNPair.lean`) — `Setup M Q D t` と `φ : L ≃* L'` から
`Setup (M.map φ) (Q.map φ) (D.map φ) (φ t)`。9 フィールドの機械的な移送だが
`split` / `fact` は `∃!` を subtype の組で扱うので注意
(⚠ (113) の実測メモ: `∃!` を `obtain ⟨-, -, huniq⟩` で受けると証人ごと `huniq` が消える)。
自己完結でインスタンスの letI 舞踏が無い。**推奨**。

**(b) `Hypothesis.ofMulEquivPullback` を使う** — 既存だが、`residualQuotientHypothesis`
自体が `letI := MulAction.compHom … residualQuotientEquiv` の下に居るので
letI が二重になり、(125) で踏んだ「別インスタンス」問題を再び踏みやすい。

### ⚠ 次セッションの手順

1. `Setup.map` を `RankOneBNPair.lean` に追加 ((a))。
2. `(hyp.residualQuotientHypothesis details).rankOneSetup.map (residualQuotientMulEquiv X)`
   と `hyp.setup_residualQuotient …` を `exists_conj_eq_triple` に食わせる
   (8 仮説は (134) の表のとおり既存資産で埋まる)。
3. 得た `c` と `residualQuotientMulEquiv` を合成した `φ` を
   `exists_ne_one_mem_W_of_mulEquiv` に食わせて **`∃ w ∈ W̄, w ≠ 1`**。
4. ⟹ `U/Z(U)` 内在版の Ch. I §3 Lemma 5 が **7/7**、`LemmaFiveSetup` /
   `QuotientFieldModel` / `IsStandardModel` が出て、残るは `hVW` / `hKcard` (= `t` の照合、
   追加仮説 `C_Q(D) = ⊥` が要る ((133)))。

## 2026-08-02 (136): 🎯 `U/Z(U)` 内在版の Lemma 5 入力が **7/7**

* `exists_mulEquiv_match_residualQuotient` — 内在版と transported 版の標準仮説を
  `H`,`D` について合わせる同型。`Setup.map` ((135) の (a)) で transported 側を
  `residualImage` へ移し、`Setup.exists_conj_eq_triple` ((131)) の共役と合成。
  8 個の数値仮説はすべて既存資産で埋まった。
* `exists_ne_one_mem_W_intrinsicResidualQuotient` — それを
  `exists_ne_one_mem_W_of_mulEquiv` ((134)) に食わせるだけ。
  ⚠ `W = D ⊓ C(Q₀)` は `t` に依存しないので **distinguished involution の照合は不要**
  ((133) の観察が効いた)。

| Lemma 5 の入力 | 内在版 |
|---|---|
| `\|Q̄₀\| = 2ⁿ` / `\|Q̄\| = \|Q̄₀\|³` / `n ≠ 0` | ✅ (118) |
| `Q̄` が Suzuki 2-群 | ✅ (118) |
| `TheoremAInductionBelow` | ✅ (118) ※ ULift 版 |
| `\|s̄ t̄\| = 3` | ✅ (120) |
| `∃ w ∈ W̄, w ≠ 1` | ✅ **今回** |

### ⚠ 次セッションはここから — universe の帳尻合わせ

`lemmaFiveSetup_of_orderThree_of_mem_W` を当てるとき、`ihq` だけは
**`Ω̄` が `Type v` の版** (`intrinsicResidualQuotientULift`, (118)) でないと型が合わない
(他の 6 入力は `intrinsicResidualQuotient` について証明済)。⟹ 両者の間で
`Q0` / `W` / `distinguishedInvolution` が一致することを示す必要がある。

**推奨**: 汎用補題 3 本を足す (`φ = MulEquiv.refl` の特殊化 + 一意性):
* `Q0_eq_of_H_eq` — `H` が同じなら `Q0` も同じ (`map_Q0_of_mulEquiv` + `Subgroup.map_id`)
* `W_eq_of_H_D_eq` — `H`,`D` が同じなら `W` も同じ (`map_W_of_mulEquiv` + 同上)
* `distinguishedInvolution_eq_of_H_Q_t_eq` — `H`,`Q`,`t` が同じなら `s` も同じ
  (`eq_distinguishedPair_of_structure` の一意性)

`ofRankOneSetupOfEquiv_{H,Q,D,t}` ((118)) が「点集合の貼り替えは 4 フィールドを動かさない」
と言っているので、上 3 本があれば 6 入力がそのまま ULift 版へ移り、Lemma 5 →
`QuotientFieldModel` → `exists_standardModel` → `corollaryTwo_of_standardModel` と繋がる
(残りは `hVW` / `hKcard` = `t` の照合、追加仮説 `C_Q(D) = ⊥` ((133)))。

## 2026-08-02 (137): `Q₀`/`W`/`s` の点集合非依存が landing — 次は ULift 版への移送

`Q0_eq_of_H_eq` / `W_eq_of_H_D_eq` / `distinguishedInvolution_eq_of_eq`
(`PSU3SectionFourIntrinsic.lean`, section `SameGroup`)。同じ群上の 2 つの標準仮説で
`H`,`Q`,`D`,`t` が一致すれば `Q0`,`W`,`s` も一致する。

### ⚠ 次セッションはここから — 6 入力を ULift 版へ

`intrinsicResidualQuotientULift` ((118)) と `intrinsicResidualQuotient` ((117)) は
`ofRankOneSetupOfEquiv_{H,Q,D,t}` により 4 フィールドが一致するので、上の 3 本で
`Q0`,`W`,`s` も一致し、`|Q̄₀|` / `|Q̄|` / `|s̄t̄|=3` / Suzuki 2-群 / `∃w∈W̄` が
そのまま移る。

⚠ **実務上の注意**: ULift 版の型は
`letI := Hypothesis.rankOneSetupAction ((hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm)`
の下にあるので、各 statement にこの `letI` を書く必要がある (長い)。
**先に `abbrev` で `ε` を切り出す**と読みやすくなる:

```
noncomputable abbrev intrinsicPointEquivULift (details) (hXD) (htX) (hCQ) (hZD) :=
  (hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm
```

その後:
1. 4 フィールドの一致 (`ofRankOneSetupOfEquiv_*` を `letI` 付きで言い直す)
2. `Q0`/`W`/`s` の一致 (section `SameGroup` の 3 本)
3. 6 入力を移送
4. `lemmaFiveSetup_of_orderThree_of_mem_W` → `nonempty_quotientFieldModel_of_orderThree`
   → `exists_standardModel` → `IsStandardModel`
5. 残り `hVW` / `hKcard` (= `t` の照合、追加仮説 `C_Q(D) = ⊥` ((133))) を埋めれば
   `corollaryTwo_of_standardModel` が当たり、(119) の 2 転送と合わせて**段 (2) が閉じる**。

## 2026-08-02 (138): 🎯 §3 の Proposition が `U/Z(U)` の**内在**仮説で成立

`nonempty_standingData_intrinsicResidualQuotient` (Lemma 5 + `QuotientFieldModel`) と
`exists_isStandardModel_intrinsicResidualQuotient` (`IsStandardModel`)。

⟹ **書籍の「§2 と §3 を `U` について走らせる」(p.133) が形式化された**。得られるモデルは
`H`,`Q`,`D`,`t` が `U ∩ H`, `U ∩ Q`, `U ∩ D`, `t` の像である仮説についてのものなので、
そこで制約される写像は書籍の `f₁`, `h₁` そのもの。

配線の要点: 6 入力は `intrinsicResidualQuotient` について証明済で、点集合を貼り替えた
ULift 版へ `intrinsicResidualQuotientULift_{H,Q,D,t}` + section `SameGroup` の 3 本
(`Q0`/`W`/`s` は点集合に依らない) で移した。帰納法仮説だけ universe の都合で ULift 版。

### 段 (2) の残り

| ピース | 状態 |
|---|---|
| `G ← U` 転送 | ✅ (119) |
| `U ← U/Z(U)` 転送 | ✅ (119) |
| §3 の Proposition (`IsStandardModel`) on `U/Z(U)` 内在 | ✅ **今回** |
| `corollaryTwo_of_standardModel` の `hVW` / `hKcard` | ⚠ 残り |

### ⚠ 次セッションはここから

`hVW` は `V̄ = D̄ ⊓ C(t̄)` なので `t` の照合が要る ((132)(133))。追加仮説は
**`C_{Q̄}(D̄) = ⊥`** で、これは `exists_conj_eq_triple` が `Q` も合わせている
(`hQc`, (131) では `_hQc` として捨てているので拾い直す) ので transported 側の
`C_{Q_tr}(D_tr) = ⊥` から移送できる。⟹ **標準モデルで
`C_{standardRootSubgroup}(psuTorusHom.range) = 1` を示す**のが実体
(`RootGroupStructure` の `psuTorusScale_fixedPointFree_of_torusWeight_ne_one`
(`Simplicity.lean:42`) が近い — torus の非自明元は根群に固定点を持たない)。

⚠ `PSU3SectionFourIntrinsic.lean` は **1330 行**。1500 に近いので次に大きく足す前に
分割を検討する (`ConjMatch`/`SameGroup`/`EquivMatch` の汎用部分を別 leaf へ、が自然)。

## 2026-08-02 (139): leaf 分割 + `C_Q(D) = ⊥` の材料を実測

`PSU3SectionFourIntrinsic.lean` が 1330 行になったので、`Q₀`/`W`/`s` の決定性補題 6 本を
**`HypothesisFieldMatching.lean`** (118 行) へ切り出した (leaf は 1252 行に)。
内容は §4 固有でなく Part II の標準仮説一般の事実なので独立 leaf が適切。

### ⚠ 次セッションはここから — `C_{Q̄}(D̄) = ⊥`

`t` の照合 ((132)(133)) の追加仮説。materials は全部 `ProjectiveUnitary` に在る:

* 標準モデルの `Q = standardRootSubgroup n`, `D = (psuTorusHom n).range`
  (`StandardModelHypothesis.lean:154`)。
* `psuTorusScale_fixedPointFree_of_torusWeight_ne_one` (`Simplicity.lean:42`) —
  norm weight が非自明な torus 元は根群に**固定点を持たない**。
* `exists_psuTorus_weight_ne_one` (`Simplicity.lean:79`) — `1 < n` ならそういう元が在る。
  ⚠ **`private`** なので公開する必要がある (または再証明)。

⟹ 手順:
1. `exists_psuTorus_weight_ne_one` の `private` を外す (または
   `center_...`-style の公開補題を `Simplicity.lean` に足す)。
2. 標準モデルで `C_{standardRootSubgroup n}((psuTorusHom n).range) = ⊥`。
3. `exists_conj_eq_triple` の `hQc` (現在 (131) の呼び出しで `_hQc` として捨てている)
   を拾い直し、`hDc` と合わせて `C_{Q̄}(D̄) = ⊥` を移送。
4. `t` の照合 (i) `t₂t₁ ∈ K₁` ((132)) を証明 →
   `exists_mem_K_conj_t_eq` ((110)) で四つ組が揃う。
5. ⟹ `hVW` / `hKcard` が transported 側から移送でき、
   `corollaryTwo_of_standardModel` が当たって**段 (2) が閉じる**。

## 2026-08-02 (140): 🎯 `t` の照合の**数学的な核が片付いた** — 残りは組み立て

* `rootHom_range_inf_centralizer_psuTorus_eq_bot` (`Simplicity.lean`) — 標準モデルで
  `C_Q(D) = 1` (torus の非自明 weight 元が根群に固定点を持たないこと + torus-根交換子)。
  ⚠ `exists_psuTorus_weight_ne_one` の `private` を外した。
* `Setup.mem_D_of_map_conj_eq` — `C_Q(D) = 1` ⟹ **`N_M(D) = D`**。
* `Setup.mul_mem_K_of_setup` — 同じ `M,Q,D` の 2 setup で **`t₂t₁ ∈ K₁`**。

⟹ (132) が「欠けている 1 文」とした (i) が landing。**段 (2) に残る未証明の数学はゼロ**で、
あとは組み立てのみ。

### ⚠ 次セッションはここから — 四つ組照合の組み立て

1. `exists_mulEquiv_match_residualQuotient` ((136)) で `H,Q,D` を合わせる `φ` を取る。
2. transported 仮説を `φ` で押し出した setup (`Setup.map`) と内在 setup に
   `Setup.mul_mem_K_of_setup` を当てて `d := φ(t_tr) · t̄ ∈ K̄` を得る。
   ⚠ `C_{Q̄}(D̄) = ⊥` は `hQc`/`hDc` (=`exists_conj_eq_triple` の出力、(131) では
   `_hQc` として捨てているので拾い直す) + 標準モデルの上記補題から移送。
3. `Hypothesis.exists_mem_K_conj_t_eq` ((110)) で `e ∈ K̄` を取り、
   `e⁻¹ t̄ e = d t̄ = φ(t_tr)` (t̄ は対合)。
4. `e ∈ K̄ ≤ D̄ ≤ M̄` なので conj `e` は `M̄`,`Q̄` (`Q ⊴ M`),`D̄` を動かさない
   ⟹ `ψ := φ` と conj `e` の合成が**四つ組**を合わせる。
5. `V`,`K` は `D`,`t` から定義されるので `ψ` で対応 ⟹ transported 側の
   `residualQuotientHypothesis_V_eq_W` などから **`hVW` / `hKcard` を移送** ⟹
   `corollaryTwo_of_standardModel` が当たり、(119) の 2 転送と合わせて**段 (2) が閉じる**。

## 2026-08-02 (141): 🎯 四つ組の照合が完成 — `hVW` も出た、残るは `hKcard` 1 本

* `exists_mulEquiv_match_residualQuotient_t` — `U/Z(U)` 上の内在仮説と transported 仮説を
  **`H`,`Q`,`D`,`t` の 4 つすべて**で合わせる同型。
  - `H,Q,D` は (136) の `φ`。
  - `t` は `Setup.mul_mem_K_of_setup` ((140)) で差が `K̄` に入ることを見て、
    `exists_mem_K_conj_t_eq` ((110)) で共役として実現。
  - conj `e` (`e ∈ K̄ ≤ D̄ ≤ M̄`) は `H,Q,D` を動かさない。
  - 追加仮説 `C_{Q̄}(D̄) = ⊥` は標準モデルから 3 段で移送済 ((140) 追記)。
* `map_V_of_mulEquiv` / `map_K_of_mulEquiv` (`HypothesisFieldMatching.lean`) —
  `V = D ⊓ C({t})`, `K = ⟨{x ∈ D | txt = x⁻¹}⟩` なので `D`,`t` で決まる。
* `V_eq_W_intrinsicResidualQuotient` — ⟹ **`hVW` が内在版で成立**。

### `corollaryTwo_of_standardModel` の引数 (最終)

| 引数 | 状態 |
|---|---|
| `H` (=`IsFGH`) / `hC2` / `sfive` / `M` / `hZc` / `hmu` / `hm` / `hQ0card` / `hVW` | ✅ |
| bilinear package (`IsStandardModel` の分解) | ✅ ((138)) |
| `hW1` / `hWdvd` / `hhW` | ✅ 導出可 ((133)(136)) |
| **`hKcard` (`\|actualKActor\| = 2ᵐ-1`)** | ⚠ **残り 1 本** |

### ⚠ 次セッションはここから — `hKcard`

`actualKActor = conjQByK.range : Subgroup (MulAut ↥Q)` (`ActualKActor.lean:117`)。
`ψ` は `Q` と `K` を合わせる (`map_K_of_mulEquiv` 今回) ので、`MulAut ↥Q_tr ≃* MulAut ↥Q̄`
(`ψ` の `Q` への制限が誘導する) の下で `conjQByK` の像が対応する。⟹ 位数が一致。

実装候補:
1. `MulEquiv.subgroupMap ψ Q_tr : ↥Q_tr ≃* ↥Q̄` (制限) を取る。
2. `MulAut.congr` (= `MulEquiv.autCongr`?) で `MulAut ↥Q_tr ≃* MulAut ↥Q̄`。⚠ mathlib の
   正確な名前を実測すること。
3. `conjQByK` の可換性 (`ψ` で共役してから制限 = 制限してから共役) を示し、range の対応を出す。
4. transported 側の `|actualKActor| = 2ᵐ-1` を実測 (標準モデルで `|K| = ℓ-1` かつ
   `K` が `Q` に忠実に作用、が実体)。

⟹ これが済めば `corollaryTwo_of_standardModel` が当たり、(119) の 2 転送と合わせて
**段 (2) が完全に閉じる**。

## 2026-08-02 (142): `hKcard` は移送不要だった — `corollaryTwo_of_standardModel` の引数が出揃った

⚠ `PSU3OrbitCount.card_actualKActor_eq` は
`(s : LemmaFiveSetup m) (M : QuotientFieldModel m) (hm) (hQ0card)` から
`|actualKActor| = 2ᵐ-1` を出す**汎用**補題だった。(138) で得ている `sfive`/`Mq` を
食わせるだけで済み、`MulAut` の congruence 経由の移送 ((141) で見積もった経路) は不要。
`exists_isStandardModel_intrinsicResidualQuotient` の結論に同梱した。

### ⚠ 新たに判明した制約 — `hcard : 5 ≤ |F|` は `ℓ ≥ 8` を意味する

`corollaryTwo_of_standardModel` / `_of_sectionThree` は
`hcard : 5 ≤ Nat.card ↥(frobFixedSubfield M.E 2 m)` を取る
(`PSU3CorollaryTwo.lean:479, 575`; `stepThree` / `stepThree_model` が消費)。
`|frobFixedSubfield| = 2ᵐ` なので **`2ᵐ ≥ 5` ⟺ `m ≥ 3` ⟺ `ℓ ≥ 8`**。

一方 §4 が持っているのは `data.one_lt_n : 1 < n`、すなわち `ℓ ≥ 4` だけ。
⟹ **`ℓ = 4` の場合の扱いが未確認**。

次セッションはまずここを実測すること:
1. 書籍 Ch. IV / Ch. III §3 に `q > 4` 相当の条件があるか (p.120-134 を PDF で確認)。
2. `stepThree` が `hcard` を何に使っているか (`PSU3CorollaryTwo.lean` の該当箇所) —
   `5 ≤ |F|` が本当に必要か、それとも `4 ≤ |F|` で足りるのに強く取っているだけか
   ([[repo-stronger-hypothesis-is-specialization-not-gap]] の型)。
3. 本当に `ℓ ≥ 8` が要るなら、`ℓ = 4` を別途排除する議論が §4 のどこかにあるはず。

⚠ この判断が済むまで段 (2) の最終組み立て (`corollaryTwo_of_standardModel` の適用) は
保留。それ以外の引数はすべて内在版で揃っている。

### (142) 追記: `hcard` は**特殊化債務**だった (書籍の仮説は「`θ` の位数が奇」)

`PSU3SectionThree.stepThree` (803 行) の docstring が明記している:

> `hcard` is the book's "`|F| ≥ 8`, since `θ` is of odd order". It is carried as a
> hypothesis because **the odd order of `θ` belongs to the type-`B` datum, which this
> development does not track**; without it the count genuinely fails — over `𝐅₄` the
> Frobenius satisfies `X + X^θ = 1` on both points outside `𝐅₂`.

⟹ 書籍の本当の仮説は「**`θ` の位数が奇**」で、`|F| ≥ 8` はそれが `𝐅₄` を排除することを
使った proxy。`𝐅₄` (= `ℓ = 4`) では `θ` = Frobenius の位数が 2 (偶) なので書籍の仮説では
除かれるが、repo の `hcard` では `ℓ = 4` が丸ごと落ちる。

これは [[repo-stronger-hypothesis-is-specialization-not-gap]] の型 —
**書籍の gap ではなく repo 側の債務**。選択肢:

**(a) `θ` の奇位数を追跡して `hcard` を弱める** — §3 の type-`B` datum に
`θ` の位数情報を持たせる。正攻法だが §3 の refactor。
**(b) `ℓ = 4` を別途排除する** — §4 に `ℓ > 4` を出す議論があるか要確認
(⚠ `PSU(3,4)` は存在するので、あるとすれば §4 固有の理由)。

⚠ どちらにせよ **段 (2) の最終組み立ての前に決着が要る**。それ以外の引数
(`IsFGH`/`hC2`/`sfive`/`M`/`hZc`/`hmu`/`hm`/`hQ0card`/`hVW`/`hKcard`/bilinear package/
`hW1`/`hWdvd`/`hhW`) はすべて `U/Z(U)` 内在版で揃っている。

次セッションはまず (b) を実測 (書籍 p.122-134 と §4 の repo ファイルを `ℓ = 4` /
`q > 4` で grep)、無ければ (a) の規模を見積もる。

### (143) `hcard` の特殊化債務を返済 — 書籍どおり「θ が奇位数」へ (段 (2) の `ℓ = 4` 障害を解消)

(142) で「(a) θ の奇位数を追跡 / (b) ℓ = 4 を別途排除」の 2 択と書いたが、**(a) を実施して landing**。
併せて (142) の記述を 2 点訂正する。

**訂正 1**: `corollaryTwo_of_standardModel` は `hcard` を**取らない**。取るのは合成版の
`corollaryTwo_of_sectionThree` だけ (中で `stepThree_model` → `stepThree` を走らせるため)。

**訂正 2**: 書籍 p.130 の原文 (実測) は

> Therefore, `c = X + X^θ` is independent of `X` for `X ∈ F − {0, α^{2τ}}`.
> **If `θ ≠ 1`, then `|F| > 8` since `θ` is of odd order**, and so there are elements
> `X, Y ∈ F` such that `{X,Y,X+Y} ∩ {0,α^{2τ}} = ∅` and `c = X+Y+(X+Y)^θ = c+c = 0`.

つまり `|F| > 8` は**仮説でなく θ の奇位数からの帰結**。`𝐅₄` の Frobenius は位数 2 ゆえ
書籍の仮説から落ちる。⟹ repo の `hcard : 5 ≤ |F|` は proxy であり特殊化債務。

**実装** (commits `3e6b4e6e5`, `927d46475`):

* `OddOrder/Algebra/FixedPointsGalois.lean`
  * `orderOf_dvd_of_card_eq_pow` — Artin の補題を `B = ⟨θ⟩` に適用: `[F : F^B] = |B|`
    かつ `|F| = |F^B|^{orderOf θ}`、両者 `p` 冪ゆえ **`orderOf θ ∣ m`**。
  * `three_le_of_odd_orderOf` — `|E| = p^{m·2}`、`θ ≠ 1` が奇位数 ⟹ `orderOf θ` は
    `2m` の奇約数 (> 1) ⟹ `m` の約数 ⟹ **`3 ≤ m`** (= 書籍の `|F| ≥ 8`)。
* `PSU3FieldArithmetic.lean` — `exists_ne_zero_ne` (3 元あれば `{0,z}` の外が取れる)。
* `PSU3SectionThree.lean`
  * `stepThree_star_all` — 旧 `stepThree` の本体を `(∗)` 止まりで切り出し
    (`∃ z ∈ F, ∀ X ∈ F, X ≠ 0 → X ≠ z → α² + w² + w(X + X^θ) = 0`)。
    補助 `theta_mem_frobFixed` / `sigma_symm_mem_frobFixed` / `theta_injective` /
    `centerCoord_div_mem_frobFixed` も切り出し。
  * `stepThree` — `5 ≤ |F|` 版 (従来の数え上げ)。入口として保持。
  * **`stepThree_of_odd`** — 書籍版。`3 ≤ |F|` + `Odd (orderOf (τ.trans σ.symm))`。
    `θ ≠ 1` なら `three_le_of_odd_orderOf` で `|F| ≥ 8` を出して `stepThree`、
    `θ = 1` なら (∗) の括弧が標数 2 で消えて `α² = w²` のみ (数え上げ不要)。
* `PSU3CorollaryTwo.lean` — `stepThree_model` / `corollaryTwo_of_sectionThree` の
  `hcard : 5 ≤ |F|` を `3 ≤ |F|` + `hodd` に in-place で差し替え (外部呼び出し無し)。

**段 (2) への影響**: `ℓ = 4` 障害は**消えた**。内在版 `U/Z(U)` は `ℓ = 2ⁿ`, `n ≥ 2` ゆえ
`3 ≤ |F| = 2ⁿ` は自明。残るのは `hodd` の供給だが、これは **σ, τ (type-`B` scaling pair) を
`U/Z(U)` について供給する仕事の一部**であり、cardinality 制約ではなくなった
(σ, τ の供給自体は §3 の type-`B` 入力として元から必要)。

**次**: 段 (2) の残りは (i) `U/Z(U)` の σ, τ + `hodd`、(ii) §2 の base pair
`f(ω₀) = (ω₀ω₀²)^{ζ₀}`、(iii) `IsStandardModel` の 11 節を `corollaryTwo_of_sectionThree`
の引数形へ展開。(iii) は `exists_isStandardModel_intrinsicResidualQuotient` から機械的。

### (144) `corollaryTwo_of_isStandardModel` — 段 (2) の残り供給物が 2 件に確定

`corollaryTwo_of_sectionThree` は Ch. III §3 Proposition を 11 節ばらばらに取るので、
`IsStandardModel` (同じものを束ねた述語) から直接入る版を追加 (`5f0abd00d`)。
`hpair` は「モデルが提示した `ι`・`d` について type-`B` scaling pair が存在する」形
(`ι`・`d` はモデル内で ∃ 束縛なので、それらを ∀ で受ける以外に書きようがない)。
`hodd` はこの `hpair` の中に入る。

**段 (2) の引数表 (内在版 `U/Z(U)`)**:

| 引数 | 状態 |
|---|---|
| `H : IsFGH` | ✓ `exists_fgh_residual_eq` + `fgh_map_residualQuotient` |
| `hC2` (braid) | ✓ |
| `sfive`, `Mq`, `x₀`, `hmodel` | ✓ `exists_isStandardModel_intrinsicResidualQuotient` |
| `hZc` | ✓ `center_Q_eq_Q0_intrinsicResidualQuotient` |
| `hmu`, `hVW` | ✓ (`V_eq_W_intrinsicResidualQuotient`) |
| `hm`, `hQ0card` | ✓ `natCard_Q0_intrinsicResidualQuotient` |
| `hcard : 3 ≤ |F|` | ✓ 自明 (`|F| = 2ⁿ`, `n ≥ 2`) — **(143) で `5 ≤` から緩和済** |
| `hKcard` | ✓ (`exists_isStandardModel_…` が同時に返す) |
| `ζ ∈ W^#` | ✓ `exists_ne_one_mem_W_intrinsicResidualQuotient` |
| `hWdvd`, `hW1`, `hfQ`, `hhW` | ○ 既存部品から出るはず (未接続) |
| **`hpair` (type-`B` scaling pair + `hodd`)** | **✗ 未** |
| **§2 の base pair `f(ω₀) = (ω₀ω₀²)^{ζ₀}`** | **✗ 未** |

⟹ 残る本物の仕事は**「§2 を `U` について走らせる」の 2 件だけ**。これは書籍 step (2) の
"run §2 and §3 relative to `U`" の §2 側そのもの。§3 側 (Proposition + Corollary 2 の
経路) は揃った。

### (145) `stepNine` が base pair を出す — 残債は `hsq` (§2 (20)) と `hpair` の 2 つに確定

(144) の「§2 の base pair」を実測したところ、**大半は既にある**:

* `PSU3OrbitCount.stepNine` (§2 (9), 書籍 p.124-125) が
  `∃ ω' ∈ Q, ω' ∉ Q₀ ∧ ∃ y ∈ Q₀, y ≠ 1 ∧ f ω' = ζ⁻¹(ω' y)ζ` を**出す** — これが
  書籍 p.125 の「ω_i は f(ω_i) = (ω_i y_i)^ζ となるよう選んでよい」の正規化。
* 欠けるのは **`ω'² = y`** だけ。これは §2 (20) (`f_eq_conj_inv_of_stepTwenty_chain` の
  第一結論) で、その docstring 曰く「ω_1,…,ω_n が相異なる `KW` 軌道にあるという族は
  形式化されていないので `ω_i = ω_k` の一致は仮定」。⟹ repo 側で未閉の §2 項目。

`corollaryTwo_of_isStandardModel_of_normalization` (`8a81d822e`) は `stepNine` を内部で
呼び、`hsq : ∀ ω' ∈ Q, ω' ∉ Q₀ → ∀ y ∈ Q₀, f ω' = ζ₀⁻¹(ω' y)ζ₀ → ω'² = y` のみを取る。

**⟹ 段 (2) の残債 = `hsq` (§2 (20)) と `hpair` (type-`B` scaling pair + 奇位数) の 2 本**
(いずれも書籍 step (2) の "run §2 relative to `U`" 側)。§3 側は完備。

次セッションの着手順 (上流優先):
1. `hpair` — `U/Z(U)` の type-`B` scaling pair。§3 の type-`B` 入力を内在版へ移す仕事。
2. `hsq` — §2 (20)。`f_eq_conj_inv_of_stepTwenty_chain` の未形式化前提
   (相異なる `KW` 軌道の代表族) を先に形式化するのが本筋。

### (146) ⚠ 自己訂正: 奇位数仮説は `E` 上でなく `F` 上に置く (E 上だと充足不能)

(143) で入れた `hodd : Odd (orderOf (τ.trans σ.symm))` (= `E = 𝐅_{q²}` 上の
`θ = σ⁻¹τ` の位数) は**実際の状況で充足できない**。commit `0e97a301c` で訂正。

**理由** (実測で確定):
* `hWinv : σ(μ(1,v))·τ(μ(1,v)) = 1` ⟹ `τ(x) = σ(x)⁻¹` on `μ(W)` ⟹
  `θ(x) = σ.symm(σ(x)⁻¹) = x⁻¹`、つまり **`θ` は `μ(W)` を反転する**。
* `QuadraticFrobenius.qFrobenius_eq_inv_of_pow_succ_eq_one` より `q`-Frobenius `σ₀` も
  norm-one 部分群を反転する。⟹ `θ = σ₀` がありうる (**位数 2 = 偶**)。
* しかも `F = fixedSet σ₀` なので `σ₀|_F = id` で、§3 (3) の結論 `θ|_F = 1` と完全に整合。

**書籍の `θ` は `F` 上の自己同型** — type-`B` datum が持つ `TypeBData.phi : RingAut F`
(`phi_orderOf_odd : Odd (orderOf phi)` を**構造フィールドとして持つ**)。よって仮説も
`θ|_F` に置くのが正しい転写で、これなら `θ = σ₀` のケースは `θF = 1` (位数 1 = 奇) として
第一分岐に入る。

**訂正後の interface**: `(θF : RingAut ↥F)` + `(hθF : (θF a : E) = σ.symm (τ a))` +
`(hodd : Odd (orderOf θF))`。`RingAut.three_le_of_odd_orderOf` も `Nat.card F = p ^ m`
版に戻した (`p^{m·2}` 版は不要になり、奇約数の coprime 段も落ちて証明が短くなった)。

**教訓**: 「教科書の仮説をそのまま転写」でも、**どの体の上の自己同型か**を取り違えると
充足不能な仮説になる。`hWinv` のような既存の関係式から `θ` の実際の姿を計算して
sanity check すること (ここでは「θ は μ(W) を反転する」から `θ = σ₀` の可能性が出た)。

### (147) `hpair` の現状 — producer は在る、欠けるのは奇位数だけ

* **producer は既存**: `CenterFieldExponent.exists_scalingPair_of_lemmaFiveSetup`
  (`LemmaFiveSetup` + `QuotientFieldModel` から `∃ d σ τ, hscale ∧ hWinv`)。
* 欠けるのは **(i) `θF` の奇位数**、**(ii) その `d` がモデルの `d` と一致すること**。
* (i) の出所は `TypeBData.phi_orderOf_odd`。`Q` が type B であること自体は
  `TypeBFromW.isTypeB_Q_of_orderThree_of_mem_W` が出す。⟹ **`exists_scalingPair_…` の
  `σ, τ` の `F` 上の制限を type-`B` の `phi` と同定する**のが次の仕事。
  書籍 p.121 の「`{μ|_F, ν|_F} = {1_F, θ}`」がまさにこの同定。
* `QuadraticFrobenius.odd_orderOf_or_odd_orderOf_mul_qFrobenius` (`45a1fc5ba`) は
  「`E` への持ち上げのうち一方が奇位数」という正しい一般事実だが、上記のとおり
  §3 (3) にはこの向きは要らない (F 上で完結する)。誤解を招く docstring は訂正済。

### (148) `hpair` の奇位数を出す具体経路 (次セッション着手点)

書籍 p.121:

> if `λ_{μν} ≠ 0`, then **`a^μ a^ν = a a^θ` for `a ∈ F`, whence `{μ|_F, ν|_F} = {1_F, θ}`**

この「2 つのペアが `F` 上で同じ積写像を与えるなら、順序を除いて一致する」は
**`FrobeniusExponentPairs.restrict_pair_eq_of_mul_eq_on_frobFixed` が既に持っている**
(`E` の Frobenius 冪ペアは `F` 上で誘導する積写像により順序を除き決まる)。

⟹ 経路:
1. `TypeBFromW.isTypeB_Q_of_orderThree_of_mem_W` で `Q` が type B ⟹
   `TypeBData ↥Q` の `phi : RingAut F'` と **`phi_orderOf_odd`** (構造フィールド)。
2. type-`B` の平方写像 `x ↦ x·phi(x)` (+ ε 項) が中心の quadratic map `χ` と一致する
   ことから、ペア `(1_F, phi)` も `χ(a x) = a·phi(a)·χ(x)` を満たす。
3. `exists_scalingPair_of_lemmaFiveSetup` の `(σ, τ)` は `σ(a)τ(a) = a^d` on `μ(K)`。
   `hKcard : |K| = 2^m − 1` と `M.mu` 単射より **`μ(K) = F^×`** なので `F` 全体で成立。
4. 2 と 3 の積写像が一致 ⟹ `restrict_pair_eq_of_mul_eq_on_frobFixed` で
   `{σ|_F, τ|_F} = {1_F, phi}` ⟹ `θ|_F = σ|_F⁻¹τ|_F` は `phi` か `phi⁻¹`。
   どちらも奇位数 ⟹ **`hodd` が出る**。

⚠ 障害になりうる点: `TypeBData` の体 `F'` と `frobFixedSubfield M.E 2 m` の同定
(どちらも位数 `2^m` の体なので `FiniteField.ringEquivOfCardEq` で移送できるが、
`phi` の移送先が `M.E` 側の何と一致するかを追う必要がある)。
`LemmaFiveSetup` は `phi` を持たず `isplit` (同型な 2 成分分解) しか持たないので、
type-B 認識を通す必要がある。

**次セッションはここから**。

### (149) `hodd` を「指数 `d` の形」1 文に還元 — 残りは type-`B` transport のみ

(148) の経路を実装。commits `8c23b22dd`, `9701282c1`。

**`OddOrder/Algebra/FrobeniusExponentPairs.lean`**:
* `odd_orderOf_inv_mul_of_mul_eq_mul_one` — `F` 上で `σ(a)τ(a) = a·φ(a)` なら
  `σ⁻¹τ ∈ {φ, φ⁻¹}` ⟹ `φ` の奇位数を継承。既存 `frobIndex_pair_eq_of_pow_mul_eq` で
  指数の非順序対を取り、Frobenius の位数 `n` で `ZMod n` 合同を自己同型の等式に戻す。
* `restrictToFrobFixed` — `E ≃+* E` の `F` への制限 (well-defined は
  `map_mem_frobFixedSubfield`、全射は有限性)。`coe_restrictToFrobFixed` と
  **`coe_restrictToFrobFixed_inv_mul`** (= `stepThree_of_odd` の `hθF` そのもの)。
* `odd_orderOf_restrictToFrobFixed_inv_mul` — `E` のペア版。

**`PSU3SectionThree.lean`**:
* `odd_orderOf_scalingPair_restrict` — `exists_scalingPair_of_lemmaFiveSetup` の
  `(σ, τ)` (μ(K) 上で `σ(a)τ(a) = a^d`) と `exists_actualKActor_mu_eq` (`μ(K) = F^×`)
  を繋ぎ、**`hshape : ∀ a ∈ F^×, a^d = a·φ(a)`** さえあれば `hodd` が出る形にした。

⟹ **`hpair` の残債は `hshape` 1 本** = 「モデルの指数 `d` が type-`B` の形を持つ」。
出所は `TypeBData.phi` + `phi_orderOf_odd` (`isTypeB_Q_of_orderThree_of_mem_W` が
`IsTypeB ↥Q` を出す) で、必要なのは **type-`B` モデルの平方写像と `QuotientFieldModel` の
中心 quadratic map `χ` を同じ座標で見る transport**:

* `TypeBData ↥Q` は `equivModel : ↥Q ≃* TypeBModel phi ε` を持ち、平方写像は
  `(a,b) ↦ a·phi(a) + ε·a·phi(b) + b·phi(b)` (`typeBQuadraticMap`)。
* `QuotientFieldModel` 側は `M.coord : Additive (Q/Z(Q)) ≃+ E`、`ι : Additive Z(Q) ≃+ F`、
  `χ` の scaling が `χ(μ(k)x) = μ(k)^d χ(x)`。
* 両者は同じ平方写像の別座標。⟹ `TypeBData` の体 (位数 `2^parameter`) と
  `frobFixedSubfield M.E 2 m` を `FiniteField.ringEquivOfCardEq` で同定し、
  `phi` を移送して `hshape` を出す。

**次セッションはこの transport から**。`LemmaFiveSetup` は `phi` を持たず `isplit` のみ
なので `isTypeB_Q_of_orderThree_of_mem_W` を通す必要がある点に注意。

### (150) type-`B` transport の実態 — 必要な関係式は認識定理の**内部に既にある**

`hshape : ∀ a ∈ F^×, a^d = a·φ(a)` の出所を実測した結果、**新規理論は要らない**ことが判明。
必要なのは Higman 認識定理の中間データを外に出すこと。

**(a) 橋そのものは 3 行** (commit `b6dd30efc`):
`Suzuki2Groups.typeBQuadraticMap_smul` — type-`B` の平方写像
`(a,b) ↦ a·φ(a) + ε·a·φ(b) + b·φ(b)` は各項が `(線形)·φ(線形)` なので、
両座標を `λ ∈ F` 倍すると値は **`λ·φ(λ)` 倍**。これが書籍 p.120 の標準同一視
`c^x = x^{1+θ} c` の中身で、`d = 1 + 2^r` の理由。

**(b) 認識定理は既にこの関係式を作っている**:
`HigmanLemmaTwelve/TypeBRecognition.lean` の
`isTypeB_of_isomorphicOrderQModuleSplit_of_xiLengthThree` の証明中に

* `hlamnuL : dL.lambda ^ (1 + 2 ^ rL) = nu` (= `ν = λ^{1+2^r}`)
* `hθLfrob : dL.theta = Frob^{rL}`、**`hθLodd : dL.theta_order_odd`**

が**局所的な `have` として存在する** (l.194-195, 232-236, 279-283)。`λ` は actor が
`Q/Z(Q)` に掛ける スカラー、`ν` は `Z(Q)` に掛けるスカラー。これはモデル側の
`μ(k)` と `μ(k)^d` に他ならない。

⟹ **必要な仕事 = 認識定理を強化して `IsTypeB` と一緒にこの指数データを返すこと**
(`∃ r, (∀ k, ν_k = λ_k^{1+2^r}) ∧ Odd (orderOf (Frob^r))` の形)。
新規数学ではなく「中間結果の露出」。`isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube`
と `..._of_xiLengthThree` の 2 段、およびそれを呼ぶ `TypeBFromW.isTypeB_Q_of_orderThree_of_mem_W`
の signature 変更を伴う (呼び出しは `lemmaFive_of_orderThree` 等)。

⚠ 逆に **`TypeBData` 経由は遠回り**: `TypeBData` は `phi` と `phi_orderOf_odd` を持つが
**actor `K` の作用を記録していない**ので、`λ`/`ν` との関係が復元できず、
座標同定 (`TypeBData` の体 ↔ `frobFixedSubfield M.E 2 m`) も別途要る。
認識定理の内部データを使えば `K` は最初から引数に入っているので直接繋がる。

**次セッションはこの露出リファクタから**。

**(150) 追記 — 露出リファクタの入口**: `nu` / `dataL0` / `dataR0` は
`exists_complementaryFactorCoordinates_of_xiLengthThree`
(`TypeBRecognition.lean` l.73) が返す存在量化子。よって露出は

1. `exists_complementaryFactorCoordinates_of_xiLengthThree` の出力 (`nu`, `lambda`) が
   **入力の actor `K` の作用でどう表せるか**を確認 (`FactorCoordinateData.lambda` の定義)、
2. `isTypeB_of_isomorphicOrderQModuleSplit_of_xiLengthThree` の 4 分岐すべてで
   `ν = λ^{1+2^r}` + `Frob^r` 奇位数 が既に手元にあるので、結論に足す、
3. `..._of_card_eq_cube` → `TypeBFromW.isTypeB_Q_of_orderThree_of_mem_W` へ順に伝搬
   (呼び出し元は `lemmaFive_of_orderThree` など)

の 3 段。⚠ θ=φ=1 分岐は `ν = λ²` = `λ^{1+2^0}` で `Frob^0 = 1` (位数 1 = 奇) なので
**全分岐が同じ形に収まる**。

### (151) 🎯 露出すべき結論が確定 — 体の同定は不要、**純粋な指数の合同**で済む

`NoncommutativeFactorCoordinateData` (`PrescribedFactorCoordinates.lean` l.735) を実測:

```
  theta : RingAut (GaloisField 2 n)
  lambda : GaloisField 2 n
  theta_ne_one : theta ≠ 1
  theta_order_odd : Odd (orderOf theta)      ← これ
```

`c : Y` (= actor の元) が `Q/Z(Q)` に掛けるスカラーが `lambda`、`Z(Q)` に掛けるのが `nu`。
座標は**具体体 `GaloisField 2 n`** で、抽象体ではない。

⟹ 認識定理から露出すべき結論は

```
∃ r : ℕ, (∀ k, ν_k = λ_k ^ (1 + 2 ^ r)) ∧ Odd (orderOf (qFrobenius (GaloisField 2 m) 2 r))
```

これがあれば、**体の同定は一切要らない**:

* モデル側の `d` は `ι(centerKHom k z) = μ(k)^d · ι z` で定まり、`μ : K ≅ F^×`。
* `ν = λ^{1+2^r}` は「actor の商スカラーから中心スカラーへの写像」という**同じ写像**を
  別座標で見たもの。どちらも位数 `2^m − 1` の巡回群上の冪写像なので、
  **指数の合同 `d ≡ 1 + 2^r (mod 2^m − 1)` として直接移る**。
* `hshape : a^d = a · a^{2^r} = a·φ(a)` は `a^{2^m−1} = 1` から従う (φ := `qFrobenius F 2 r`)。
* `Odd (orderOf φ)` も `F ≅ GaloisField 2 m` で位数が保たれるので移る
  (体同型を経由するが、位数だけなので `orderOf` の共役不変性で足りる)。

⟹ 残る仕事は **(b) の露出リファクタ 1 本**に確定。数学は全部済んでいる。

**(150)(151) 訂正**: `typeBQuadraticMap_smul` は**既存だった**
(`TypeBIsomorphicSplit.lean:56`、同名・同証明)。`b6dd30efc` で `Types.lean` に重複追加し、
leaf build では衝突が見えず素通り → フルビルドで `has already been declared` で赤になり、
`4102db2c8` で撤回。**橋は既存補題をそのまま使えばよい**。
⚠ 書く前に概念名で grep する ([[grep-before-writing-transport-defs]])。
⚠ 新規宣言は leaf build が green でも**フルビルドまで名前衝突を検出しない**。

### (152) 🎯 `hodd` = 「モデル自身の twist が奇位数」1 文に還元 — type-`B` transport は不要になった

(151) で「認識定理の露出リファクタが要る」と書いたが、**もっと短い道があった** (commits
`705163994`, `6b749895e`)。

**(a) ペア補題を一般化** (`705163994`): Ch. III §3 の `d` は座標の取り替えで `2ⁱ d` になる
ので、手元の関係は `a^d = a·φ(a)` でなく `a^d = ψ(a)·φ(ψ(a))`。`RingAut F` は可換ゆえ
twist `σ⁻¹τ` は `φ^{±1}` のまま。⟹ **`d` の `1 + 2^t` 正規化は不要**。

**(b) `hshape` はモデルから直接出る** (`6b749895e`): `thetaModel_eq_id_on_frobFixed` の
証明内部に `μ(k)·θ(μ(k)) = μ(k)^d` があった (cocycle の半線形性 `hsemi` と `K`-scaling
`hscaleQ0` を `x = y = 1` で評価; anisotropy より `φ(1,1) ≠ 0`)。これを
`zpow_eq_mul_thetaModel` として切り出し、`μ(K) = F^×` と合わせて
**`a^d = a·θ(a)` on `F^×`** を得た。

⟹ `odd_orderOf_scalingPair_restrict_of_model`:

> `hsemi` + `haniso` + `hscaleQ0` + `hscale` + **`Odd (orderOf (θ|_F))`**
> ⟹ `Odd (orderOf ((σ|_F)⁻¹ · τ|_F))` (= `stepThree_of_odd` の `hodd`)

**`θ` はモデル自身の cocycle の twist** — `IsStandardModel` が `hsemi` と一緒に返すもの。
⟹ **体の同定も、`d` の正規化も、認識定理の露出リファクタも一切不要**。

**残る唯一の入力**: `Odd (orderOf (θ|_F))`。これは Appendix III Def 3 の `θ` そのもので、
`Suzuki2Groups.TypeBData.phi_orderOf_odd` が持っている。結び付けは
「モデルの cocycle `φ` と type-`B` の平方写像が同じもの」という**1 点の同定**のみ
(`typeBQuadraticMap_smul` が既存の橋)。

**次**: `IsStandardModel` の `θ` について `Odd (orderOf (θ|_F))` を出す。
`isTypeB_Q_of_orderThree_of_mem_W` の `TypeBData` と、`exists_bilinear_lift_normalized`
が返す `θ` を突き合わせる。

### (153) 最後の 1 点の正体 — 「K が type-`B` 座標で対角スカラーとして作用する」

(152) で `hodd` は `Odd (orderOf (θ|_F))` (θ = モデルの cocycle の twist) 1 文になった。
これを `TypeBData.phi_orderOf_odd` に結び付ける論証を詰めた結果、**指数だけで閉じる**:

* モデル側: `χ(a x) = a·θ(a)·χ(x)` for `a ∈ F` (`zpow_eq_mul_thetaModel` の元になる
  `hsemi` を `x = y` で読んだもの)。`θ|_F = Frob^t` とすると係数は `a^{1+2^t}`。
* type-`B` 側: `typeBQuadraticMap_smul` (既存) より `typeBQ(λ·v) = λ·phi(λ)·typeBQ(v)`。
  `phi = Frob^{t'}` とすると係数は `λ^{1+2^{t'}}`。
* `K` の作用は**内在的** (座標に依らない)。`μ : K ≅ F^×` と `λ : K ≅ F_B^×` はどちらも
  「k の固有値」なので、`ρ := λ ∘ μ⁻¹` は巡回群 `F^×` の群同型 = `x ↦ x^u` (gcd(u, 2^m−1)=1)。
  中心側の座標同型も同様。⟹ **冪写像は可換なので指数がそのまま移る**:
  `1 + 2^t ≡ 1 + 2^{t'} (mod 2^m − 1)` ⟹ `t ≡ t' (mod m)` ⟹ `orderOf (θ|_F) = orderOf phi`。

⟹ **必要な唯一の未形式化入力** = 「`K` が type-`B` 座標 `F_B × F_B` に**対角 `F_B`-スカラー**
として作用する」。これは Higman 認識定理の内部にある (`dataL.lambda` がその固有値) が、
`TypeBData` は記録していない。

⟹ (151) の露出リファクタは依然必要だが、**露出すべきものは 1 つだけ**に縮んだ:

```
∃ (lam : ↥K → F_B), (K の Q/Z(Q) への作用が type-B 座標で (a,b) ↦ (lam k * a, lam k * b))
```

(`ν = λ^{1+2^r}` も `Frob^r` の奇位数も、これがあれば `typeBQuadraticMap_smul` +
`phi_orderOf_odd` から従う。)

**次セッション**: `TypeBData` にこの `lam` フィールド (または並行する定理) を足す方向で
`TypeBRecognition` を強化する。

### (154) ✅ `hodd` 決着 — 「K が Z(Q)^# 上 regular」1 点で閉じた (type-`B` transport 不要)

(153) は「`K` が type-`B` 座標で対角スカラー」を認識定理から露出せよ、と書いていたが、
**その道は要らなかった**。`hodd` は**モデル内部の情報だけ**で出る (commit `f177a0886`)。

**(a) 数論の核** (`Algebra/FrobeniusExponentPairs.lean`):

> `odd_orderOf_of_mul_self_surjective` — `F = 𝐅_{2^n}`, `ρ ∈ RingAut F`。
> 積写像 `a ↦ a · ρ(a)` が `F^×` 上に **onto** なら `Odd (orderOf ρ)`。

`ρ = Frob^r` と書くと写像は `a ↦ a^{1+2^r}`。`orderOf ρ = n / gcd(n,r)` が偶とすると、
`g := gcd(n,r)` に対し `r/g` は奇なので `2^g + 1 ∣ 2^r + 1`、また `2g ∣ n` なので
`2^g + 1 ∣ 2^{2g} − 1 ∣ 2^n − 1`。⟹ 位数が `2^g+1 (> 1)` を割る元が `1` の第二の原像。

**(b) onto 性の出所 = `K` の regularity** (`PSU3ModelTwistOdd.lean`):

`exists_zpow_eq_of_mem_frobFixed` — `K` は `Z(Q)^#` 上推移的
(`LemmaFiveSetup.transCenter`)、座標 `ι` では `z ↦ μ(k)^d z` (`hequiv`)、
`μ(K) = F^×` (`exists_actualKActor_mu_eq`) ⟹ **`a ↦ a^d` は `F^×` 上 onto**。
`zpow_eq_mul_thetaModel` の `a^d = a·θ(a)` と合わせて (a) が発火する。

⟹ `TypeBData` も認識定理の露出も**一切不要**。Appendix III Def 3 が構造フィールドとして
持つ「θ は奇位数」は、標準モデル側では**定理**。

**(c) おまけ: `hpair` 仮説を全廃**。`exists_scalingPair_of_lemmaFiveSetup` は自前の `d` を
返すので座標が合わなかったが、`exists_scalingPair_of_centerCoordinate` (与えられた
`(ι, d)` 用に立て直したもの) で解決。`corollaryTwo_of_isStandardModel` /
`..._of_normalization` から `hpair` を削除し、pair も `θF` も奇位数も内部で構成する。

⟹ **「§2 を `U` 相対で走らせる」の残債は `hsq` (step (20) の平方関係) のみ**。

### (155) §2 の閉じ — 軌道 transversal が landing、残りは step (20) との配線

(154) で `hpair` が消えたので、段 (2) の残債は **`hsq` (§2 (20) の平方関係)** 1 本。
書籍 p.129 の閉じの Proposition を追い直し、必要な道具を 2 つ landing させた
(commits `3050fd983`, `bbade15b8`)。

**書籍の論法 (p.129)**: `ω_1,…,ω_n` を `(Q/Q₀)^#` の `KW` 軌道の代表系 (各々 (9) で
正規化済) とする。`ω²= (0,r)` と置き、

* `i` := 「`f(ω⁻¹)` が `ω_i` の軌道に入る」ような添字
* `k` := 「`f(ω⁻¹(0,α))` が `ω_k` の軌道に入る」ような添字

(17)+(20) で 2 本の等式を出し、(H4)+(H5) で `(ω_i(0,r))^{KW} = (ω_k(0,α+r))^{KW}`、
**代表系が相異なるから `i = k`**、そして `sq_eq_of_dOrbitRel` で `ω_i² = (0,α)`。

**⚠ 要点 (実測)**: `sq_eq_of_dOrbitRel` は `dOrbitRel D (ω⁻¹ρ) (ω(ρy))` を
**同一の `ω`** について要求する (両辺が同じ `ω` の `Q₀`-平行移動でないと、自由性から
`d = 1` を出す議論が動かない)。⟹ 「同じ軌道」では足りず、**代表の一致**が要る。

**landing した道具**:

1. `PSU3BarOrbit.lean` の `barOrbitRel x y := ∃ z ∈ Q₀, dOrbitRel D (x z) y`
   — 商群を作らずに `Q/Q₀` の `KW` 軌道を表す同値関係 (`refl`/`symm`/`trans`/
   `barOrbitSetoid`、`mem_Q`/`notMem_Q0`)。
2. `stepNine` の結論に書籍の軌道条項を復元 (witness は `c⁻¹(ωz)c`, `c ∈ K`)。
3. `exists_normalizedOrbitRep` — **正規化 transversal**
   `∃ r : G → G, (軌道上定数) ∧ (∀ x ∈ Q∖Q₀, r x ∈ Q∖Q₀ ∧ barOrbitRel x (r x) ∧ 正規化)`。
   類の `Quotient.out` を (9) で正規化するだけ。「軌道上定数」が書籍の「相異なる代表」。

**⚠ 次セッションはここから — 閉じの Proposition の組み立て**:

`ω := r x` (任意の `x ∈ Q∖Q₀`; 存在は `exists_mem_Q_notMem_Q0`)、`ρ := ω²`、
`y` は正規化の随伴元。`ω_i := r (f (ω⁻¹))`、`ω_k := r (f (ω⁻¹ y))` と置く
(`f` は `Q∖Q₀` を保つ: `IsFGH.mem`)。手順:

1. **`hi`/`hk` を作る**: `stepTwenty_snd` (「像は常に `ω₂(z y)`」) を正規化ペア
   `(ω, ω_i)` / `(ω, ω_k)` に当てる。⚠ `stepTwenty_snd` の仮説を実測して、
   `barOrbitRel` レベルの所属から `dOrbitRel` の精密形へ上げる経路を確認すること。
2. **`i = k`**: (H5) 連鎖 `dOrbitRel_of_stepTwenty_chain` の結論
   `dOrbitRel D (ω_k⁻¹ρ) (ω_i(ρy))` から `barOrbitRel ω_i ω_k` を読み、
   transversal の軌道上定数性で `ω_i = ω_k` (⚠ `r (f (ω⁻¹))` と `r (f (ω⁻¹ y))` の
   引数が同じ軌道に入ることを示す形にする)。
3. **仕上げ**: `f_eq_conj_inv_of_stepTwenty_chain` (既存) がそのまま
   `ω_i² = y ∧ f(ω_i) = (ω_i⁻¹)^ζ` を出す。`h(ω_i) ∈ W` は `h_mem_W` (既存)。

⟹ 出口は `∃ ω ∈ Q∖Q₀, f ω = ζ⁻¹ω⁻¹ζ ∧ h ω ∈ W` (書籍の閉じの Proposition そのもの)。
これが出れば `corollaryTwo_of_isStandardModel` の base pair を内部で供給でき、
`hsq` も消える。

### (155) 追記 — `hi`/`hk` を作る経路の実測 (次の着手点はここ 1 点)

`stepTwenty_snd` の署名を実測した (`PSU3StepTwenty.lean:232`):

> 正規化ペア `(ω₁, ω₂)` (**同じ `y`**)、`z, w ∈ Q₀`、`c ∈ D`、
> `f(ω₁ z) = c⁻¹(ω₂ w)c`、`z ≠ 1`、**`w y ≠ 1`** ⟹ `z = w y`。

⟹ `hi` の作り方はこうなる: `ω_i := r (f (ω ρ))` と置くと transversal から
`barOrbitRel (f (ω ρ)) ω_i`、その `symm` が
`∃ w ∈ Q₀, ∃ c ∈ D, f(ω ρ) = c⁻¹ (ω_i w) c` を与える。ここに `stepTwenty_snd` を
`z := ρ` で当てると `ρ = w y` ⟹ `w = ρ y` (∵ `y² = 1`) ⟹
`ω_i (ρ y) = (c⁻¹)⁻¹ f(ω ρ) (c⁻¹)` = `dOrbitRel D (f (ω ρ)) (ω_i (ρ y))` = **`hi`**。
`hk` は `z := ρ y` で同型。

**側条件 2 つ**:
* `z ≠ 1`: `ρ = ω² ≠ 1` は自動 (`ω² = 1` かつ `ω ∈ Q ≤ H` なら `ω ∈ Q₀` に反する)。
* **`w y ≠ 1` が未解決**。`w = y` の場合、正規化から `ω_i y = ζ f(ω_i) ζ⁻¹` なので
  `f(ω ρ)` が `f(ω_i)` の `D`-共役、つまり (H2)+`dOrbitRel_f` で `ω_i` が `ω⁻¹` の
  `D`-共役、という状況になる。**ここを潰すか、`stepTwenty_snd` を `hwy` 無しに
  強化するのが次の一手**。書籍側の対応箇所 (p.128 の (20) 第二主張の導出) を
  ページ画像で読み直すこと。

### (156) 段 (20) の側条件は解消済 — ただし仮説の形を「精密形」に直す必要がある

commit `814ac78a6` で退化 2 ケースを解消し、`dOrbitRel_mul_of_barOrbitRel` /
`y_eq_of_barOrbitRel` を landing させた。ただし**両者の仮説 `hne : ¬ barOrbitRel ω ω'`
は強すぎる** — 閉じの Proposition で `ω_i = ω` (書籍の `i = j`) が起こりうるから。

**⚠ 重要な発見**: `ω_i = ω` は矛盾ではなく**むしろ望ましい**ケース。連鎖の結論
`dOrbitRel D (ω_k⁻¹ρ) (ω_i(ρy))` で `ω_i = ω_k = ω` なら `sq_eq_of_dOrbitRel` が
そのまま `ω² = y` を出す。よって排除すべきは「軌道の一致」でなく**退化ケースそのもの**。

`ω' = ω` のとき退化 2 ケースはいずれも矛盾する (`z := ρ = ω²`):
* `w = y` ケース ⟹ `dOrbitRel D ω (ω ρ)`、`ρ ≠ 1` ゆえ `not_dOrbitRel_self_mul_Q0` で矛盾。
* `w = 1` ケース ⟹ `dOrbitRel D (ω y) (ω ρ)` = `dOrbitRel D (ωy) ((ωy)(y⁻¹ρ))`、
  **`ρ ≠ y` なら**同じ補題で矛盾 (`ρ = y` は結論そのものなので場合分けで先に処理)。

⟹ **次セッションの手順** (機械的):
1. `barOrbitRel_of_stepTwenty_degenerate_one` の結論を精密形
   `dOrbitRel D (ω' * y') (ω * z)` に変える (現状は `barOrbitRel ω ω'` に潰していて、
   `ω' = ω` の矛盾論法が動かせない)。
2. `dOrbitRel_mul_of_barOrbitRel` の仮説を `hdeg : ¬ dOrbitRel D ω' (ω * z)` に戻す。
3. `y_eq_of_barOrbitRel` の仮説を `hdeg1 : ¬ dOrbitRel D ω' (ω*z)` +
   `hdeg2 : ¬ dOrbitRel D (ω' * y') (ω*z)` の 2 本に。
4. 閉じの Proposition の組み立てで、この 2 本を
   「transversal の軌道上定数性 ⟹ `ω' = ω` ⟹ `not_dOrbitRel_self_mul_Q0`」で潰す。

**組み立ての骨格** (道具はすべて揃っている):
```
ω := r x₀ / ρ := ω*ω (∈ Q₀) / y := ω の正規化の随伴元
case ρ = y  ⟹ f_eq_conj_inv_of_sq_eq で即終了
case ρ ≠ y  ⟹ ω_i := r (f (ω*ρ)), ω_k := r (f (ω*(ρ*y)))   -- f_mem_sdiff_Q0 で Q∖Q₀
              y_eq_of_barOrbitRel で y_i = y = y_k
              dOrbitRel_mul_of_barOrbitRel で hi, hk
              dOrbitRel_of_stepTwenty_chain ⟹ dOrbitRel D (ω_k⁻¹ρ) (ω_i(ρy))
              ⟹ barOrbitRel ω_k ω_i ⟹ (transversal) ω_k = ω_i
              ⟹ sq_eq_of_dOrbitRel ⟹ ω_i² = y、f_eq_conj_inv_of_sq_eq で仕上げ
```

### (157) 🎯 §2 の閉じの Proposition が landing (`exists_f_eq_conj_inv`)

commit `943afd971`。書籍 p.129 の Proposition 前半が Lean に:

> `∃ ω ∈ Q − Q₀`, `∃ y ∈ Q₀`, `ω² = y ∧ f(ω) = (ω⁻¹)^ζ`

(後半 `h(ω) ∈ W` は既存の `h_mem_W`。) 仮説は `M`/`hZ`/`hmu`/`hVW` (= `D` の自由性)、
`hsqQ0 : ∀ x ∈ Q, x² ∈ Q₀`、`ζ` は `W` の生成元 (`hWcard`)、および任意の `x₀ ∈ Q∖Q₀`。

(156) で予告した精密形リファクタも完了 (`dOrbitRel_of_stepTwenty_degenerate_one` は
`dOrbitRel D (ω' y') (ω z)` を返す / 側条件は `hdeg1`,`hdeg2` の 2 本)。
新規補助: `not_dOrbitRel_mul_Q0_mul_Q0`, `normalization_y_unique`。

### ⚠ 次セッションはここから — `hsq` の消去 (endpoint 配線)

`corollaryTwo_of_isStandardModel_of_normalization` はまだ
`hsq : ∀ ω' ∈ Q∖Q₀, ∀ y ∈ Q₀, f ω' = ζ₀⁻¹(ω' y)ζ₀ → ω'² = y` (**全称**) を取るが、
書籍が主張するのは**存在**形。⟹ endpoint を `stepNine + hsq` でなく
`exists_f_eq_conj_inv` から base pair を取る形に組み替える:

1. `hsqQ0` を `sfive` から作る (`LemmaFiveSetup.sqMem` + `centerEqQ0`)。
2. `x₀ ∈ Q∖Q₀` は `exists_mem_Q_notMem_Q0` (`hcardQ` 済)。
3. **`ζ₀` を `W` の生成元に取る**必要がある (`hWcard : orderOf ζ₀ = |W|`)。
   `W` の巡回性は `isCyclic_W_and_card_dvd_of_orderThree`
   (`WCyclicDivides.lean:47`、仮説 `hst : orderOf (s·t) = 3` 等) から。
   ⟹ endpoint の `ζ₀` を**引数でなく内部で選ぶ**版を作るのが素直。
4. `exists_f_eq_conj_inv` の出力 `(ω, y, ω² = y, f ω = ζ⁻¹ω⁻¹ζ)` から
   `corollaryTwo_of_isStandardModel` が要る `hfω₀ : f ω₀ = ζ₀⁻¹(ω₀ y₀)ζ₀` を復元
   (`ω y = ω·ω² = ω³ = ω⁻¹`、`ω⁴ = 1` ゆえ)。

これが済めば **`hsq` が消え、段 (2) の残債はゼロ**になる。

### (158) 🎯 `hsq` 消滅 — 段 (2) の §2 側の残債はゼロに

commit `e02a85891`。`corollaryTwo_of_isStandardModel_of_closing` を新設し、base pair を
§2 の閉じの Proposition から直接供給するようにした。

* 旧 `..._of_normalization` の `hsq` は**全称**形だったが、書籍が主張するのは**存在**形
  (repo 側の特殊化債務だった)。新版はそれを取らない。
* `ζ₀` も引数から外し、内部で `W` の生成元を選ぶ (書籍の選択)。代わりに
  `hWcyc : IsCyclic ↥W` が入るが、これは `hWdvd` と**同じ補題**
  (`isCyclic_W_and_card_dvd_of_orderThree`) が同時に返すので新たな債務ではない。
* 補助 `sq_mem_Q0_of_lemmaFiveSetup` (`Q` の平方は `Q₀`)。

**endpoint の現在の仮説** (`corollaryTwo_of_isStandardModel_of_closing`):
`H`/`hC2`/`sfive`/`M`/`hZc`/`hmu`/`hVW`/`hm`/`hQ0card`/`hcardQ`/`hcard (3 ≤ |F|)`/
`hKcard`/`hWdvd`/`hW1`/**`hWcyc`**/`hfQ`/`hhW`/`x₀`/`hmodel`/`ζ`。
⟹ **§2 由来の未証明仮説はもう無い**。

### ⚠ 次セッションはここから — Ch. IV §4 段 (2) の配線

`isStandardModel_residualQuotient` (`PSU3SectionFourCorollaryTwo.lean`) が
`U/Z(U)` 上のモデルを出すので、そこに `..._of_closing` を当てるのが段 (2) の完成。
過去の実測 ((133)(136)(141)(142)、本 issue の表) では残り仮説はすべて
「導出可・未接続」= **新規数学でなく配線**:

* `hfQ` — `exists_fgh_mapsTo` (本ファイル) / `Setup.exists_fgh_one`
* `hhW` — `h_mem_W` 経由 (`hVW`/`hWdvd`/`hZc`/`hmu` から)
* `hWdvd` + **`hWcyc`** — `isCyclic_W_and_card_dvd_of_orderThree` が同時に返す
* `hW1` — `exists_ne_one_mem_quotient_W`
* 数値系 (`hm`/`hQ0card`/`hcardQ`/`hKcard`/`hcard`) — 内在版で既出 ((141)(142))

⚠ `hcard : 3 ≤ |F|` は (143) で「θ が奇位数」へ置換済の側の話と混同しないこと
(こちらは `θ|_F = 1` 分岐が要求する 3 元)。

### (158) 追記 — 段 (2) 配線の材料、所在を実測

`..._of_closing` の残り仮説について、供給元を grep で確定した (未接続なだけ):

| 仮説 | 供給元 |
|---|---|
| `H` (`IsFGH`) + `hfQ` | `Hypothesis.exists_fgh_mapsTo` (汎用、どの仮説にも当たる) |
| `hC2` | `braid_of_orderOf_mul_eq_three` (`DistinguishedInvolution.lean:429`) ⟸ `hst : orderOf (s·t) = 3`。**商側の `hst` は既存**: `residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t` |
| `hmu` | `mu_injective_residualQuotient` (`PSU3SectionFourModel.lean:210`) — transported 版で既存 |
| `hZc` | `sfive.centerEqQ0` そのもの |
| `sfive`/`M`/`x₀`/`hKcard`/`hmodel` | `exists_isStandardModel_intrinsicResidualQuotient` の結論に同梱 ((142)) |
| `hWdvd` + **`hWcyc`** | `isCyclic_W_and_card_dvd_of_orderThree` (同時に返す) |
| `hW1` | `exists_ne_one_mem_quotient_W` |
| `hhW` | `h_mem_W` 経由 ((133)) |
| `hcard : 3 ≤ \|F\|` | `\|F\| = 2^n` なので **`n ≥ 2`** と同値 — ⚠ 商側で `n ≥ 2` が出るか未確認 |
| `hcardQ : \|Q\| = \|Q₀\|³` | §4 transport で既出 ((138) の 5 入力の 1 つ) |

⚠ **設計分岐 (次セッションが決める)**: 配線先を
**(a) transported 版 `residualQuotientHypothesis`** (上表の `hmu`/`hst` が直接使える) にするか、
**(b) 内在 ULift 版 `intrinsicResidualQuotientULift`** (書籍の `f₁`,`h₁` に対応するのはこちら;
(141) の四つ組照合同型で (a) から移送できる) にするか。
(b) が最終的に要るが、(a) で先に閉じて移送する方が安全かもしれない。

**(158) 追記 2 — `hcard` も解決**: `PSU3InductionTarget.one_lt_n : 1 < n`
(`CentralizerInductionBridge.lean:74`) が構造フィールドなので `|F| = 2^n ≥ 4 ≥ 3`。
⟹ **段 (2) 配線に未解決の材料は無い**。残るは (a)/(b) の配線先の選択と実装のみ。

### (159) ⚠ 注記の食い違いを訂正 — `hhW` (∀ 版) は**未解決**

(158) の表で `hhW` を「`h_mem_W` 経由で導出可」と書いたが、**本 issue 内で注記が
食い違っている**。古い実測 (l.5520) の方が正しい:

> `h_mem_W` (`PSU3StepEighteen.lean:171`) は**特定の `ω`** について §2 の鎖データ
> (正規化 `hfω` + 停止指数 `hns`/`hstop`) 込みで出す。**∀ 版は要検討**。

一方 (6608)(7111) は「✅ 導出可」としているが、根拠が示されていない。
⟹ **`hhW : ∀ ρ ∈ Q∖Q₀, h ρ ∈ W` は現時点で未証明**。`hsq` と**同じ型の問題**
(書籍は代表元 `ω_i` についてしか言っていない) である可能性が高い。

**次セッションの最初の仕事**: `hhW` の消費点を実測する。
* 消費は `corollaryTwo_of_stepFour` 1 箇所 (`PSU3CorollaryTwo.lean:319` 経由)。
* §3 段 (4) は `stepFour_cover_of_base` で `Q` を base pair の `KW`-移動で覆うので、
  **覆いの各元でしか `h ρ ∈ W` を使っていない可能性**がある。
  そうなら `hhW` は「transversal 代表 + 覆い」に弱められ、`h_mem_W` で閉じる
  (`hsq` を `exists_f_eq_conj_inv` で閉じたのと同じ形)。
* 停止指数 `hns`/`hstop` の供給は `stepEleven` 系 (`PSU3Sequence.lean`) を実測すること。

⚠ 教訓: 本 issue は 7000 行を超え、古い ⚠ と新しい ✅ が混在している。
**表の「✅ 導出可」は、根拠 (定理名) が併記されていなければ信用しない**
([[verify-port-state-by-number-not-coq-name]])。

### (160) 🎯 `hhW` の消費点は **1 箇所・1 元だけ** — 弱化できる

`corollaryTwo` (`PSU3InverseFormula.lean:925`) を実測。`hhW` の使用は末尾の 1 行のみ:

```
  exact ⟨(ωQ : G), hωmem, hnotQ0, hfeq,
    hyp.h_eq_zpow_three H M hZc hmu hVW hζ hωmem hnotQ0 hfeq (hhW _ hωmem hnotQ0)⟩
```

⟹ **∀ 版は不要**。必要なのは「`corollaryTwo` が `ζ` から構成する当の `ω`」1 点での
`h ω ∈ W` だけ。しかもその `ω` は `hfeq : f ω = ζ⁻¹ω⁻¹ζ` を満たしている。

**弱化の候補 2 つ**:
1. 仮説を `∀ ρ ∈ Q∖Q₀, f ρ = ζ⁻¹ρ⁻¹ζ → h ρ ∈ W` に絞る (消費点に必要十分)。
   さらに `h_mem_W` で閉じられるか: `ω² ∈ Q₀` から `y := ω²` と置くと
   `ω y = ω³ = ω⁻¹` なので `hfeq` は正規化 `f ω = ζ⁻¹(ω y)ζ` そのもの。
   ⚠ ただし `h_mem_W` は **`hWcard : orderOf ζ = |W|`** (ζ が生成元) を要求する。
   Corollary 2 の `ζ` は `W^#` の任意元なので、そのままでは当たらない。
2. **書籍の道**: `corollaryTwo` の docstring 自身が
   > the book's second conclusion `h(ω) = ζ³` is `h_eq_zpow_three` applied to the first
   > (it needs `h(ω) ∈ W`, **which the book reads off (H5)**)

   と書いている。⟹ **p.132 を読んで (H5) からの導出を形式化するのが本筋**。
   (H5) は `(f∘j)³(x) = x^{h(x)⁻¹}` (`dOrbitRel_fj_cube` / `hFive`)。

**次セッションの手順**: `references/peterfalvi/pages/peterfalvi-p132.png` を読み、
Corollary 2 の証明で `h(ω) ∈ W` をどう出しているかを確定 → 形式化 → `hhW` を
`corollaryTwo` から削除 → 上流 6 箇所 (`corollaryTwo_of_stepFour` …
`..._of_closing`) の仮説から芋づる式に落とす。
⟹ これが済めば endpoint の未証明仮説は `hfQ` (= `exists_fgh_mapsTo` で供給) と
標準データのみになる。

### (161) 🎯 書籍 p.132 の Corollary 2 は `h(ω) ∈ W` を**使っていない** — (H5) 直で `h(ω) = ζ³`

原文 (p.132、pdftotext):

> **Corollary 2.** If `G = PSU(3,q)` and if `ζ ∈ W^#`, then there is an element
> `ω ∈ Q − Q₀` such that `f(ω) = ω^{-ζ}` and `h(ω) = ζ³`.
> *Proof.* As `ζ⁻¹ + ζ^{-q} ≠ 0`, there is `ω̄ ∈ E − {0}` with `ω̄^{1+q} = ζ⁻¹ + ζ^{-q}`.
> Then `ω = (ω̄, ζ⁻¹) ∈ Q`, `ω⁻¹ = (ω̄, ζ)` and `f(ω) = (ω̄ζ, ζ) = ω^{-ζ}`.
> **Applying (H5), we thus see that `h(ω) = ζ³`.** ∎

⟹ 書籍は `h(ω) ∈ W` を経由しない。(H5) `(f∘j)³(x) = x^{h(x)⁻¹}` を `f(ω) = ω^{-ζ}`
に当てると `ω^{h(ω)⁻¹} = ω^{ζ⁻³}`、つまり `h(ω)⁻¹ζ³ ∈ D` が `ω` を `Q₀` を法として
固定する ⟹ **`D` の自由性** (`eq_one_of_conj_eq_mul_Q0_of_mem_D`) で `h(ω) = ζ³`。

⟹ **`hhW` は repo 側の特殊化債務**。`h_eq_zpow_three` が `h ω ∈ W` を取っているのが
原因なので、そこを自由性で書き換えれば `hhW` は消える。

**次セッションの手順**:
1. `h_eq_zpow_three` (`PSU3SectionThree.lean` 付近) の証明を読み、`h ω ∈ W` が
   どこで効いているかを実測。
2. `(f∘j)³` の計算は既存 (`fj_cube_of_f_eq_conj_inv` / `hFive`) なので、
   最後の「`D` の元が `ω` を `Q₀` 法で固定 ⟹ 1」を
   `eq_one_of_conj_eq_mul_Q0_of_mem_D` に差し替える。
3. `h_eq_zpow_three` から `h ω ∈ W` 仮説を落とす → `corollaryTwo` から `hhW` を落とす
   → 上流 6 箇所 (`corollaryTwo_of_stepFour` … `..._of_closing`) を芋づるで掃除。

### (161) 追記 — `hhW` が効いている行は 1 行だけ、正体は「`t` が `h(ω)` と可換」

`h_eq_zpow_three` (`PSU3SectionThree.lean:167`) で `hhW : h ω ∈ W` の使用は:

```
  have hth : hyp.t * h ω * hyp.t = h ω := by
    have hc : Commute (h ω) hyp.t := hyp.commute_t_of_mem_V (hyp.W_le_V hhW)
```

の 1 箇所のみ。これで (H4) `h(ω⁻¹) = (h(ω)^t)⁻¹` を `h(ω⁻¹) = h(ω)⁻¹` に直し、
`h_inv_eq` (`h(ω⁻¹) = ζ⁻³`) と突き合わせている。

⚠ `V = D ⊓ C({t})` なので `h ω ∈ V` ⟺ `h ω ∈ D` (常に真) **かつ** `t` と可換、で
**循環**する。⟹ (H4) 経由の現行ルートでは `hhW` は落とせない。

⟹ **書籍どおり (H5) 経由に書き換えるのが正解**:
* `fj_cube_of_f_eq_conj_inv` (同ファイル、既存) が `(f∘j)³(ω⁻¹) = ω^{-ζ³}` を出す。
* (H5) `hFive` は `(f∘j)³(x) = x^{h(x)⁻¹}`。
* 両者を突き合わせると「`D` の元 (`h(·)⁻¹ζ³` 相当) が `ω` を `Q₀` 法で固定」
  ⟹ `eq_one_of_conj_eq_mul_Q0_of_mem_D` (自由性) で `h(ω) = ζ³`。
* 自由性の入力 (`M`/`hZ`/`hmu`/`hVW`) は `h_eq_zpow_three` が**既に取っている**ので
  仮説は増えない。

### (162) 🎯 `hhW` 全廃 — endpoint の未証明仮説は `hfQ` と標準データのみに

commit `5a294fc66`。(161) の読み通り、`ω⁻¹` 側で `h_inv_eq` を回すと (H4) の twist が
最初から現れず、`hhW` は不要だった:

* `f_inv_eq`: `f(ω⁻¹) = ζωζ⁻¹ = (ζ⁻¹)⁻¹(ω⁻¹)⁻¹(ζ⁻¹)` — `ζ ↦ ζ⁻¹` で同型の仮説。
* `h_inv_eq` を `(ω⁻¹, ζ⁻¹)` に当てて `h(ω) = ζ³`。`h_inv_eq` は自由性だけで回るので
  仮説増なし。

⟹ `corollaryTwo` / `corollaryTwo_of_stepFour` / `PSU3CorollaryTwo` の endpoint 6 本から
`hhW` を削除。`hpair` (154) → `hsq` (158) → `hhW` (162) と**特殊化債務 3 本を返済**。

**`..._of_closing` の現在の仮説** = `H`/`hC2`/`sfive`/`M`/`hZc`/`hmu`/`hVW`/`hm`/
`hQ0card`/`hcardQ`/`hcard`/`hKcard`/`hWdvd`/`hW1`/`hWcyc`/**`hfQ`**/`x₀`/`hmodel`/`ζ`。
`hfQ` は `exists_fgh_mapsTo` が供給する (f,g,h を作る側とセット)。
⟹ **残るは §4 段 (2) の配線のみ** ((158) の表、材料は全部所在確認済)。

### (163) 段 (2) 配線のレシピ (transported 版) — 全補題名を確定

`PSU3SectionFourCorollaryTwo.lean` に `corollaryTwo_residualQuotient` を書く。
`qhyp := hyp.residualQuotientHypothesis details`、`n := data.n`。
`letI := MulAction.compHom (ULift.{v} (Unital data.n)) details.residualQuotientEquiv.toMonoidHom`
は `isStandardModel_residualQuotient` (同ファイル l.325-) をそのまま真似る。

| `..._of_closing` の引数 | 供給 (すべて実在を確認済) |
|---|---|
| `H` + `hfQ` | `qhyp.exists_fgh_mapsTo` (`PSU3CorollaryTwo.lean:~700`) |
| `hC2` | `braid_of_orderOf_mul_eq_three` ⟸ `residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t` |
| `sfive`, `M` | `nonempty_standingData_residualQuotient` (`PSU3SectionFourModel.lean:172`) |
| `hZc` | `sfive.centerEqQ0` |
| `hmu` | `mu_injective_residualQuotient` (同 l.210) |
| `hVW` | `residualQuotientHypothesis_V_eq_W` (同 l.78) |
| `hm` | `(Nat.zero_lt_one.trans data.one_lt_n).ne'` |
| `hQ0card` | `natCard_residualQuotientHypothesis_Q0` (同 l.89) |
| `hcardQ` | `natCard_residualQuotientHypothesis_Q` (同 l.99) |
| `hcard : 3 ≤ \|F\|` | `natCard_frobFixedSubfield` + `2^n ≥ 4` (`data.one_lt_n`) |
| `hKcard` | `card_actualKActor_eq` (`PSU3OrbitCount`、汎用: `sfive`+`M`+`hm`+`hQ0card`) |
| `hWdvd` + `hWcyc` | `isCyclic_W_and_card_dvd_of_orderThree hst hQsuz hm hQ0card hcardQ ihq` (`WCyclicDivides.lean:47`)。`hQsuz` = `isSuzuki2Group_residualQuotientHypothesis_Q` (`PSU3SectionFourModel.lean:137`)、`ihq` = `theoremAInductionBelow_residualQuotient` |
| `hW1` | `exists_ne_one_mem_residualQuotientHypothesis_W` (同 l.126) から `1 < Nat.card W` |
| `x₀`, `hmodel` | `exists_center_Q_ne_one_residualQuotient` (同 l.198) + `isStandardModel_residualQuotient` |
| `ζ` | 引数 (任意の `ζ ∈ W^#`) |

結論の形: `∃ f₁ g₁ h₁, IsFGH … ∧ ∃ ω ∈ Q, ω ∉ Q₀ ∧ f₁ ω = ζ⁻¹ω⁻¹ζ ∧ h₁ ω = ζ³`
(`f` は `exists_fgh_mapsTo` が作るので存在量化にする)。

⚠ この後さらに内在 ULift 版 (`intrinsicResidualQuotientULift`) へ移す必要がある
((141) の四つ組照合同型)。書籍の `f₁`,`h₁` は内在版に対応するため。

### (164) 🎯🎯 Ch. IV §4 段 (2) が landing — `corollaryTwo_residualQuotient`

commit `62eb97427`。(163) のレシピどおりで**初回ビルド green**。

> `∀ ζ ∈ W^#`, `∃ f₁ g₁ h₁`, `IsFGH … ∧ ∃ ω ∈ Q − Q₀`, `f₁ ω = ζ⁻¹ω⁻¹ζ ∧ h₁ ω = ζ³`
> (`hyp.residualQuotientHypothesis details` 上で)

書籍 p.133 の段 (2)「§2 と §3 を `U` 相対で走らせる」の結論。**未証明仮説ゼロ**
(`hpair`(154) → `hsq`(158) → `hhW`(162) の返済がここで効いた)。

**残り**: 内在 ULift 版 (`intrinsicResidualQuotientULift`) への移送。書籍の `f₁`,`h₁` は
`U ∩ H`, `U ∩ Q`, `U ∩ D`, `t` の像に関する写像なので、四つ組照合同型 ((141)
`exists_mulEquiv_match_residualQuotient_t`) で `corollaryTwo_residualQuotient` の結論を
移せばよい。`IsFGH` と結論はどちらも群同型で移送可能な形なので、
**`Hypothesis.ofMulEquivPullback` 系の移送補題を 1 本足す**のが筋。

### (165) 内在版への移送レシピ — `IsFGH.map` がそのための道具 (docstring がそう書いている)

`IsFGH.map` (`RankOneBNPair.lean:478`) の docstring:

> …it is what Peterfalvi Part II, Ch. IV §4, step (2) (p. 133) uses to read Corollary 2
> of §3 — proved for the quotient `U/Z(U)` — back inside `U`

署名: `(hS' : Setup M' Q' D' t') (H : IsFGH M Q D t f g h) (H' : IsFGH M' Q' D' t' f₁ g₁ h₁)`
`(π : L →* L') (ht : π t = t') (hQπ) (hDπ) (hxQ : x ∈ Q) (hx1 : π x ≠ 1)`
⟹ `f₁ (π x) = π (f x) ∧ g₁ (π x) = π (g x) ∧ h₁ (π x) = π (h x)`。

⟹ **移送補題の骨格** (次セッション):
1. `ψ` と `H,Q,D,t` の対応を `exists_mulEquiv_match_residualQuotient_t` から取る
   (`Q₀` は `map_Q0_of_mulEquiv`、`W` は `map_W_of_mulEquiv`; `HypothesisFieldMatching.lean`)。
2. 内在側の三つ組は `exists_fgh_mapsTo` で別途作る (`f₂,g₂,h₂`)。
3. `corollaryTwo_residualQuotient` の `ω` を `ψ ω` へ移す。`IsFGH.map` で
   `f₂ (ψ ω) = ψ (f₁ ω) = ψ(ζ⁻¹ω⁻¹ζ) = (ψζ)⁻¹(ψω)⁻¹(ψζ)`、
   `h₂ (ψ ω) = ψ (h₁ ω) = (ψζ)³`。
4. `ψ ω ∉ Q₀'` は `map_Q0_of_mulEquiv` + `ψ` の単射性。
   `ζ' := ψ ζ` は `W'^#` を走る (`map_W_of_mulEquiv`)。
⟹ 結論は `corollaryTwo_residualQuotient` と同型の文が
`intrinsicResidualQuotient` 上で成り立つ、という形になる。

### (166) 移送補題 landing — 段 (2) 内在版まであと 1 手

commit `0a8002626`。`corollaryTwo_conclusion_of_mulEquiv`
(`HypothesisFieldMatching.lean`) が結論の移送を担う (核は `IsFGH.map`)。

**残り 1 手** = 組み立て: `PSU3SectionFourIntrinsic.lean` に

```
theorem corollaryTwo_intrinsicResidualQuotient … :
  ∀ ζ ∈ (intrinsic hyp).W, ζ ≠ 1 → ∃ f₂ g₂ k₂, IsFGH … ∧ ∃ ω ∈ Q, ω ∉ Q₀ ∧ …
```
を書く。手順:
1. `ψ` と 4 つ組対応 ← `exists_mulEquiv_match_residualQuotient_t`
2. 内在側の `ζ` を transported 側へ引き戻す (`map_W_of_mulEquiv` の逆向き:
   `ζ = ψ ζ₀` となる `ζ₀ ∈ W` を取る)
3. `corollaryTwo_residualQuotient` を `ζ₀` に当てて `(f₁,g₁,k₁,ω)` を得る
4. 内在側の三つ組は `exists_fgh_mapsTo`、`corollaryTwo_conclusion_of_mulEquiv` で移送
⚠ `intrinsicResidualQuotient` と `intrinsicResidualQuotientULift` の使い分けに注意
(照合同型は前者、標準モデルは後者)。

### (167) 🎯🎯 段 (2) 完了 — 内在版 `corollaryTwo_intrinsicResidualQuotient`

commit 済。書籍 p.133 の段 (2) が、書籍の意味の写像 (`f₁`,`h₁` = 内在仮説の三つ組) に
ついて**未証明仮説ゼロで**成立:

> `∀ ζ ∈ W^#`, `∃ f₂ g₂ k₂`, `IsFGH … ∧ ∃ ω ∈ Q − Q₀`, `f₂ ω = ζ⁻¹ω⁻¹ζ ∧ k₂ ω = ζ³`

経路: `corollaryTwo_residualQuotient` → `exists_mulEquiv_match_residualQuotient_t`
→ `corollaryTwo_conclusion_of_mulEquiv`。

**このセッションの成果** (段 154-167): `hpair` / `hsq` / `hhW` の特殊化債務 3 本を返済し、
§2 の閉じの Proposition (p.129) を証明し、段 (2) を transported/内在の両方で閉じた。

**次**: Ch. IV §4 の段 (3) 以降 (p.133-134)。段 (2) の結論を `U` 内へ読み戻す
(`IsFGH.map` の docstring が言う "back inside `U`") ところから。
