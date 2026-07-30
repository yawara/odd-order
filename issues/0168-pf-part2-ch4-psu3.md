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

### (10) (p.125) — 確定済

`a, b ∈ K` が `b^{1+θ} = α + a^{-(1+θ)}` を満たすなら

    f(ω s^a) = (f(ω s^b) s^a)^{ζ a⁻²}

証明: (2) より
`f(ωs^a) = f(f(ω)s^{a⁻¹})^{a⁻²}s^{a⁻¹} = f(ωys^{a⁻¹})^{ζa⁻²}s^{a⁻¹}
= (f(ωs^b)s^a)^{ζa⁻²}`。

⚠ `θ` = モデルの Frobenius (`exists_standardModel` の `θ : E ≃ₐ[ZMod 2] E`)、
`α` = `y` の `E`-座標。**(10) 以降は 0167 の標準モデルの座標計算**になる。

その後: `τ` = `u ↦ u^{1+θ} : F^× → F^×` の逆写像 (`θ` が奇数位数ゆえ全単射)。


## ⚠ ファイル分割 — 実施すべき (境界確定済)

`PSU3Preliminary.lean` = **1407 行** (2026-07-31)。上限 1500 が近いので、
段 (8) の最終組み立てを入れる**前に**分割する。**境界は調査済**:

```
1–77     ヘッダ + import
78–176   汎用補題 4 本 (coprime_two_pow_sub_one_two_pow_add_one /
         eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one /
         two_pow_sq_sub_one_div / card_fiber_eq_of_card_eq)
177      namespace Hypothesis
178–1046 §2 段 (1)-(7) + `|D:K|` + 翻訳の群論部分   ← モデル非依存
1047–1404 「The scalar group μ(KW) inside E^×」以降 ← モデル依存
1405     end Hypothesis
```

**分割案** (tail-out; 下流未消費なので module 名の維持は不要):
* 新 `PSU3OrbitCount.lean` ← `78–176` + `namespace Hypothesis` + `1047–1404`
  + `end Hypothesis`。import = `PSU3Preliminary` + `QuotientKWField`
  + `ModelIsomorphism`。
* `PSU3Preliminary.lean` から上記を削除し、`QuotientKWField` /
  `ModelIsomorphism` の import も落とす (群論部分は使っていない)。
* `OddOrder.lean` と `AxiomsCheck.lean` に新 leaf を配線
  (⚠ orphan leaf 防止; AxiomsCheck の該当エントリも移す)。

汎用補題 4 本を tail 側に置く理由: いずれも消費者がモデル数値部分のみ。

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
