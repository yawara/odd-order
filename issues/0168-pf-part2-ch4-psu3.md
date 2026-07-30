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

### 次 = (4)-(6)

**(4)** `f(ωx) = f(ω)y` (`ω ∈ Q−Q₀`, `x,y ∈ Q₀`) ⟹ `x = 1`。書籍の証明:
`x ≠ 1` なら `x = s^k` (`k ∈ K`) → (3) で `f(ω)y = f(g(ω)s^{k⁻¹})^{h(ω)^t} f(ω)`
→ `f(g(ω)s^{k⁻¹}) ∈ Q₀` → `g(ω) ∈ Q₀` → `ω ∈ Q₀` で矛盾。

**必要な部品と repo の所在 (調査済)**:
* `x ∈ Q₀^#` ⟹ `∃ k ∈ K, x = s^k` = 既存の
  `Hypothesis.image_conj_KSet_eq_involutions_H`
  (`(fun k => k⁻¹ s k) '' KSet = {x | x² = 1 ∧ x ≠ 1 ∧ x ∈ H}`) を `s` で適用。
* **`f` と `g` は `Q₀^#` を `Q₀^#` に写す** — (1) の `f(s^a) = g(s^a) = s^{a⁻¹}` と
  上記の enumeration から。`f∘f = id` ((H2)) と `g∘g = id` (`hFive` の中で証明済:
  `g(g x) = x`) で全単射性が出るので `f(z) ∈ Q₀ ⟹ z ∈ Q₀` も従う。⟸ これが (4) の鍵。
* `Q₀ ⊴ Q` と `D` が `Q₀` を正規化 — `ActualCenter.lean` 周辺を要確認。

**(5)** `f(ω) = (ωy)^a` ⟹ `y ≠ 1` かつ `a ∉ K`。`|D|` 奇数 ⟹ `j` は `Q−Q₀` の
`D`-軌道集合上に不動点なし、`f` は誘導置換群内で `j` と共役 (= p.123 の注、
`IsFGH.dOrbitRel_f`/`_fj_cube` で形式化済) ⟹ `f` も不動点なし。
**(6)** `f(ωx) = (f(ω)y)^a` (`y ≠ 1`) ⟹ `a ∈ K`。(2) と (5) から。

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
