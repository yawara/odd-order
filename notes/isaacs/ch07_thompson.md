# Isaacs Ch.7: The Thompson Subgroup — mini-roadmap

> ✅ **COMPLETE (frozen, 2026-07-02)** — Ch.7 全定理 sorry-free
> (`OddOrder/Isaacs/Ch07_ThompsonSubgroup/`)。以下の「未作成」等は調査時点の記述 (履歴)。

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.7 (pp. 201-222).
形式化先 (予定): `OddOrder/Isaacs/Ch07_ThompsonSubgroup.lean` (未作成).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 3713-4058.
ROADMAP 上の位置: **第 5 波 (Ch.6 完了後、Ch.10 と並列可)** — **Phase 1 の山場のクリティカルパス頂点**. 前提は Ch.6 (6.11, 6.20, 6.23, 6.24) + Ch.5 (5.26 Frobenius normal p-complement) + Ch.4 (4.29, 4.33, 4.35) + Ch.3 (3.21 Hall-Higman) + Ch.2 (2.13 Baer 系, 2.17 normalizer/centralizer の `p'`-quotient).

## TL;DR — **FT クリティカル経路の頂点**、mathlib カバレッジは事実上ゼロ、BG **App.A** で全面前提

**Phase 1 内で本書最重要章の一つ**. 章本体は **わずか 8 結果** (Thm 7.1 + Lemma 7.2-7.4, 7.7 + Thm 7.5-7.6, 7.8) で短いが、各定理が独立に **BG/Peterfalvi 経由の FT 経路で本質的**:

- **Thm 7.1 (Thompson)** = Ch.6 Thm 6.23 の改良版で **本書での Frobenius kernel nilpotent (6.24) 完備化の最後のピース**. ✅ 完了 — 6.23 (characteristic-subgroup 形) は Thm 7.1 から導出済 (`Ch06_FrobeniusActions/ThompsonPComplement.lean`). なお 6.23 が `axiom`/`sorry` で置かれたことは一度も無い (この記述は当初計画のまま残っていた).
- **Thm 7.6 normal-J theorem** ≡ **BG Theorem 6.2** (`Z(J(S))·O_{p'}(G) ⊴ G` for solvable G of odd order). **BG §8, §9 (Uniqueness Theorem) で 7 ヶ所超で直接引用** (L2456, L2480, L2482, L2511, L2515, L5014, L5032). BG App.A "Prerequisites and p-Stability" は **Thm A.4(b) として Thm 7.6 を再述**し、これに依拠する形で BG §6 の Theorem 6.1 ("`O_{p',p}(G)` contains every abelian normal subgroup of S") を導出.
- **Thm 7.5 normal-P theorem** = `p`-solvable + abelian Sylow-2 + 忠実作用 + `|V:C_V(P)| ≤ p` ⇒ `P ⊴ G`. Thm 7.6 の induction step として中で使う.
- **Thm 7.8 Burnside p^a q^b** — character-free Goldschmidt-Bender-Matsuyama 証明. BG/Peterfalvi 直接被引用は無いが Phase 1 完成度のため必須 (BG L2633 が "we can obtain Burnside's `p^a q^b` very easily now" と本章手法の応用例として言及).
- **`J(P)` 定義そのもの** — 「最大 elementary abelian 部分群の生成」. **BG L5586 で `J(P) = Thompson subgroup of P`** として `p.49` で導入され全本 (BG §6, §8, §9, App.A, App.B) で多用. BG App.B は J(P) の代替 (Puig L(S)) を扱うが、これも本来は `Z(J(S))` の代替.

**mathlib カバレッジは事実上ゼロ**:
- **`J(P)` 定義**: mathlib に「elementary abelian 部分群」概念すら存在しない (`grep -rE "elementary|Elementary" Mathlib/GroupTheory` 全マッチ無し). `Subgroup.exponent = p` で表現可能だが`def IsElementaryAbelian` から新規.
- **ZJ theorem (Glauberman) / normal-J theorem (Isaacs Thm 7.6)**: mathlib 完全未収載 (`grep -r "Thompson\|ZJ\|p[-_]stab" Mathlib` 全マッチ無し).
- **Thompson normal p-complement (Thm 7.1)**: mathlib 未収載. Ch.6 Thm 6.23 経由でも記載なし.
- **Burnside p^a q^b (Thm 7.8)**: mathlib `Burnside` 名は `Mathlib/GroupTheory/Transfer.lean` (5.13 Burnside normal p-complement) と `Mathlib/GroupTheory/GroupAction/Quotient.lean` (Burnside lemma orbits) のみで、**`p^a q^b` 可解性は未収載**.
- **`GL(2,p)` 上の Lemma 7.3 (p-subgroup が `p'`-subgroup を normalize ⇒ centralize)**: `Mathlib/LinearAlgebra/SpecialLinearGroup.lean` には行列構造のみ、Isaacs 流の p-subgroup 引数は完全に新規.
- **`SL(2,q)` の involution unique = -I (Lemma 7.4)**: mathlib `SpecialLinearGroup` API ではあるが直接補題は未収載.

⇒ **Ch.7 は実質 100% 新規実装**. **`J(P)` 定義 + ZJ-style theorem + Thompson factorization 派生**は Ch.6 Frobenius と並ぶ Phase 1 の双璧.

## 章のセクション分割と全 8 結果

mmd で `### 7a` (L3715), `### 7b` (L3828), `**7C**` (L3898, インラインテキストマーカー), `### 7D` (L3951) の 4 セクション. `Problems 7A` (L3803), `Problems 7C` (L3945) のみ捕捉済 (Problems 7B, 7D は本文に存在せず). MISSING_PAGE marker ゼロ. mmd 品質良好.

| § | mmd 行 | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 7A | 3715-3826 | Thompson subgroup `J(P)` 定義 + `GL(2,p)`/`SL(2,q)` 補題 + **normal-P theorem** | 7.1 (statement), 7.2 – 7.5 | **Thm 7.1 statement** (proof は §7C), J(P) 特性 (7.2), **Lem 7.3 GL(2,p) p-sub normalize ⇒ centralize**, **Lem 7.4 SL(2,q) odd の唯一 involution = -I**, **Thm 7.5 normal-P** |
| 7B | 3828-3896 | **normal-J theorem** | 7.6 | **Thm 7.6 normal-J** (= BG Theorem 6.2 odd-order 版) — 8 step proof. p-solvable + abelian Sylow-2 + `O_{p'}=1` + `P=C_G(Z(P))` ⇒ `J(P) ⊴ G` |
| 7C | 3898-3949 | **Thompson normal p-complement (= Thm 7.1) の証明** | 7.7, 7.1 (proof) | **Lem 7.7 N/C 系の `p'`-quotient** (Lem 2.17 拡張), **Thm 7.1 proof** — 7 step counterexample-minimum 引数. **Ch.6 Thm 6.23 を完備化** |
| 7D | 3951-4053 | **Burnside p^a q^b** (character-free) | 7.8 | **Thm 7.8 Burnside `p^a q^b` ⇒ solvable** — Goldschmidt-Bender-Matsuyama 9 step proof. p/q-type maximal subgroup, p/q-central, `J(S)` Thompson factorization |

### § 7A — J(P) definition + GL(2,p) lemma + normal-P theorem (lines 3715-3826)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 7.1 | Theorem (statement only) | **(Thompson)** `p ≠ 2`, `P ∈ Syl_p(G)`, `C_G(Z(P))` と `N_G(J(P))` が normal p-complement を持つ ⇒ G が normal p-complement を持つ. 証明は §7C | L3721 |
| 7.2 | Lemma | `J(P) ⊆ Q ⊆ P` ⇒ `J(P) = J(Q)`. 特に `J(P)` は Q 内 char | L3733 |
| 7.3 | Lemma | **(GL(2,p) 補題)** `G = GL(2,p)`, `p ≠ 2`, P ⊆ G p-subgroup, P ⊆ N_G(L), `(\|L\|, p) = 1`, L の Sylow-2 abelian ⇒ `P ⊆ C_G(L)` | L3739 |
| 7.4 | Lemma | `q` odd ⇒ `SL(2,q)` 内の唯一 involution は `-I` (Cayley-Hamilton + minimal polynomial 経由) | L3765 |
| 7.5 | Theorem | **normal-P theorem**: (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) G が p-group V に忠実作用, (v) `\|V:C_V(P)\| ≤ p` ⇒ `P ⊴ G`. **Thm 7.6 の中核 step (8 Step)** | L3783 |

### § 7B — normal-J theorem (lines 3828-3896)

`### 7b` (L3828) で section 開始. Thm 7.6 の証明本体 (8 ステップ) を含む.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 7.6 | Theorem | **normal-J theorem**: (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) `O_{p'}(G) = 1`, (v) `P = C_G(Z(P))` ⇒ `J(P) ⊴ G`. **BG Theorem 6.2 の odd-order 等価版** | L3832 |

### § 7C — Thm 7.1 proof + p'-quotient lemma (lines 3898-3949)

`**7C**` (L3898) インラインマーカー (`###` ヘッダ抽出失敗) で section 開始. Ch.6 Thm 6.23 の完備化が主目的.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 7.7 | Lemma | `N ⊴ G` が p'-subgroup, P ⊆ G が p-subgroup ⇒ (a) `N_{G/N}(PN/N) = N_G(P)·N/N` (= Lem 2.17), (b) **`C_{G/N}(PN/N) = C_G(P)·N/N`** | L3902 |
| 7.1 | (proof) | Thm 7.1 の証明 (Steps 1-7): counterexample-minimum + Frobenius 5.26 + normal-J 7.6 結合 | L3913 |

### § 7D — Burnside p^a q^b (lines 3951-4053)

> ✅ **COMPLETE (2026-05-27)** — `OddOrder.Isaacs.Ch07.burnside_p_pow_q_pow` は標準 3 公理
> (`propext`/`Classical.choice`/`Quot.sound`) のみに依存する **unconditional な theorem**。
> Steps 1-9 全て sorry/project-axiom 無し。`#assert_only_allowed_axioms` で回帰ガード済み。
> 最後の関門だった `step3_main` の faithful-action 分岐は **sub-axiom 無し**で wire 完了
> (generation は Ch06 Thm 6.21 `nontrivialActionFixedByClosure_eq_top_of_not_isCyclic`)。
> 詳細は [issues/closed/0032](../../issues/closed/0032-isaacs-ch07-thm-7-8-burnside.md)。
> ⚠ 本ノート下部の forward-axiom 表 (`hMinCounterexample` 記載) は discharge 前の旧情報で stale。

`### 7D` (L3951) で section 開始. character-free 証明 (Goldschmidt + Bender + Matsuyama). Thompson 局所解析の応用例.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 7.8 | Theorem | **(Burnside)** `\|G\| = p^a q^b` ⇒ G solvable. **character 不使用**. 9 step proof: (1-3) maximal subgroup の p/q-type 二分性, (4) 各 p-subgroup が p-central centralized, (5-6) **`q`-central 元は非自明 p-subgroup を normalize しない**, (7) `p ≠ 2 ∧ q ≠ 2` (Thm 2.13 経由), (8) p-type maximal で `J(S) ⊴ M` (normal-J theorem 7.6 適用), (9) Thompson factorization 矛盾 | L3955 |

## mathlib カバレッジ

**Ch.7 主要結果のうち直接利用可は事実上ゼロ**. 全て新規実装. 周辺概念 (Coatom, Subgroup, Sylow, IsPGroup, IsSolvable, IsNilpotent, MonoidHom.transfer, focalSubgroup) は既存だが Ch.7 statement 自体への mathlib 対応は無い.

### 直接利用できるもの (周辺 API のみ、Ch.7 statement 直接は無し)

| Isaacs | mathlib | 備考 |
|---|---|---|
| `Subgroup.IsCoatom` (Thm 7.1, 7.8 で "maximal subgroup of G") | `Mathlib/Order/Atoms.lean` `IsCoatom` + `Mathlib/GroupTheory/Frattini.lean` `frattini_le_coatom` | maximal subgroup を `IsCoatom` で表す慣習 |
| `IsPGroup` (Sylow, p-group) | `Mathlib/GroupTheory/PGroup.lean` | 基本 API |
| `Sylow p G` | `Mathlib/GroupTheory/Sylow.lean` | |
| `IsSolvable` | `Mathlib/GroupTheory/Solvable.lean` | Thm 7.8 結論 |
| `IsNilpotent` | `Mathlib/GroupTheory/Nilpotent.lean` | Thm 7.1 結論 (normal p-complement) との橋渡し |
| `MulAction` 系 (Thm 7.3, 7.5 内の "G acts on V") | `Mathlib/GroupTheory/GroupAction/*.lean` | 基本 API |
| `SpecialLinearGroup n F` (Lem 7.3, 7.4) | `Mathlib/LinearAlgebra/SpecialLinearGroup.lean` | 行列構造のみ. p-subgroup 引数は新規 |
| `GeneralLinearGroup n F` | `Mathlib/LinearAlgebra/GeneralLinearGroup.lean` | 同上 |
| Aut(E) ≅ GL(n,p) for E elementary abelian | mathlib **未収載** (elementary abelian def 自体無し) | 新規 |
| **normal p-complement existence** | `Mathlib/GroupTheory/Transfer.lean` `MonoidHom.ker_transferSylow_isComplement'` (Isaacs 5.13 Burnside) | **API はあるが Ch.7 が要求する "G has normal p-complement" 概念の def** は要整備 (例: `def Group.HasNormalPComplement G p := ∃ K, K.Normal ∧ ...`) |
| Frobenius normal p-complement (Thm 5.26, Thm 7.1 内部使用) | **mathlib 未収載** (Ch.5 ノート参照) | 新規 |

### 新規実装が必要な主要項目

| Isaacs | 状況 | コスト見積もり |
|---|---|---|
| **`def IsElementaryAbelian (P : Subgroup G) (p : ℕ)`** | mathlib 完全未収載 (elementary abelian 概念自体無し). 候補: `P.IsCommutative ∧ Subgroup.exponent P = p`, または `P` が p-group かつ exponent ∣ p. 中核 def | **大** (Phase 1 設計判断: bundle として `IsElementaryAbelianPGroup G p` を `OddOrder.GroupTheory` 配下に置くか) |
| **`def Subgroup.thompsonJ (P : Subgroup G)`** = `⨆ E ∈ E(P), E` (最大位数 elementary abelian の生成) | mathlib 完全未収載. **章の中核 def**. `E(P)` (maximal-order elementary abelian の集合) も def | **大** (`E(P)` def + `J(P)` def + Lem 7.2 char 性) |
| 7.1 statement (Thompson normal p-complement) | mathlib 未収載 | **大** (statement の前に `def HasNormalPComplement G p` 自体が必要) |
| 7.1 proof | 7.6 + 5.26 + 2.17 (Lem 7.7) 結合. counterexample-minimum 7 step | **大** |
| 7.2 J(P) char | mathlib 未収載. 短い (def 直後の系) | 短い |
| **7.3 GL(2,p) 補題** | mathlib `SpecialLinearGroup` 上で全く新規. induction on `\|L\|` + Sylow + コプライム作用 + Hall-Higman (3.21) | 大 |
| 7.4 SL(2,q) unique involution = -I | mathlib `SpecialLinearGroup 2 (ZMod p)` 上で行列計算 + Cayley-Hamilton 引数 | 中 |
| **7.5 normal-P theorem** | 8 step proof. **Sylow conjugacy + GL(2,p) embedding (Aut(E) for E elem ab) + Hall-Higman 1.2.3 (3.21) + Thm 7.3 + 6.11** の総動員. 章内最重 | **大** |
| **7.6 normal-J theorem** | 8 step proof. 6.20 (abelian coprime ⟨C_N(a)⟩=N), Hall-Higman 3.21, 4.35 (Ω₁ fixed), 7.5 経由. **BG App.A の Thm A.4(b) 等価** | **大** |
| 7.7 N/C `p'`-quotient | Lem 2.17 (= mathlib `Subgroup.normalizer` 系) の単純拡張. correspondence theorem | 短い |
| **7.8 Burnside `p^a q^b`** | 9 step proof. 局所解析の集大成. `p`-central / `q`-central 元の定義 + Thompson factorization. **character-free, 全章のクライマックス** | **大** |

### mathlib カバレッジ概観

| 種別 | 数 | 比率 |
|---|---|---|
| 直接利用可 (周辺 API のみ、statement 直接は 0) | 0 / 8 | 0% |
| 同等概念有り、ラッパー必要 (7.4 行列計算は `SpecialLinearGroup` 上に書ける) | 1 / 8 | 13% |
| 新規実装が必要 | 7 / 8 | **87%** |

Ch.6 (mathlib ~21%) を下回り **Phase 1 内で最も新規実装中心の章**. Ch.1 (Sylow) と並ぶ「重い章」だがそちらは mathlib `Sylow.lean` で大半カバー済なのに対し, Ch.7 は **mathlib 上で全く未開拓の地形**.

## 下流被引用 (Isaacs Ch.8+, BG, Peterfalvi)

### Isaacs Ch.8-10 内 (mmd L4059-末尾を grep)

```
0 件: いずれの Theorem/Lemma 7.X も Ch.8-10 本文で 引用されない.
```

⇒ **Isaacs FGT 内では Ch.7 は完全な「葉」**. ただし **Ch.6 Thm 6.23 を本章 Thm 7.1 が完備化** する関係で、Ch.6 (Frobenius kernel nilpotent 6.24) が **論理的に Ch.7 完了に依存**. Isaacs 内で言えば Ch.7 → Ch.6 (補完方向) という双方向依存が一意に存在.

### BG での引用 (`references/bg/local-analysis.mmd`)

**BG にとって Ch.7 は局所解析の最重要前提**. Thompson subgroup `J(P)` は **BG L5586 で記法集に登録**され、`Z(J(S))` を normalizer に持つ subgroup として **BG §6, §8, §9, App.A, App.B で繰り返し中核的に使用**:

| BG 箇所 | Isaacs Ch.7 対応 | 概要 |
|---|---|---|
| **L5586 (記法集)** | J(P) | "`J(P)` Thompson subgroup of `P`, p.49" — BG の中核記法 |
| **L5770-5772 (索引)** | ZJ-subgroup, ZJ-theorem | "`ZJ`-theorem, **49**, 55" + "`ZJ`-subgroup, 139" — App.B Puig 代替がここで再登場 |
| **L1971-1973 Theorem 6.1** | Thm 7.6 系 (BG App.A Thm A.4(b) 経由) | "`p` odd, G solvable odd, S Syl_p ⇒ `O_{p',p}(G)` contains every abelian normal subgroup of S" — Isaacs 7.6 の **応用形** (J(P) を含む normal abelian の包含) |
| **L1975-1977 Theorem 6.2** | **Thm 7.6 (normal-J) 等価** | "G solvable odd, p prime, S Syl_p ⇒ `Z(J(S))·O_{p'}(G) ⊴ G`" — **Isaacs Thm 7.6 と odd-order 仮定下で完全等価**. BG 本体での Thm 7.6 への直接被引用. |
| **L2456 (§8.1 proof)** | Thm 7.6 | "By (8.9) and Theorem 6.2, we know that `Z(J(P)) ⊴ M`. Consequently `N_G(P) ⊆ N_G(Z(J(P))) = M`" |
| **L2482 (§8.1 proof)** | Thm 7.6 | "By (8.9), (8.13), and Theorem 6.2, `M = N_G(Z(J(R))) = H`" |
| **L2511 (§9.1 proof)** | Thm 7.6 | "By Theorem 6.2, `O_{p'}(M)·Z(J(P)) ⊴ M`. Therefore, by Frattini..." |
| **L2515 (§9.1 proof)** | Thm 7.6 | `N_G(P) ⊆ N_G(Z(J(P))) = M` を用いて Uniqueness Theorem の核心 |
| **L4452 App.A 序文** | Thm 7.6 + 7.5 + 7.3 一式 | "Among the main tools for shortening the first half of the proof of **FT** are Theorems 6.1 and 6.2, which are obtained by use of the concept of `p`-stability. In Section 6 these are obtained from theorems in **G** [= Gorenstein 1968]. These have shorter proofs if one restricts to groups of odd order and uses a different characteristic subgroup in place of `J(S)`." **App.A 全体が Isaacs Ch.7 を odd-order 仮定で再構築** |
| **L4476 Thm A.3** | Thm 7.5 + 7.3 結合 | "p odd, G with no nontrivial p-subgroups, G is not p-stable ⇒ G has even order" — Isaacs Thm 7.3 + Thm 7.5 の合成. **奇数位数仮定下の p-stability** |
| **L4480 Thm A.4** | **Thm 7.6** | "p odd, G solvable odd, P p-subgroup ⇒ (a) `O_p(G)=1 ⇒ G is p-stable`, (b) **`P ∈ Syl_p(G) ⇒ every normal abelian subgroup of P is in O_{p',p}(G)`** ← Thm 6.1, (c) `O_{p'}(G)·P ⊴ G ∧ A p-subgroup of N_G(P) with [P,A,A]=1 ⇒ AC_G(P)/C_G(P) ⊆ O_p(N_G(P)/C_G(P))`" |
| **L4488 Thm A.5** | Thm 7.6 系 | "p odd, G solvable odd, P ◁ G p-subgroup, X = ⟨abelian p-groups normalized by P⟩ ⇒ (1) X·C_G(P)/C_G(P) ⊆ O_p(G/C_G(P)), (2) `O_{p'}(G)=1 ∧ C_{O_p(G)}(P) ⊆ P ⇒ X ⊆ O_p(G)`" — Isaacs 7.6 を `X` 一般化 |
| **L4517-4540 App.B** | Thm 7.6 代替 (Puig `L(S)`) | "In this appendix we will define an important characteristic subgroup ... similar to the properties of the Thompson J-subgroup described in **G**, Chapter 8." **App.B が J(S) を Puig L(S) に置き換えた変種** — Theorem B.4 = Thm 7.6 の odd-order substitute |
| **L5014-5044 App.D Lemma D.1** | Thm 7.6 | Sibley の論証で "Let `N = N_G(Z(J(P)))` (One may substitute `L(P)` for `J(P)` ...). Theorem 6.2 ⇒ `Z(J(P))·O_{p'}(M) ⊴ M`" — `CN`-theorem 代替に使用 |
| L825 Note | Ch.6 6.24 (経由) | "Thompson's Thesis ... implies kernel nilpotent" — Ch.6 6.24 を BG が借用 |

⇒ **BG §6-§9 (Uniqueness Theorem 周辺) + App.A (p-stability) + App.B (Puig L(S)) + App.D (CN-theorem) で Isaacs Thm 7.6 が 7 ヶ所超で直接被引用**. **Thm 7.6 こそ BG にとって Ch.7 最重要**. Thm 7.5, 7.3 も App.A 内で再述. Thm 7.1 (Thompson normal p-complement) は BG では Ch.6 6.24 経由で間接利用 (Frobenius kernel nilpotent の前提として).

**注**: BG は `**G**` (= Gorenstein 1968) 引用スタイルで, Isaacs 番号は引かない. ただし `Z(J(S))·O_{p'}(G) ⊴ G` という同一 statement と J(P) Thompson 起源を介して Ch.7 との対応は明確.

### Peterfalvi での引用 (`references/peterfalvi/*.mmd`)

Peterfalvi 本体 §1-§16 (character theory) では **Thompson subgroup J(P), ZJ, normal-J/P theorem の直接出現はゼロ**. これは指標論ベースの議論で局所解析は [BG] 既知扱いだから:

```
J(P), Z(J(, Thompson subgroup, p-stability 全マッチ: 0 件 (Peterfalvi 本体)
```

ただし **Peterfalvi §8 が [BG] §16 (= [BG] Theorem A-E の系) を Theorem (8.8), (8.13) として翻訳** (Peterfalvi 04.17 Notes L15): "§8. Theorems (8.8) and (8.13) correspond to Theorems 14.1 and 14.2 of [FT]". これらは BG §10-§14 の Uniqueness Theorem 系で **そこに Isaacs Thm 7.6 が前提として埋め込まれている**.

Peterfalvi 付録 (05.X, 06.0, 07.0) でも Ch.7 内容は直接使われない (Suzuki 定理 / Huppert / Near-field は permutation group / 表現論側).

⇒ **Peterfalvi にとって Ch.7 は "BG 経由で既知"** のレイヤー. Phase 2b 本体に進む前に Phase 2a (BG) を経由する必要があり、Phase 2a で Ch.7 への依存が顕在化.

### 比較表: Ch.7 結果の FT クリティカル度

| Isaacs | BG での被引用 | Peterfalvi での被引用 | FT クリティカル度 |
|---|---|---|---|
| **7.1 Thompson normal p-comp** | Ch.6 6.24 経由 (Frobenius kernel nilpotent) | 無し (BG 経由) | **HIGH** (6.24 完備化に必須) |
| 7.2 J(P) char | App.B Lem B.1 (a) で類似 | 無し | MEDIUM (def 直後の系) |
| **7.3 GL(2,p) p-sub centralize** | App.A Thm A.1 で類似 (2 次元 irreducible) | 無し | MEDIUM (Thm 7.5, 7.6 の補題) |
| 7.4 SL(2,q) -I unique inv | App.A 周辺で類似引数 | 無し | LOW (Thm 7.3 の補題) |
| **7.5 normal-P theorem** | App.A Thm A.3, A.4(c) 経由 | 無し | **HIGH** (Thm 7.6 の核 step) |
| **7.6 normal-J theorem** | **§6 Thm 6.2 + §8, §9 で 7 ヶ所直接, App.A Thm A.4(b)** | 無し (BG 経由) | **HIGHEST** |
| 7.7 N/C `p'`-quotient | (Lem 2.17 + 拡張) | 無し | LOW |
| 7.8 Burnside `p^a q^b` | L2633 で言及のみ | 無し | LOW-MEDIUM (Phase 1 完成度) |

## 章内依存 (Ch.7 内で 7.X が引用される頻度)

`awk` で Ch.7 本文 (L3713-4058) を切り出し grep:

```
最頻 被引用 (証明本文中):
- 7.1  (Thompson normal p-comp)  — 9 回 (statement + §7C proof 内自己参照)
- 7.3  (GL(2,p) 補題)             — 8 回 (Thm 7.5, 7.6 で多用)
- 7.5  (normal-P theorem)         — 4 回 (Thm 7.6 step 8 で適用 + Burnside 7.8 で間接)
- 7.6  (normal-J theorem)         — 4 回 (Thm 7.1 step 7 + Burnside 7.8 step 8)
- 7.4  (SL(2,q) -I)               — 2 回 (Thm 7.3 proof + Thm 7.5 proof)
- 7.8, 7.7, 7.2                  — 1 回ずつ
```

**章内ハブ**:
- §7A: 7.2 (J(P) char) → 7.3 (GL(2,p)) → 7.4 (SL(2,q) -I) → 7.5 (normal-P)
- §7B: (7.3, 7.5 + Ch.6 6.20 + Ch.3 3.21) → **7.6 (normal-J)** — 章のハイライト
- §7C: (Ch.5 5.26 Frobenius normal p-comp + 7.6 normal-J + 7.7 N/C quotient) → **7.1 (Thompson)**
- §7D: (7.6 + Ch.2 2.13 Baer + Ch.4 4.33) → **7.8 (Burnside `p^a q^b`)**

**証明依存の強い軸**:
- 7.3 → 7.5 → 7.6 → 7.1 (Frobenius kernel nilpotent への王道)
- 7.6 → 7.8 (Burnside の Thompson factorization は 7.6 を maximal subgroup M に適用)
- 6.23 (Ch.6) → 7.1 (Ch.7) → 6.24 (Ch.6 完備化) ← **Ch.6/Ch.7 間の唯一の双方向依存**

## 着手状況 (2026-05-26)

- ✅ shared module `OddOrder/GroupTheory/ElementaryAbelian.lean` (`IsElementaryAbelian`).
- ✅ shared module `OddOrder/GroupTheory/ThompsonSubgroup.lean` (`Subgroup.thompsonJ` def + Thm 7.2).
- ✅ Thm 7.2 in [`Main.lean`](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean) (shared module wrapper).
- ✅ **Lem 7.4** SL(2,q) odd の唯一 involution = -I (sorry-free, ~100 行).
- ✅ **Lem 7.7** N/C 系 p'-quotient (`centralizer_map_of_coprime_kernel`, sorry-free, ~80 行).
- ✅ **Lem 7.3** GL(2,p) 補題 (`gl2_pSubgroup_centralizes_of_normalizes`, sorry-free).
  `|L|`-induction + P-invariant Sylow + Ch.4 coprime action + Lem 7.4 + finite abelian
  2-group cyclicity branch + odd-q orbit-count branch.
- 🔧 **Thm 7.5** action infrastructure 着手: faithful action `G ↪ Aut(V)` の Lean bridge
  (`toMulAut_injective_of_faithful`, `subgroupOfMulAutAction`), `C_V(P)` notation
  (`actionCentralizer`), conjugacy step `C_V(P^g)=C_V(P)^g`
  (`actionCentralizer_map_conj`), generated-subgroup fixed-point step
  `C_V(P⊔Q)=C_V(P)∩C_V(Q)` (`actionCentralizer_sup`) を sorry-free で追加.
  さらに `U=C_V(P)∩C_V(Q)` 形式の index bound
  (`actionCentralizer_inf_index_le_sq`), `P⊔Q=⊤` から `U` が action-invariant になる bridge
  (`actionCentralizer_inf_isAInvariant_of_sup_eq_top`), 商 `V/U` 上の index 保存
  (`actionCentralizer_quotient_image_index_eq_of_le`), quotient action と kernel `K`
  (`quotientActionHom`, `quotientActionKernel`), `[V,K]≤U` bridge
  (`actionCommutator_quotientActionKernel_le`), `[V,K,K]=1` bridge
  (`actionCommutator_quotientActionKernel_le_fixedPoints`), faithful action + `V` p-group から
  `K` p-group まで (`quotientActionKernel_isPGroup_of_faithful_of_isPGroup`) 追加済み.
  また quotient-by-kernel action の faithful form
  (`quotientActionFaithfulHom`, `quotientActionFaithfulHom_injective`) も追加済み.
  商作用下で `C_V(P)/U` が `P̄` に固定され, index bound `≤ p` が保たれる bridge
  (`actionCentralizer_quotient_image_le_quotientActionFaithful_actionCentralizer`,
  `actionCentralizer_quotientActionFaithful_index_le`) も追加済み.
  商 `G/K` 側で得た Sylow image の normality を元の `P` に戻す quotient/Sylow bridge
  (`normal_of_quotient_image_normal_of_le`,
  `sylow_normal_of_quotient_image_normal_of_normal_isPGroup`) も追加済み.
  さらに quotient 後も `P̄,Q̄` が異なる Sylow として残り, `P̄` normality が元の
  counterexample 仮定と矛盾することを使う bridge
  (`quotient_sylow_images_ne_of_ne_of_normal_isPGroup`,
  `quotient_sylow_image_not_normal_of_not_normal_of_normal_isPGroup`) も追加済み.
  商群側の任意の 2-subgroup abelian 仮定は Sylow lift 経由で
  `quotient_two_subgroup_abelian` により継承可能. p-separable 仮定は Ch03 既存
  `quotient_isPiSeparable` instance を直接使えばよく, Ch07 wrapper は不要.
  minimal-counterexample descent 用の `|G/K| < |G|` は repo-local mathlib helper
  `Subgroup.card_quotient_lt_of_ne_bot` に集約済み.
  `G/K ↷ V/U` が elementary-abelian order `p^2` の reduced branch に入った場合は,
  `quotient_sylow_normal_of_elementaryAbelian_card_prime_sq_of_actionKernel` と
  contradiction form
  `false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal` で閉じられる.
  cyclic quotient branch も `quotient_sylow_normal_of_isCyclic_of_actionKernel` と
  `false_of_quotient_isCyclic_of_sylow_not_normal` で quotient action から
  counterexample contradiction へ戻せる.
  さらに order `p^2` の elementary abelian quotient の `Aut(V) ≃ GL(2,p)` bridge
  (`mulAutGLTwoEquivOfIsElementaryAbelianCard`) と, Lem 7.3 の GL 側結論を `Aut(V)` 側へ戻す
  transfer (`mulAut_centralizes_of_gl2_image_hypotheses`), さらに faithful action 経由で
  元の作用群側へ戻す
  (`le_centralizer_of_map_le_centralizer_of_injective`,
  `subgroup_centralizes_of_mulAut_gl2_image_hypotheses`) を追加済み. 7.5 の
  `|V| ≤ p^2` reduction 用に
  `IsPGroup.isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic`
  も追加済み. さらに `GL(2,p)` に埋めた後の cardinality step
  `gl2_pSubgroup_card_le_prime` (`p`-subgroup of `GL(2,p)` has order `≤ p`) も追加済み.
  この bound と `P` 非正規性から `O_p(G)=1` へ落とす
  `opCore_eq_bot_of_sylow_card_le_prime_of_not_normal` も追加済み.
  さらに `O_p(G)=1` から Hall-Higman を `π={p}'` 側へ適用する
  `centralizer_oPiCore_compl_le_of_opCore_eq_bot` も追加済み.
  その結論で `P ≤ O_{p'}(G)` になった後の coprime contradiction
  `sylow_eq_bot_of_le_oPiCore_compl` も追加済み.
  さらに reduced elementary-abelian branch の Lem 7.3 仮説 adapter
  (`map_le_normalizer_map_of_normal`,
  `not_dvd_card_map_of_isPiGroup_compl_of_injective`,
  `two_subgroup_abelian_of_le_map_of_injective`) と, 7.5 後半そのものを閉じる
  `sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful` を追加済み.
  `U=C_V(P)∩C_V(Q)` quotient で `|V/U|≤p^2`, 非巡回なら elementary
  abelian order `p^2` へ落とす
  `quotient_card_le_prime_sq_of_actionCentralizer_inf` と
  `quotient_isElementaryAbelian_card_prime_sq_of_actionCentralizer_inf_not_isCyclic`
  も追加済み. cyclic quotient branch は
  `false_of_quotient_isCyclic_of_sylow_not_normal` で `P ⊴ G` contradiction まで
  戻せる.
  theorem statement / proof 本体は保留.
- 2026-05-26: 7.5 minimal-counterexample reduction 用に Ch03 側へ
  `Subgroup.isPiSeparable_of_isPiSeparable` を追加済み. これで `G` を
  `⟨P,Q⟩` に置き換えるときの p-separable 仮定は `P⊔Q` 専用 wrapper なしで継承できる.
- **2026-05-26 ✅ Thm 7.5 top-level 完成**: `sylow_normal_of_elementary_normal_P_theorem`
  ([Main.lean:2515](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean#L2515),
  ~150 LOC + 1 helper `actionCentralizer_comp_subtype_index_le_of_globalHypothesis`).
  Proof: strong induction on `Nat.card G` + generation reduction `⟨P,Q⟩ ≠ ⊤` を
  IH に落とす + closing branch (`⟨P,Q⟩ = ⊤`) で `U = C_V(P) ⊓ C_V(Q)` から
  cyclic/elementary p² の dichotomy を `false_of_quotient_*` で閉じる.
  既存 §7A bridge (1568-2460) を 1 行も追加せず assembly のみ. Sorry-free.
- **2026-05-26 ✅ Thm 7.6 normal-J conditional 完成**: `normal_J.{u}`
  ([Main.lean:2712](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean#L2712),
  ~85 LOC). Strong induction on `Nat.card G` + 普遍量化された
  `hMinCounterexample` を forward-dep として取る. 8-step proof body は
  Hall-Higman corollaries + Ω₁ + Ch.4 4.35 + Ch.6 6.20 + Thm 7.5 を組み合わせて
  back-fill 予定. Sorry-free.
- **2026-05-26 ✅ Thm 7.1 conditional 完成**: `thompson_normal_p_complement`
  ([Main.lean:3005](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean#L3005))
  が `(thompsonJ P p).Normal` を forward-dep 仮説に取って sorry-free で完成.
  Steps 1-6 (normal-J 5 仮説確立) は normal-J 7.6 が landing 後に back-fill.
  Step 7 (`J(P) ⊴ G ⇒ N_G(J(P)) = G ⇒ G has normal p-complement`) は
  `MulEquiv` transport helper `hasNormalPComplement_of_mulEquiv` (~55 LOC)
  + `MulEquiv.subgroupCongr` + `Subgroup.topEquiv` で実現.
- **2026-05-26 ✅ Thm 7.8 Burnside conditional 完成**: `burnside_p_pow_q_pow.{u}`
  ([Main.lean:3073](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean#L3073),
  ~88 LOC). Strong induction on `Nat.card G` + 普遍量化された
  `hMinCounterexample` を forward-dep として取る. 9-step Goldschmidt-Bender-Matsuyama
  proof body は §7D の `IsPCentral` / `IsPType` / `U⋆` 定義 + Thm 7.6 +
  Matsuyama + Thompson factorization で back-fill 予定. Sorry-free.

### back-fill 必要項目 (forward-dep hypothesis 経由で立てた conditional theorem)

| 識別子 | Forward-dep hypothesis | 解消 prerequisite | LOC 見積もり |
|---|---|---|---:|
| `normal_J.{u}` ([Main.lean:2712](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean#L2712)) | `hMinCounterexample` (普遍量化) | §7B 8-step proof: Hall-Higman corollaries + Ω₁ design + Ch.4 4.35 adapter + Ch.6 6.20 adapter + Thm 7.5 application | ~800-1500 LOC |
| `thompson_normal_p_complement` ([Main.lean:3005](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean#L3005)) | `hJ_normal : (thompsonJ P p).Normal` | Thm 7.6 normal-J back-fill (上記) + 7.1 Steps 1-6 | ~300-450 LOC (Steps 1-6) |
| `burnside_p_pow_q_pow.{u}` ([Main.lean:3073](../../OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean#L3073)) | `hMinCounterexample` (普遍量化) | §7D 9-step proof: `IsPCentral` / `IsPType` / `U⋆` 新規 defs (~150 LOC) + 9 steps (Matsuyama + Thm 7.6 + Thompson factorization) | ~600-900 LOC |

## 前提章の再分類 (main 取り込み後)

先行 chapter の進捗により, Ch.7 側で blocker と見なす対象を絞り直す:

- ✅ **Ch.3 Hall-Higman 3.21**: `hall_higman_1_2_3` は sorry-free. Thm 7.5 / 7.6 の Hall-Higman step は利用側の接続問題.
- ✅ **Ch.4 4.33 / 4.35**: p-local `p'`-core 押し込みと abelian p-group coprime action 補題は利用可能.
- ✅ **Ch.5 5.26 + `HasNormalPComplement`**: Thm 7.1 の normal p-complement 側の基礎定義・Frobenius criterion は利用可能.
- ✅ **Ch.7 Lem 7.3 / 7.4 / 7.7**: 7.5 の GL(2,p) 補題と 7.1 の N/C quotient 補題は Ch.7 内で利用可能.
- ✅ **Ch.6 6.11**: Thm 7.5 final reduction の blocker は解消.
  `isCyclic_or_two_quaternion_of_subgroups_card_prime_unique` として,
  `p`-group with at most one subgroup of order `p` ⇒ cyclic / `p = 2`
  generalized quaternion を sorry-free 化済み. 7.5 では `p ≠ 2` 仮定により cyclic
  branch だけを使えばよい.
- ✅ **Ch.6 6.20**: Thm 7.6 Step 5 の blocker は解消.
  `isCyclic_of_faithful_trivial_on_proper_invariant` として, Lemma 6.20 の本文通り
  6.21 から faithful abelian coprime action 補題を sorry-free 化済み.
- ✅ **`Aut(E) ≅ GL(2,p)` bridge**: elementary abelian order `p^2` から Lem 7.3 へ渡す
  automorphism-group bridge は `mulAutGLTwoEquivOfIsElementaryAbelianCard` と
  `mulAut_centralizes_of_gl2_image_hypotheses` として追加済み. faithful action で
  元の作用群側の中心化結論へ戻す
  `subgroup_centralizes_of_mulAut_gl2_image_hypotheses` も利用可能.
- 🟡 **Ω₁ / order-p fixed subgroup helper**: Thm 7.6 Step 7 で必要. Ch.6 6.11 実装で先に共通化できる可能性あり.

## 着手順 (提案)

FT クリティカル度 + 章内依存 + 前提章完了状態で並べる:

1. ✅ **shared definitions + 7.2 / 7.4 / 7.3 / 7.7** — Ch.7 内の独立補題群は完了.
2. 🔧 **7.5 normal-P theorem 前半** — Ch.6 6.11 に依存しない action / centralizer / quotient-action 側を先に固める.
   - ✅ `Q = P^g` から `|V:C_V(Q)| = |V:C_V(P)|` (`actionCentralizer_map_conj_index`).
   - ✅ `U = C_V(P) ∩ C_V(Q) = C_V(⟨P,Q⟩)` と `|V:U| ≤ |V:C_V(P)| |V:C_V(Q)| ≤ p^2`
     (`actionCentralizer_sup`, `actionCentralizer_inf_index_le_sq`).
   - ✅ `V` が finite `p`-group で `|V:C_V(P)|, |V:C_V(Q)| ≤ p` なら
     `U = C_V(P) ∩ C_V(Q)` は normal:
     `normal_of_isPGroup_index_le_prime` と
     `actionCentralizer_inf_normal_of_index_le_prime` で `[U.Normal]` を供給可能.
   - ✅ `G = ⟨P,Q⟩` 仮定下で `U` が action-invariant になり, 既存
     `IsAInvariant.quotientMulAutHom` で quotient action `G ↷ V/U` へ進める
     (`actionCentralizer_inf_isAInvariant_of_sup_eq_top`).
   - ✅ 商 `V/U` 内の `C_V(P)/U` index 保存
     (`actionCentralizer_quotient_image_index_eq_of_le`).
   - ✅ quotient action の kernel `K` と `[V,K]≤U` / `[V,K,K]=1` / `K` p-group 化
     (`quotientActionKernel`, `actionCommutator_quotientActionKernel_le`,
     `actionCommutator_quotientActionKernel_le_fixedPoints`,
     `quotientActionKernel_isPGroup_of_faithful_of_isPGroup`). `U ⊴ V` は上記 bridge で供給.
   - ✅ quotient-by-kernel action: `G/K` が `V/U` に faithful に作用する
     (`quotientActionFaithfulHom_injective`).
   - ✅ quotient action fixed-index transfer: `C_V(P)/U ≤ C_{V/U}(P̄)` かつ
     index bound `≤ p` を faithful quotient action 側へ移す
     (`actionCentralizer_quotientActionFaithful_index_le`).
   - ✅ quotient/Sylow normality pullback: `K` が normal `p`-subgroup なら `K ≤ P`;
     `G/K` 側の `P̄` normality から元の `P` normality へ戻す
     (`sylow_normal_of_quotient_image_normal_of_normal_isPGroup`).
   - ✅ quotient counterexample bridge: `K ≤ P,Q` なら `P ≠ Q` は quotient image の
     distinctness として残り, quotient image の normality は元の `P` normality に戻って矛盾
     (`quotient_sylow_images_ne_of_ne_of_normal_isPGroup`,
     `quotient_sylow_image_not_normal_of_not_normal_of_normal_isPGroup`).
   - ✅ quotient theorem-condition inheritance: p-separable は Ch03
     `quotient_isPiSeparable`; 任意の 2-subgroup abelian は `quotient_two_subgroup_abelian`.
   - ✅ minimality cardinal descent: `K ≠ ⊥` なら `|G/K| < |G|`
     (`Subgroup.card_quotient_lt_of_ne_bot`).
   - ✅ quotient reduced branch: `G/K ↷ V/U` が elementary abelian order `p^2` の場合,
     reduced Thm 7.5 branch から `P̄ ⊴ G/K`, さらに `P ⊴ G` contradiction へ戻せる
     (`false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal`).
   - ✅ quotient cyclic branch: `G/K ↷ V/U` で `V/U` cyclic の場合も
     `P̄ ⊴ G/K` から `P ⊴ G` contradiction へ戻せる
     (`false_of_quotient_isCyclic_of_sylow_not_normal`).
   - ✅ `|V| ≤ p^2` かつ非 cyclic な finite `p`-group から
     elementary abelian order `p^2` へ落とす small-order bridge.
   - ✅ cyclic quotient branch: faithful/injective action into `Aut(V)` と `V` cyclic から
     acting group 可換, よって `P` normal.
3. ✅ **Ch.6 6.11** — 7.5 final reduction に必要な cyclic/quaternion 分岐は利用可能.
4. ✅ **`Aut(E) ≅ GL(2,p)` bridge** — elementary abelian order `p^2` の `Aut(E)` を
   `GL(2,p)` に移し, Lem 7.3 の centralizer 結論を戻すところまで完了.
   faithful action から元の作用群側の centralizer 結論へ戻す bridge も完了.
   `GL(2,p)` 内の `p`-subgroup cardinality bound `gl2_pSubgroup_card_le_prime` も追加済み.
   その bound から `O_p(G)=1` に落とす bridge
   `opCore_eq_bot_of_sylow_card_le_prime_of_not_normal` も利用可能.
   final Hall-Higman step 用の `p'`-core self-centralizing bridge
   `centralizer_oPiCore_compl_le_of_opCore_eq_bot` も利用可能.
   reduced elementary-abelian case から normality を返す
   `sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful` まで完了.
5. **7.5 normal-P theorem 本体** — 7.3 + Ch.6 6.11 + Hall-Higman 3.21 で contradiction を閉じる.
   残りは minimal-counterexample / quotient-kernel reduction をこの reduced branch へ接続する部分.
6. ✅ **Ch.6 6.20** — 7.6 Step 5 の直接前提は利用可能.
7. **7.6 normal-J theorem** — 7.5 + Ch.6 6.20 + Ch.4 4.35 + Hall-Higman 3.21. **章のハイライト**.
8. **7.1 Thompson normal p-complement** — Ch.5 5.26 + 7.6 + 7.7. Ch.6 6.23 をここから backfill.
9. **Ch.6 6.23 / 6.24 backfill** — 7.1 から Thompson char-X 版と Frobenius kernel nilpotent を完備化.
10. **7.8 Burnside `p^a q^b`** — 7.6 + Ch.4 4.33 + Ch.2 2.13 Baer. **BG/Peterfalvi 直接被引用は薄いので最後**.

優先度 (FT クリティカル度 + 現在の到達可能性):
**7.5 本体 assembly** → **7.6** → **7.1 / Ch.6 backfill** → **7.8**.

## 開発時の注意点

### 設計判断 (1): `IsElementaryAbelian` と `J(P)` の def

Isaacs L3727 の定義: 「`P` の elementary abelian 部分群のうち最大位数のものの集合 `E(P)`, `J(P) = ⟨E(P)⟩`」.

Lean 候補:

```lean
/-- A subgroup is elementary abelian for prime `p` if it is a p-group with exponent dividing p. -/
def IsElementaryAbelian (H : Subgroup G) (p : ℕ) : Prop :=
  IsPGroup p H ∧ Monoid.exponent H ∣ p
-- 同等: H が abelian かつ 全 h ∈ H で h^p = 1

/-- The set of elementary abelian subgroups of `P` of maximum order. -/
def maxElemAbelianSubgroups (P : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {E | E ≤ P ∧ IsElementaryAbelian E p ∧
       ∀ F ≤ P, IsElementaryAbelian F p → Nat.card F ≤ Nat.card E}

/-- **Isaacs Ch.7 def**: Thompson subgroup of a p-group. -/
def Subgroup.thompsonJ (P : Subgroup G) (p : ℕ) : Subgroup G :=
  ⨆ E ∈ maxElemAbelianSubgroups P p, E
```

- **設計判断 A**: `p` を bundle 内に持つか引数で取るか. `P ∈ Syl_p(G)` 文脈では `p` が外側で固定なので引数で取るほうが自然.
- **設計判断 B**: `IsElementaryAbelian` を `Mathlib` 風スタイルで先に作って upstream 視野. `OddOrder.GroupTheory.ElementaryAbelian` ファイル.
- **注意**: Isaacs L3729 で `J(P)` の **代替定義** (Thompson 原版 = abelian subgroups of largest *rank*, Aschbacher = abelian subgroups of largest *order*) が言及される. Isaacs の `J(P)` は elementary abelian of largest *order* で、**Thompson 原版より小さい可能性がある** (例: `P` abelian non-elementary). Lean では Isaacs 版を採用するが、wrapper で他版との関係を docstring に明記.

### 設計判断 (2): `HasNormalPComplement` def

Thm 7.1 / 7.8 / Ch.6 6.23 / Ch.5 5.26 で繰り返し出る "G has normal p-complement". mathlib `Mathlib/GroupTheory/Transfer.lean` には `MonoidHom.ker_transferSylow_isComplement'` という形で個別 lemma がある (Isaacs 5.13 Burnside) が、**`Group.HasNormalPComplement G p` の def 自体は未収載**.

候補:

```lean
/-- G has a normal p-complement: there exists a normal p'-subgroup K with G = P × K
    for any Sylow p-subgroup P. -/
def Group.HasNormalPComplement (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ K : Subgroup G, K.Normal ∧ IsPGroup p (G ⧸ K) ∧
    ∀ x ∈ K, ¬ p ∣ orderOf x
-- 同等: ∃ K, K.Normal ∧ K is a p'-Hall ∧ ∃ Sylow p P, P ⋊ K = G
```

- mathlib `Sylow.ker_transferSylow_isComplement'` (Transfer.lean L275) の存在から `IsComplement'` 形で書く方が `transferSylow` API と直結.
- Ch.5 5.26 Frobenius normal p-complement 実装時に決定すべき def. **Ch.5 ノートで先に決めるか、Ch.5 と Ch.7 同時着手か** が悩みどころ.

### 設計判断 (3): `GL(2,p)`, `SL(2,q)`, `Aut(E)` の橋渡し

Thm 7.3, 7.4 は **行列計算と抽象群論の境界**:
- mathlib `Mathlib/LinearAlgebra/SpecialLinearGroup.lean` `SpecialLinearGroup n F` (行列 perspective)
- mathlib `Mathlib/LinearAlgebra/GeneralLinearGroup.lean` `GeneralLinearGroup n F`
- mathlib **未収載**: `Aut(E) ≅ GL(n, p)` (E elementary abelian of order `p^n`)

⇒ `def AutOfElemAbelian {p : ℕ} [Fact p.Prime] (E : Type*) [Group E] (hE : IsElementaryAbelian (⊤ : Subgroup E) p) : MulAut E ≃* GeneralLinearGroup (Module.rank (ZMod p) E) (ZMod p)` の形が必要. **Ch.7 で新規実装**.

Thm 7.5 の Steps 6-8 (`G ≅ subgroup of GL(2,p)`) はこの bridge を経由する.

### Hall-Higman 3.21 への依存

Thm 7.5 (Step) と Thm 7.6 Step 1 で **`p`-solvable + `O_{p'}(G) = 1` ⇒ `C_G(O_p(G)) ⊆ O_p(G)`** (Hall-Higman 1.2.3 = Isaacs Thm 3.21) を本質的に使用. **Ch.3 §3D 完了が Ch.7 着手の必須前提**. Ch.3 ノートが Hall-Higman を「**FT クリティカル**」とマークしているのはここを見据えてのこと.

具体的依存:
- Thm 7.5: 最終段で `P ⊆ C_G(L) ⊆ L` (L = `O_{p'}(G)`) を Hall-Higman で導く.
- Thm 7.6 Step 1(a, c): `Z(P) ⊆ U = O_p(G)` および `C_{\overline{G}}(\overline{L}) ⊆ \overline{L}` を Hall-Higman で導く.

### Ch.6 6.20 (`abelian A coprime, A not cyclic ⇒ N = ⟨C_N(a) | 1 ≠ a ∈ A⟩`)

Thm 7.6 Step 5 で **Lemma 6.20** を直接適用 ("$\overline{A}$ acts coprimely on $\overline{L}$, ... `\overline{A}` cyclic" の引数). Ch.6 ノートで 6.20 が「Ch.7 で 1 回引用」と注記済 (✓ 確認).

### Ch.4 依存

| Isaacs Ch.7 内 | Ch.4 依存 | mmd |
|---|---|---|
| Thm 7.3 proof: `[L,P,P]=[L,P]` (coprime) | **Lemma 4.29** | L3777 |
| Thm 7.6 Step 6 proof: `Q acts coprimely on Z(U)`, `Q fixes Ω₁(Z(U)) ⇒ Q trivial` | **Corollary 4.35** | L3884 |
| Thm 7.8 Step 1 proof: `O_{p'}(M ∩ X) ⊆ O_{p'}(X)` (p-local subgroup) | **Theorem 4.33** | L3971 |

⇒ Ch.4 §4D (coprime action 系) も Ch.7 着手必須前提.

### Ch.2 依存

| Isaacs Ch.7 内 | Ch.2 依存 | mmd |
|---|---|---|
| Lem 7.7 (a): `N_{G/N}(PN/N) = N_G(P)·N/N` | **Lemma 2.17** | L3907 |
| Thm 7.8 Step 7: `q=2 ⇒ ∃ x order p, x^t = x^{-1}` (Baer 系) | **Theorem 2.13** | L4027 |

### Thm 6.23 (Ch.6) のバックエッジ書き換え

Ch.6 ノートが 6.23 を `axiom` / `sorry` 化する案を提示. Ch.7 完了時のスムーズな書き換え経路:

```lean
-- Ch.6 段階: theorem 6.23 (Thompson normal p-complement char-X version) : ... := by sorry
-- Ch.7 完了後: theorem 6.23 (Thompson normal p-complement char-X version) : ... := by
--   intro hCharX
--   apply thompsonNormalPComplement_7_1 -- = Thm 7.1
--   · exact hCharX (J P) (J_characteristic ...)
--   · exact hCharX (center P) ...
```

⇒ Ch.7 で 7.1 を `thompsonNormalPComplement` 等の記述的名で実装し, Ch.6 内で `theorem thompsonNormalPComplement_charSubgroup := ...` として 7.1 の系として再記述. **6.23 → 7.1 の依存が一方向 (Ch.6 から Ch.7) になる形**.

### Burnside `p^a q^b` (Thm 7.8) の独立性

Ch.7 §7D は **Ch.7 §7A-§7C の応用例** という位置づけ. BG/Peterfalvi 本筋で直接被引用は無いが、本書全体の "Thompson 局所解析の強さ" を示す看板定理. **着手は Ch.7 §7A-§7C + Ch.5 5.26 + Ch.4 4.33 が揃ってから**. Bender + Matsuyama + Goldschmidt 引用が必要なら docstring に明記.

### BG / Peterfalvi 橋渡し名

将来 BG/Peterfalvi を書く時に Isaacs 7.X を引用する局面:

- **BG Theorem 6.2 (`Z(J(S))·O_{p'}(G) ⊴ G`)**: Isaacs Thm 7.6 を odd-order 仮定下で再述. `OddOrder.BG.Ch1.S06` で section docstring に "BG Thm 6.2 = Isaacs Thm 7.6 (odd-order specialization)" と明記.
- **BG Theorem 6.1 (`O_{p',p}(G)` contains every abelian normal subgroup of S)**: Thm 7.6 系で導出 (App.A Thm A.4(b)).
- **BG §8.1 Uniqueness Theorem proof**: Thm 7.6 を `N_G(P) ⊆ N_G(Z(J(P))) = M` 経路で繰り返し適用.
- **BG App.A "Prerequisites and p-Stability"**: **Isaacs Ch.7 全体の odd-order 再構築**. Phase 2a 開始時に Isaacs 7.X → BG App.A の対応表を作成必須.

⇒ Phase 1 で Isaacs 7.6 を `normalJTheorem` / `Subgroup.thompsonJ_normal` 等の記述的 Lean 名で実装. BG が `Z(J(S))·O_{p'}(G) ⊴ G` 形で再述するときの記述名は `BG.Ch1.S06.zjThompsonFactorization` 等.

## 未解決の疑問

- **`IsElementaryAbelian` の def 形** — `IsPGroup p H ∧ exponent H ∣ p` か `IsAbelian H ∧ ∀ h, h^p = 1` か. mathlib upstream 視野なら前者 (`exponent` API 直結) が自然.
- **`J(P)` 定義の Isaacs 版 vs Thompson 原版** — Isaacs 版 (elementary abelian of largest order) を実装するか, Thompson 原版 (abelian of largest rank) を実装するか. **Isaacs 版を採用** が ROADMAP 整合, **BG が "J(P)" を Isaacs/Thompson どちらの意味で使うか** は BG §6 周辺の精査要 (BG L5586 は `p.49` で導入されるが BG §1 はまだ Phase 2a 着手前で未読). 注: BG App.B は "different characteristic subgroup `L(S)`" (= Puig) を意図的に使うので, BG 内でも J(P) 版の選択にゆるみがある.
- **`HasNormalPComplement G p` def の置き場所** — Ch.5 ノートが触れているが Ch.5 で実装するか Ch.7 で実装するか. mathlib `Mathlib/GroupTheory/Transfer.lean` の `transferSylow` API 直結なら Ch.5 で実装が自然. Ch.7 はそれを利用する側.
- **`Aut(E) ≅ GL(n,p)` (E elem ab) の def** — mathlib `Mathlib/GroupTheory/SpecificGroups/AddCommGroup` 系には `ZMod p`-module 構造があるが elementary abelian と GL(n,p) を結ぶ MulEquiv は未収載. **新規実装が必要** — `Aut(ZMod p)^n ≃* GL(n, ZMod p)` の形で書ける.
- **Burnside `p^a q^b` (Thm 7.8) の優先度** — FT 経路で直接被引用無いので Phase 1 完成度のため. 着手時期: Ch.7 §7A-§7C + Ch.5 5.26 完了後. **mathlib upstream 価値高 (character-free Burnside は珍しい)**.
- **`p`-stability 概念の def** — Isaacs Ch.7 本文には明示 def 無い (BG App.A で "p-stability" として導入). しかし Thm 7.5 statement の (i)-(v) 条件群が事実上 "G is p-stable" を含意するため, Phase 1 で **`IsPStable G p` を別途定義する価値**あり (BG App.A への橋渡し用). 着手時期は Ch.7 §7B 完了後.
- **Thm 7.3 (GL(2,p) 補題) の `p ≠ 2` 仮定の柔軟化** — Isaacs L3741 が "`p > 3` なら abelian Sylow-2 仮定不要" と注記. 形式化版でも `p > 3` 強化版を別途 wrapper で書くか, 一次は弱い形のみ書くか.
- **Thm 7.6 Step 7 の `V = {z ∈ Z(U) | z^p = 1}` 構成** — `Ω₁(Z(U))` だが Isaacs は `Ω₁` 記号を使わず明示的に書く. **2026-05-26 決定**: 新規 `Subgroup.omega1ZCenter` def は **追加しない**. 理由: Cor 4.35 (`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`, `Ch04_Commutators/Main.lean:3437`) は `(h_fix : ∀ g : G, g ^ p = 1 → ∀ a, (φ a) g = g)` を **pointwise 仮説** として取るため, `Ω₁(Z(U))` を subgroup として明示的に作る必要なし. 既存 `OddOrder.GroupTheory.Omega G p 1` (subgroup closure 形) は Step 6/7 で必要なら使うが, デフォルトは Z(U) 上の pointwise predicate `g^p = 1` で済ませる. Ch.6 6.11 完成済みで Ω₁ 形の def を使っていない事も確認.

## 第 6 波以降 (Phase 2a BG, Phase 2b Peterfalvi) との接続

ROADMAP は Ch.7 完了後を Phase 1 残り (Ch.8-10, Appendix) に充てるが, Ch.7 → Phase 2a の中核橋渡し:

- **Phase 2a BG §1 (Preliminaries)**: Isaacs 7.6 を `BG.Ch1.S06.zjFactorization` として再述. BG App.A は **Phase 2a 終盤** (BG §1-§16 完了後) で扱う.
- **Phase 2a BG App.A**: Isaacs 7.5, 7.6, 7.3 の **odd-order 仮定再構築**. ここで初めて "p-stability" 名前を導入 (Isaacs では暗黙).
- **Phase 2a BG §6 (Theorems 6.1, 6.2)**: Isaacs 7.6 系として証明完了. **BG §8, §9 Uniqueness Theorem の基礎**.
- **Phase 2a BG §8 (Fitting subgroup of maximal)**: BG Theorem 8.1 で Thm 6.2 (= Isaacs 7.6) を中核引用. SCN_3 概念導入.
- **Phase 2b Peterfalvi**: BG §8, §9 の Uniqueness Theorem を §8 で翻訳 (Peterfalvi (8.8), (8.13)). **Isaacs Ch.7 への依存は BG 経由**.

⇒ Phase 1 完成への道筋: **Ch.6 → Ch.7 → BG App.A → BG §6 → BG §8 → BG §10-§14 → Peterfalvi §8** がクリティカルパス. Ch.7 は **「Phase 1 内で完結する自己充足」+ 「Phase 2a 全体の埋め込み前提」** の両面で重要.
