# Isaacs Ch.3: Split Extensions — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.3 (pp. 65-112) — Hall, Schur-Zassenhaus, coprime action。
形式化先: [`OddOrder/Isaacs/Ch03_SplitExtensions.lean`](../../OddOrder/Isaacs/Ch03_SplitExtensions.lean).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 1322-2123。

## 進捗 (2026-05-22 更新)

§3A ウォームアップ実装済 (Thm 3.1, 3.2 を mathlib `SemidirectProduct` 経由で wrap):

| # | 状態 | 実装 |
|---|---|---|
| Thm 3.2 part 1 (inl(N) normal) | ✅ | `inl_range_normal` instance (`range_inl_eq_ker_rightHom` + `MonoidHom.normal_ker`) |
| Thm 3.2 part 2 (inl(N), inr(H) complementary) | ✅ | `inl_range_isComplement_inr_range` (構造 projection 経由) |
| Thm 3.2 part 3 (conjugation = action) | ✅ | `inr_conj_inl_eq` (mathlib `inl_aut` ラッパー) |
| Thm 3.1 (uniqueness via mulEquivSubgroup) | ✅ | `mulEquivSubgroupOfComplement` (mathlib `mulEquivSubgroup` 再述) |
| **Thm 3.3 Horosevskii** | ✅ (2026-05-22) | `horosevskii_aut_order_lt`: `orderOf σ < Nat.card G`. Ch.2 Lucchini axiom + 半直積 (mathlib `SemidirectProduct`) + `inl_range_isComplement_inr_range` (Thm 3.2 part 2) + Lemma 2.7 (`commute_of_normal_of_disjoint`) で完全証明 (~120 行) |
| Thm 3.4 (abelian P regular orbit) | ✅ (2026-05-21 完成, 2026-05-23 audit で確認) | `abelian_p_aut_regular_orbit` L255-424. Ch.1 §1F Thm 1.37 Brodkey + `opCore` + Lemma 2.7 + Sylow II 経由 |
| §3B Schur-Zassenhaus (3.5-3.10) | docstring | mathlib 対応表のみ (`exists_right_complement'_of_coprime`, `IsSolvable` instance chains) |
| §3B Thm 3.11 前半 (abelian) | ✅ | `solvable_minimal_normal_isAbelian` (`⁅M,M⁆ < M` + 最小性) |
| §3B Thm 3.11 後半 (elementary abelian) | ✅ (2026-05-23 shared 化) | `solvable_minimal_normal_isElementaryAbelian` (p-torsion T が characteristic in M + 最小性). `IsElementaryAbelian` def は `OddOrder/GroupTheory/ElementaryAbelian.lean` に extract (whole-group + subgroup form), Ch.6/Ch.7/BG App.A 共有予定 |
| §3C Lemma 3.16 coprime index ⇒ HK=G | ✅ | `sup_eq_top_of_coprime_index` (Subgroup.index_dvd + Nat.dvd_gcd) |
| §3C IsHallSubgroup 定義 + 基礎 | ✅ | `IsHallSubgroup`, `.coprime_index`, `.top_iff`, `.bot_iff`, `.bot_of_card_eq_one` |
| §3C **Thm 3.13 Hall-E** | ✅ | **完全証明**. `hall_E_strong_aux` で `|G|`-強誘導. base (|G|=1): ⊥. step: minimal normal M (Thm 3.11 で elem abelian p-group) + IH on G/M + pullback. Case p ∈ π: H = comap で直接. Case p ∉ π: Schur-Zassenhaus on M.subgroupOf H |
| §3C Thm 3.14 Hall-C | **leaf axiom 削除** (2026-05-22) | mathlib SZ 共役性依存. 将来 `OddOrder/Mathlib/SchurZassenhausConj.lean` で実装後にここで theorem 化. Ch.3 内 redirect コメントのみ. |
| §3C Thm 3.15 (Hall converse) | **placeholder 移動** (2026-05-22) | `OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean` に owner-chapter 配置. Burnside `p^a q^b` 経由のため Ch.7 完成後に実装. |
| §3C Thm 3.17 (3 subgroups solvability) | **placeholder 移動** (2026-05-22) | 同上 (`Ch07_ThompsonSubgroup/ForwardFromCh03.lean`). 単純群場合分けで Burnside 必要. |
| §3D Thm 3.20 (π-separable ⇒ Hall) | ✅ | 仮定義 `IsPiSeparable := IsSolvable` 下で `hall_E_exists` に帰着 |
| §3D **IsPiGroup / oPiCore 定義** | ✅ (2026-05-22) | `IsPiGroup`, `Subgroup.IsPiGroup`, `oPiCore π G`, `oPiCore.normal` instance |
| §3D Hall-Higman 1.2.3 (3.21) | ✅⭐⭐ (2026-05-23 ralph-loop) | `hall_higman_1_2_3` — G π-separable + `oPiCore π' G = ⊥` ⇒ `centralizer(oPiCore π G) ≤ oPiCore π G`. case π body + case π' body + main assembly (~350 LOC 累計: helpers 200 + cases 130 + main 25). AxiomsCheck flagship 入り (3 標準公理のみで unconditional). 下流引用: Ch.4 4.33, Ch.7 7.5/7.6. |
| §3E `IsAInvariant` 定義 | ✅ (2026-05-22) | `IsAInvariant`, `.top`, `.bot`, `.inf`, `.sup` (Ch.3 内に残置, definition のみ) |
| §3E IsAInvariant suite 拡張 | ✅ (2026-05-23 ralph-loop, ~24 lemmas) | `.{smul_mem, inv_smul_mem, iSup, iInf, of_characteristic, derivedSeries, lowerCentralSeries, center, fittingSubgroup, frattini, commutator (binary), commutator_self, normalizer, centralizer, normalCore, fixedPointsOfMulAut, restrict + restrict_apply_val, subgroupOf, closure_of_invariant_set}` 全部 sorry-free. 下流 Glauberman 3.24 + Ch.4 §4C [G,A] 機構の前哨基地. |
| §3E Thm 3.23 (a/b) + Lemma 3.24 | **placeholder 移動** (2026-05-22) | `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean` に owner-chapter 配置. Ch.4 §4C-§4D coprime action machinery 完成後に実装 (~8-12 週). |
| §3F 巡回商 lift (3.35 弱版) | ✅ (2026-05-22) | `cyclic_quotient_lift`: G/H cyclic ⇒ ∃ g, ⟨g⟩ ⊔ H = ⊤. 弱版を Quotient.mk_surjective + zpowers で証明. 旧 axiom statement は inconsistent (H ≤ K + K ⊔ H = ⊤ ⇒ K = ⊤ で card 等式が \|G/H\| = \|H\| に帰着し反例あり) のため置換 |

## mmd 抽出失敗の整理

Ch.3 は mmd で **3 つの MISSING_PAGE markers** あり (PDF 直接補完が必要):

| 行 | marker | PDF p. | 書籍 p. | 失われたもの |
|---|---|---|---|---|
| 1306 | MISSING_PAGE_EMPTY:78 | 78 | 65 | Ch.3 表紙 + § 3A 開始 |
| 1392 | MISSING_PAGE_FAIL:85 | 85 | 72 | §3A 末尾 (3.4 証明の続き + 3A 最終ディスカッション) |
| 1726 | MISSING_PAGE_FAIL:102 | 102 | 89 | §3C 内部 (3.17 周辺) |

また `## Chapter 3 Split Extensions` のヘッダ自体が mmd で完全欠落 (`## Chapter 2` の次が `## Chapter 4`).

## 章のセクション分割と全 36 結果

Ch.3 は § 3A–3F の 6 節構成 (Ch.2 と同様 subsection には番号のみ・タイトル無し).
PDF で境界確認済:

| § | 書籍 pp. | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 3A | 65-74 | 半直積 + Aut(G) の位数評価 | 3.1 – 3.4 | 半直積構成 (3.2), Horosevskii (3.3), Schur 系 (3.4) |
| 3B | 75-82 | Schur-Zassenhaus + 可解群基本 | 3.5 – 3.12 | Schur-Zassenhaus (3.5, 3.8), 可解性特性化 (3.9-3.11), 共役性 (3.12) |
| 3C | 83-88 | Hall 部分群 + 可解性判定 | 3.13 – 3.17 | **Hall E (3.13), Hall C (3.14)**, p-complement ⇒ 可解 (3.15) |
| 3D | 89-95 | π-separable 群 + Hall-Higman | 3.18 – 3.22 | **Hall-Higman 1.2.3 (3.21)**, π-length |
| 3E | 96-104 | Coprime action | 3.23 – 3.34 | Glauberman lemma (3.24), Hartley-Turull (3.31), 軌道サイズ (3.34) |
| 3F | 105-112 | 巡回商の lift | 3.35 – 3.36 | cyclic quotient extension lifts |

### 全結果一覧 (mmd 行番号付き)

#### § 3A — Semidirect products + Aut bounds (1322-1391, 失われた p.72)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 3.1 | Lemma | 半直積の uniqueness | L1322 |
| 3.2 | Theorem | **半直積の存在 (external semidirect product)** | L1350 |
| 3.3 | Corollary | **Horosevskii**: σ ∈ Aut(G) で o(σ) < \|G\| | L1372 |
| 3.4 | Corollary | abelian P ⊆ Aut(G), p ∤ \|G\| ⇒ P は G に regular orbit | L1380 |

#### § 3B — Schur-Zassenhaus + solvability basics (1458-1620)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 3.5  | Theorem | **Schur-Zassenhaus (abelian 場合)** | L1458 |
| 3.6  | Lemma   | crossed homomorphism の基本性質 | L1468 |
| 3.7  | Lemma   | abelian normal の transversal 差 `d(S, T)` | L1509 |
| 3.8  | Theorem | **Schur-Zassenhaus (一般 existence)** | L1545 |
| 3.9  | Lemma   | G solvable ⇔ G^{(m)} = 1 | L1569 |
| 3.10 | Lemma   | solvable の基本性質 (商・部分群・拡大) | L1585 |
| 3.11 | Lemma   | solvable minimal normal は elementary abelian p-group | L1599 |
| 3.12 | Theorem | **complement の共役性** (N or G/N solvable) | L1607 |

#### § 3C — Hall theory (1690-1725, 失われた p.89)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 3.13 | Theorem | **Hall-E**: G solvable ⇒ Hall π-subgroup 存在 | L1690 |
| 3.14 | Theorem | **Hall-C**: G solvable ⇒ Hall π-subgroup 共役 | L1700 |
| 3.15 | Theorem | 全 p について p-complement 存在 ⇒ G solvable | L1710 |
| 3.16 | Lemma   | \|G:H\|, \|G:K\| coprime ⇒ G = HK | L1716 |
| 3.17 | Theorem | 3 つの部分群が pairwise coprime index + solvable ⇒ G solvable | L1724 |

#### § 3D — π-separable + Hall-Higman (1771-1835)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 3.18 | Lemma     | π-separable の補助 | L1771 |
| 3.19 | Corollary | G solvable ⇒ 全 π について π-separable | L1787 |
| 3.20 | (Thm)     | π-separable ⇒ Hall π-subgroup 存在 | L1799 |
| 3.21 | Theorem   | **Hall-Higman 1.2.3**: π-separable + O_{π'}(G)=1 ⇒ O_π(G) ⊇ C_G(O_π(G)) | L1807 |
| 3.22 | Theorem   | π-separable + abelian Hall π ⇒ π-length ≤ 1 | L1819 |

#### § 3E — Coprime action (1844-2021)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 3.23 | Theorem   | coprime action: A-invariant Sylow p の存在・共役・等 | L1844 |
| 3.24 | Lemma     | **Glauberman 補題**: コンパチブル作用 + transitive ⇒ A-不変点存在 | L1857 |
| 3.25 | Corollary | A-invariant p-subgroup は A-invariant Sylow に含まれる | L1910 |
| 3.26 | Theorem   | A-invariant 共役類 ↔ C = C_G(A) の共役類 (bijection) | L1916 |
| 3.27 | (Thm)     | A-invariant coset と C との交わり | L1924 |
| 3.28 | (Thm)     | quotient G/N での coprime 作用の整合性 | L1936 |
| 3.29 | Corollary | A acts trivially on G/Φ(G) ⇒ A acts trivially on G | L1942 |
| 3.30 | Corollary | A faithful on G ⇒ A faithful on G/Φ(G) | L1950 |
| 3.31 | Theorem   | **Hartley-Turull**: 軌道構造が abelian H に転送可 | L1956 |
| 3.32 | (Lemma)   | P A-invariant Sylow ⇒ P ∩ C ∈ Syl_p(C) | L1960 |
| 3.33 | (Thm)     | fixed point 数一致 ⇒ orbit-preserving bijection | L1970 |
| 3.34 | Theorem   | A-orbit sizes m, n coprime ⇒ size mn の orbit も存在 | L2002 |

#### § 3F — Cyclic quotient lifts (2050-2123)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 3.35 | Theorem | 巡回商の同型 lift (一般化された 3.1) | L2050 |
| 3.36 | Theorem | a, σ で生成される巡回商型拡大の存在 | L2068 |

## mathlib カバレッジ

Ch.2 と比べて **mathlib カバレッジは厚い** が、FT クリティカルな部分はまだ多くが未収載.

### 直接利用できるもの

| Isaacs | mathlib | 備考 |
|---|---|---|
| Thm 3.2 半直積 | `SemidirectProduct` (`Mathlib/GroupTheory/SemidirectProduct.lean`) | external semidirect product 構成 |
| Def 補集合 | `Subgroup.IsComplement`, `IsComplement'` (`Mathlib/GroupTheory/Complement.lean`) | |
| Thm 3.5 SZ abelian + Thm 3.8 SZ general | **`Subgroup.exists_right_complement'_of_coprime` 1 つで両方カバー** (`SchurZassenhaus.lean:274`, abelian 仮定不要) — 2026-05-23 audit 確認 | 3.5 / 3.8 別実装は不要 |
| Def IsSolvable | `IsSolvable` class (`Mathlib/GroupTheory/Solvable.lean:106`) | 既存. Thm 3.9, 3.10 ラッパー可 |
| Thm 3.9 G^{(m)}=1 | **`isSolvable_def`** (auto-gen `@[mk_iff]`, `Solvable.lean:105`) が exact match. 2026-05-23 audit 確認: `derivedSeries_eq_bot_iff` や `isSolvable_iff_derivedSeries_eq_bot` は mathlib v4.29.1 に **存在しない** | `(isSolvable_def G).symm` 1 行 |
| Thm 3.10 solvable 基本 | mathlib に整っているはず (subgroup/quotient/extension) | |

### 新規実装が必要な主要項目

* **Def Hall π-subgroup** (`Subgroup.IsHallSubgroup` 相当). 新規必須. π ⊆ primes,
  `|H|` が π-数, `|G:H|` が π'-数, の組合せ.
* **Def π-separable group** (`Group.IsPiSeparable` 相当). 新規必須. composition factor
  が全て π-group か π'-group.
* **Thm 3.3 Horosevskii** — **Ch.2 Thm 2.20 Lucchini を使う** (PDF で証明確認済).
  ⇒ **§2D の Lucchini だけは Ch.3 のために実装必要** (§2D 全体は不要だが 2.20 単独で要).
* **Thm 3.13 Hall-E** + **Thm 3.14 Hall-C** — 可解群の Hall 部分群存在・共役.
  FT 本筋で BG が多用.
* **Thm 3.15-3.17** — p-complement / 可解性判定.
* **Thm 3.21 Hall-Higman 1.2.3** — **BG が明示引用** (BG L492, L1971). FT クリティカル.
* **Thm 3.22 π-length** — 3.21 と一緒の議論.
* **§3E coprime action 全体 (3.23-3.34)** — Glauberman lemma + Hartley-Turull.
  BG/Peterfalvi では名前無しで A-invariant Hall として使う. mathlib 完全未収載.
* **Thm 3.31 Hartley-Turull** — orbit 構造の abelian 化. やや特殊.
* **§3F 巡回商 lift (3.35, 3.36)** — 補助結果. 下流必要性が見えるまで保留可.

## 下流被引用 (Isaacs Ch.4+)

```
3.28 (3 回), 3.21 (3 回), 3.23 (2 回), 3.10/3.11/3.16/3.21 各 1 回
```

3.28 (coprime action quotient) と 3.21 (Hall-Higman) が突出. Ch.3 全体としては
被引用が多く、Ch.2 と異なり **本書内で頻繁に使われる** ことが確認できる.

## BG/Peterfalvi 引用調査

### BG での名前引用

| 名前 | 件数 | 文脈 |
|---|---|---|
| **Hall-Higman 1.2.3** | 複数 | L492 `(P. Hall & G. Higman, "Lemma 1.2.3")` で `C_G(T) ⊆ O_{p',p}(G)` を主張. L1971 で Thm 6.1 として再述. 索引にも記載. **Isaacs 3.21 と等価/同値**. |
| Hall (general) | 多数 | A-invariant Hall theory として BG §1 で展開. L402-412 で "A-invariant Hall π-subgroup" の存在・共役を BG が独自に証明 (Isaacs 3.13-3.14 の coprime 拡張). |
| Glauberman | 文献のみ | L5459 "A characteristic subgroup of a p-stable group" (1968) — BG App.A の ZJ 関連. **Isaacs §3E の Glauberman lemma (3.24) とは別物**. |
| Hartley-Turull | 0 | 序文に Turull = 共同作業者の言及のみ. Isaacs Thm 3.31 とは無関係. |

⇒ **BG にとって Ch.3 の必須項目**: **Hall E + C (3.13, 3.14)**, **Hall-Higman 1.2.3 (3.21)**.
A-invariant Hall (Isaacs 3.23 の流れ) も精神的には必要だが、BG は §1 で自前構築済.

### Peterfalvi での名前引用

| 名前 | 文脈 |
|---|---|
| Glauberman | 04.17 Notes で「FT Lemma 34.5/34.6/34.7 の Glauberman による改善」を引用. **Isaacs §3E とは別物**. |
| Hall | Hall σ-subgroup, Hall π-subgroup の利用. 詳細は Phase 2b で要確認. |

## 着手順 (提案)

依存 (Ch.2 + 自章内) と新規実装コストで並べる:

1. **§3A 前半 (Thm 3.1, 3.2)** — mathlib `SemidirectProduct` ラッパー + uniqueness. ウォームアップ.
2. **Ch.2 Thm 2.20 Lucchini を先に実装** (3.3 の前提). §2D 全体は要らないが 2.20 のみ必要.
3. **§3A 残り (Thm 3.3 Horosevskii, 3.4)** — Lucchini を使う Schur-Aut 評価.
4. **§3B (Thm 3.5-3.12)** — mathlib `SchurZassenhaus` + `IsSolvable` の薄いラッパー.
   mathlib に Thm 3.5, 3.8 が直接ある.
5. **§3C (Thm 3.13 Hall-E, 3.14 Hall-C, 3.15-3.17)** — **Hall 部分群の新規定義 + 主定理**.
   **FT クリティカル**.
6. **§3D (Thm 3.18-3.22)** — π-separable 新規定義 + **Hall-Higman 1.2.3 (3.21)**.
   **FT クリティカル**.
7. **§3E (Thm 3.23-3.34)** — coprime action 系. 新規実装重い. BG/Peterfalvi 直接引用
   無いので後回し可 (ただし 3.28 は Isaacs 内被引用 3 回).
8. **§3F (Thm 3.35, 3.36)** — 巡回商 lift. 下流必要性確認後で.

優先度 (FT クリティカル度): **3.13, 3.14, 3.21** > 3.5, 3.8, 3.2 > 3.23-3.34 > その他.

## 未解決の疑問

* **mathlib の `derivedSeries` 周りで Thm 3.9, 3.10 がどこまでラッパー化できるか** —
  `mathlib/GroupTheory/Solvable.lean` の API を要 grep.
* **Hall 部分群定義の最善形** — π を `Set ℕ` で取るか `Finset ℕ` で取るか. mathlib に
  Sylow との対応で参考になる慣習があるはず.
* **3.21 Hall-Higman 1.2.3 の Isaacs 流証明** — π-separable + O_{π'}(G) = 1 仮定からの
  induction. 実装着手前に PDF p.103 周辺の証明を読み込む必要あり.
* **3.23-3.34 (coprime action) の優先度** — Isaacs Ch.4+ で 3.28 が 3 回引用される
  以外、BG/Peterfalvi 直接引用無し. ⇒ Ch.4-7 を実装する時に順次必要になる予感だが、
  §3E をひとまとめに実装するか、必要分だけ pull するか要判断.
* **3.31 Hartley-Turull** — Isaacs 独自結果. **BG / Peterfalvi で by-name 引用 0 件**
  (2026-05-23 audit grep 確認). Ch.4-10 でも by-name cite 無し. ⇒ **Phase 4 までも skip 可**,
  Phase 1 完成度のためのみ.
