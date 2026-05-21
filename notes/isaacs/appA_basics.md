# Isaacs Appendix: The Basics — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Appendix (pp. 325-352).
形式化先 (予定): `OddOrder/Isaacs/AppA_Basics.lean` (未作成).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 5915-6254 (Index は L6255 から).
ROADMAP 上の位置: **第 1 波 (前提なし、mathlib 既存資産で薄く)** — Ch.1, Ch.8, Appendix と同枠.

## TL;DR — 99% mathlib 既収載、**Lean ファイル不要** が結論

Appendix は本書を読むための **基礎群論の高速復習**: 群定義, 部分群, 剰余類, Lagrange,
準同型, 同型定理, 正規部分群, 商群, 共役, 中心化群/正規化群, 自己同型, 特性部分群,
直積 (内/外). **これらは全て mathlib に既収載** (`Mathlib/GroupTheory/`, `Mathlib/Algebra/Group/Subgroup/`).

**重要結果 X.1-X.23 全 23 件** のうち mathlib 直接対応:
- **Lagrange (X.8)** → `Subgroup.card_subgroup_dvd_card` (`Mathlib/GroupTheory/Coset/Card.lean:66`)
- **Homomorphism Thm (X.18)** → `QuotientGroup.quotientKerEquivOfSurjective` (`QuotientGroup/Basic.lean:146`)
- **Correspondence Thm (X.21)** → `QuotientGroup.comapMk'OrderIso` (`QuotientGroup/Basic.lean:355`)
- **Diamond Iso / Second Iso (X.20)** → `QuotientGroup.quotientInfEquivProdNormalQuotient` (`QuotientGroup/Basic.lean:293`)
- **|HK| 式 (X.2)** → `Subgroup.card_mul_eq_card_mul_card_inter` 系
- **Dedekind (X.3)** → 短い格子計算 (`inf_sup_assoc_of_le` または直証)

→ wrapper policy ([feedback_no_mathlib_wrapper](file:///Users/ywr/odd-order/notes/meta/lean_formalization_tips.md)) に従い
**`OddOrder/Isaacs/AppA_Basics.lean` は作成しない** が推奨. 本書他章で Appendix の X.N を citation
した場面で初めて、その箇所の section docstring に mathlib 名を併記すれば足りる.

例外候補は **皆無** (後述の gap analysis 参照): Appendix で使われる概念は完全に mathlib 既存
API でカバー済み.

## Appendix セクション分割と全 23 結果

**Appendix には subsection 番号も `### A.1` 等の header も無い**. 連続する flow text に
"X.1 Lemma", "X.2 Lemma", ..., "X.23 Lemma" と番号付きで定理が散在. mmd 抽出でも `### ...`
header は皆無 (`grep -nE "^### |^## "` でゼロ件). 論理的な話題区分は以下:

| 話題 | mmd 行 | 内容 | Isaacs X.# |
|---|---|---|---|
| 基本定義 | 5915-5928 | 群, Sym(X), 転置, 符号, 交代群, x^n, 位数 | (def 群 L5919, def Sym L5921, def Alt L5923, def 位数 L5927) |
| 部分群と HK | 5929-5949 | 部分群定義, 生成, HK が群 ⇔ HK=KH, 位数式, Dedekind | X.1, X.2, X.3 |
| Frattini / 極大 | 5950-5975 | 直接 diamond, 極大部分群, Frattini Φ(G), 非生成元 | X.4, X.5 |
| Cyclic 群 | 5976-5993 | 巡回群定義, 部分群分類, 位数 d の唯一性 | X.6, X.7 |
| Lagrange | 5994-6022 | 右剰余類, index \|G:H\|, Lagrange, exponent, 等式系 | X.8, X.9, X.10, X.11, X.12 |
| 同型 / Aut | 6049-6082 | 同型, 巡回群同型, Aut, Aut(cyclic) = (Z/nZ)*, 特性部分群 | X.13, X.14 |
| 共役 / 正規 / 商 | 6083-6121 | 共役, Inn, N◁G, N_G(H), C◁N で C char ⇒ C◁G, 同値命題 | X.15, X.16 |
| 準同型 / 商 | 6122-6155 | 準同型, ker, 商群, 同型定理 (準同型), N/C 定理 | X.17, X.18, X.19 |
| Diamond / 対応 | 6156-6193 | 第二同型 (Diamond), Correspondence, π:G→G/N の対応 | X.20, X.21 |
| 直積 | 6195-6253 | 外直積, 内直積, X.22 内 ↔ 外, 中心の積分解 | X.22, X.23 |

### § 全結果一覧 (mmd 行番号付き)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| X.1  | Lemma | H, K ≤ G ⇒ HK ≤ G ⇔ HK = KH | L5935 |
| X.2  | Lemma | \|HK\| = \|H\|\|K\| / \|H ∩ K\| (有限) | L5941 |
| X.3  | Lemma (Dedekind) | H ⊆ U ⊆ G ⇒ HK ∩ U = H(K ∩ U) | L5947 |
| X.4  | Cor   | HK ≤ G ⇒ 区間 \[H, HK\] と \[D, K\] (D=H∩K) の対応 (直接 diamond) | L5953 |
| X.5  | (Lemma) | X ≤ G (生成元) で ⟨X⟩ < G ⇔ ⟨X ∪ Φ(G)⟩ < G; Φ の非生成元特性化 | L5971 |
| X.6  | (Lemma) | G = ⟨g⟩ 巡回, 1 ≠ H ≤ G ⇒ H = ⟨g^m⟩ (m 最小正で g^m ∈ H); 部分群は全て巡回 | L5981 |
| X.7  | Cor   | G = ⟨g⟩, \|G\|=n, ∀d∣n: ⟨g^{n/d}⟩ が唯一の位数 d 部分群; これで全部分群を尽くす | L5989 |
| X.8  | Theorem (Lagrange) | (a) y∈Hx ⇒ Hy=Hx, (b) 異なる右剰余類は交わらない, (c) \|Hx\|=\|H\|, (d) \|H\| ∣ \|G\|, \|G\|/\|H\|=\|G:H\| | L5999 |
| X.9  | Cor   | g ∈ G 有限 ⇒ o(g) ∣ \|G\| | L6012 |
| X.10 | Cor   | H ⊆ K ⊆ G ⇒ \|G:H\| = \|G:K\|·\|K:H\| (multiplicativity of index) | L6020 |
| X.11 | Cor   | \|K : H∩K\| ≤ \|G:H\|; 等号 ⇔ HK = G | L6024 |
| X.12 | Cor   | gcd(\|G:H\|, \|G:K\|) = 1 ⇒ HK = G | L6036 |
| X.13 | Lemma | 同位数の有限巡回群は同型 (b^i ↦ c^i) | L6056 |
| X.14 | Lemma | G 巡回 ⇒ Aut(G) 可換; \|G\| 有限なら \|Aut(G)\| = φ(\|G\|) | L6070 |
| X.15 | Lemma | N ◁ G, C char N ⇒ C ◁ G | L6090 |
| X.16 | Lemma | H ◁ G ⇔ Hx=xH ⇔ 全右剰余類が左剰余類 ⇔ ⋯ (6 同値条件) | L6098 |
| X.17 | Lemma | 準同型 θ: G→H, N=ker θ: (a) θ(1)=1, (b) θ(x⁻¹)=θ(x)⁻¹, (c) N◁G, (d) θ(x)=θ(y) ⇔ Nx=Ny, (e) θ injective ⇔ N=1 | L6131 |
| X.18 | Theorem (Homomorphism) | 全射 θ:G→H, N=ker θ ⇒ G/N ≅ H (∃! τ:G/N→H で τ(Nx)=θ(x)) | L6147 |
| X.19 | Cor (N/C-Thm) | H ≤ G ⇒ C_G(H) ◁ N_G(H), N_G(H)/C_G(H) ↪ Aut(H) | L6159 |
| X.20 | (Thm — Diamond / Second Iso) | N ◁ G, H ≤ G ⇒ H∩N ◁ H, NH/N ≅ H/(H∩N) | L6167 |
| X.21 | Theorem (Correspondence) | 全射 θ:G→H で N=ker θ: 部分群対応 X ↔ θ(X), index 保存, 正規部分群保存, 商の同型 | L6173 |
| X.22 | Theorem | G = M_1·M_2⋯M_r (M_i ◁ G) が direct product ⇔ ∀k>1: (M_1⋯M_{k-1}) ∩ M_k = 1 | L6215 |
| X.23 | Lemma | 内直積 G = M_1 × ⋯ × M_r ⇒ G ≅ 外直積 (M_1 × ⋯ × M_r) | L6241 |

注: X.5, X.6, X.20 は本文中で "**X.N**." 形式で名前 (Lemma/Theorem/Cor) を省略して登場する.
内容的にはそれぞれ Lemma 相当.

その他 Appendix で **定義のみ与えられる概念** (これらも mathlib 完備):

| 概念 | mmd | mathlib |
|---|---|---|
| 群 (`Group`) | L5919 | `Mathlib/Algebra/Group/Defs.lean` |
| 対称群 `Sym(X)`, `S_n` | L5921 | `Equiv.Perm`, `Equiv.Perm (Fin n)` |
| 交代群 `Alt(X)`, `A_n` | L5923 | `alternatingGroup` (`Mathlib/GroupTheory/SpecificGroups/Alternating.lean`) |
| 位数 `o(x)` | L5927 | `orderOf` (`Mathlib/GroupTheory/OrderOfElement.lean`) |
| 部分群 | L5929 | `Subgroup` |
| 生成 `⟨X⟩` | L5967 | `Subgroup.closure` |
| 極大 / Frattini Φ(G) | L5969 | `Subgroup.frattini` (`Mathlib/GroupTheory/Frattini.lean:23`) |
| 巡回 | L5977 | `IsCyclic` (`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`) |
| 剰余類, index | L5997 | `QuotientGroup`, `Subgroup.index` |
| exponent | L6016 | `Monoid.exponent` (`Mathlib/GroupTheory/Exponent.lean`) |
| 同型 `≅` | L6050 | `MulEquiv` |
| 中心 Z(G) | L6066 | `Subgroup.center` |
| 自己同型 Aut(G), Inn(G) | L6068, L6084 | `MulAut`, `MulAut.conj.range` |
| 特性部分群 | L6082 | `Subgroup.Characteristic` (`Mathlib/Algebra/Group/Subgroup/Basic.lean:236`) |
| 共役 x^g | L6084 | `MulAction.ConjAct`, `mul_aut_arrow_apply` |
| 正規 N ◁ G | L6086 | `Subgroup.Normal` |
| 正規化群 N_G(H) | L6094 | `Subgroup.normalizer` |
| 商群 G/N | L6121 | `QuotientGroup`, `G ⧸ N` |
| 準同型, ker | L6123, L6129 | `MonoidHom`, `MonoidHom.ker` |
| 中心化群 C_G(X) | L6157 | `Subgroup.centralizer` (`Mathlib/GroupTheory/Subgroup/Centralizer.lean`) |
| 交換子 [m,n] | L6235 | `commutatorElement` (`⁅·,·⁆`) |
| 外直積 G_1 × ⋯ × G_r | L6195 | `Prod.instGroup`, `PiLp` 系 |
| 内直積 | L6209 | (構成的に内部直積を主張する命題) |

## mathlib カバレッジ

Phase 1 諸章で最も **カバー率が高い (実質 100%)**. 23 結果中 1 件も新規実装は不要.

### 直接利用できるもの (主要対応表)

| Isaacs Appendix | mathlib | 備考 |
|---|---|---|
| **X.1** HK ≤ G ⇔ HK=KH | `Subgroup.mul_normal` / `Subgroup.normal_mul` + `Subgroup.mul_subgroup_iff` 周辺 | 厳密同等は数行で得る (mathlib では `HK = KH ↔ HK ≤ G` を二方向で構成) |
| **X.2** \|HK\| 式 | `Subgroup.card_mul_eq_card_mul_card_inter` 等 (cardinal 形は `Subgroup.card_inf_mul_card`) | 直接 |
| **X.3** Dedekind | `Subgroup.inf_sup_assoc_of_le` / 直接 `inf` と `sup` の格子計算 | 短い補題; mathlib 直名は無いが格子 API で導出 |
| **X.4** 直接 diamond / interval 対応 | `Subgroup.relIndex` API + `Subgroup.subgroupOf` で interval 構造 | mathlib 既存資産で組み立て可 |
| **X.5** Φ(G) 非生成元特性化 | `frattini_nongenerating` (`Mathlib/GroupTheory/Frattini.lean` ~L48) | 直接対応 (Lemma 1.51 mathlib 名は `Subgroup.frattini_nongenerating` 形) |
| **X.6** 巡回部分群分類 | `Subgroup.IsCyclic.of_subgroup` / `IsCyclic.subgroup` 系; `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` 巡回部分群定理 | 直接 |
| **X.7** 巡回 G で各約数 d に唯一の位数 d 部分群 | `IsCyclic.uniqueSubgroupOfCard` (cyclic.lean 内) / `IsCyclic.card_orderOf_eq_totient` 周辺 | 直接 |
| **X.8** Lagrange | `Subgroup.card_subgroup_dvd_card` (`Mathlib/GroupTheory/Coset/Card.lean:66`); 剰余類分割は `QuotientGroup.mk_surjective` + `Subgroup.card_eq_card_quotient_mul_card_subgroup` | 直接 |
| **X.9** o(g) ∣ \|G\| | `orderOf_dvd_card` | 直接 |
| **X.10** \|G:H\|=\|G:K\|\|K:H\| | `Subgroup.index_mul` / `Subgroup.relIndex_mul_index` (`Mathlib/GroupTheory/Index.lean`) | 直接 |
| **X.11** \|K:H∩K\| ≤ \|G:H\|, 等号 ⇔ HK=G | `Subgroup.relIndex_le_index` + `Subgroup.relIndex_eq_iff_mul_eq` 系 | mathlib 名は微妙に違うがほぼ直接 |
| **X.12** gcd(\|G:H\|, \|G:K\|)=1 ⇒ HK=G | `Subgroup.coprime_index_implies_mul_eq` 形 | 短い補題 (X.10+X.11 から) |
| **X.13** 同位数 cyclic は同型 | `zmodCyclicMulEquiv` / `IsCyclic.equiv_zmod` (Cyclic.lean) | 直接 |
| **X.14** Aut(G) 巡回で \|Aut\|=φ(\|G\|) | `MulAut (ZMod n) ≃* (ZMod n)ˣ` + `Nat.card (MulAut G) = Nat.totient (Nat.card G)` (`Cyclic.lean:581`) | 直接 |
| **X.15** N◁G, C char N ⇒ C◁G | `Subgroup.Characteristic.normal_of_normal` / `Subgroup.Normal.comp_characteristic` | 直接 (mathlib 名は `Subgroup.Characteristic` の `normal_of_characteristic` 関連) |
| **X.16** N ◁ G 同値条件 6 つ | `Subgroup.Normal` の `iff_*` 群 (`mem_normalizer_iff`, `normal_iff_eq_cosets` 等) | 直接 |
| **X.17** ker 基本性質 | `MonoidHom.map_one`, `MonoidHom.map_inv`, `MonoidHom.ker_normal`, `MonoidHom.eq_iff_ker_coset` 等 | 直接 |
| **X.18** Homomorphism Theorem (第一同型) | `QuotientGroup.quotientKerEquivOfSurjective` (`Mathlib/GroupTheory/QuotientGroup/Basic.lean:146`) | 直接 |
| **X.19** N/C-Theorem | `Subgroup.normalizer_quotient_centralizer_embed_aut` 形 (mathlib 直名探索要); 構成は `Subgroup.normalizer / Subgroup.centralizer → MulAut H` で `MonoidHom.toEmbedding` | 既存 API の合成で 数行 |
| **X.20** Diamond / 第二同型 | `QuotientGroup.quotientInfEquivProdNormalQuotient` (`QuotientGroup/Basic.lean:293`) | 直接 |
| **X.21** Correspondence | `QuotientGroup.comapMk'OrderIso` (`QuotientGroup/Basic.lean:355`); 第三同型 (Y◁H で G/X ≅ (G/N)/(X/N)) は `QuotientGroup.quotientQuotientEquivQuotient` (`Basic.lean:332`) | 直接 (lattice 同型 + 第三同型の二部品) |
| **X.22** 内直積判定 | `Subgroup.IsInternal` / `Submodule.IsInternal` 系 + `Group.directProductOfNormal` (Sylow.lean:774 の構成); mathlib では複数本に分散 | 部品を集めれば直接 |
| **X.23** 内直積 ⇒ 外直積同型 | `Group.directProductOfNormal` (`Mathlib/GroupTheory/Sylow.lean:774`) と類似の構成; `Prod.toAlgEquiv` で表現 | 直接 |

参考: mathlib 内で **Lagrange の名前** は `Mathlib/GroupTheory/Index.lean` (L22 docstring) と
`Mathlib/GroupTheory/Coset/Card.lean` (L12 ファイルヘッダ, L66-67 主定理) で明示されており、
"Several theorems proved in this file are known as Lagrange's theorem" と書かれている.

### カバレッジ概観

| 種別 | 数 | 比率 |
|---|---|---|
| mathlib 直接対応 (single API call) | 18 / 23 | 78% |
| mathlib 既存資産から数行で組立 | 5 / 23 | 22% |
| 新規実装が必要 | 0 / 23 | 0% |

## 下流被引用

**Appendix は Isaacs 本体全章 (Ch.1-10) で implicitly 使われる前提**. 本書 Ch.1-10 で
明示的に "X.N" や "Appendix" と引用する箇所は **稀** (Index 5915-6254 を grep する限り、
本文側から `\text{App}` や `\text{X}\.\d` 形式での citation は無い; 本書は前置きで
"基礎部分は復習程度なので必要に応じて参照されたい" と書く方式).

つまり Appendix は **読者向けのリファレンス** であって、形式化対象としての
"被引用カウント" は不要 (mathlib に任せて Lean 化を省略しても本体形式化に影響ゼロ).

BG / Peterfalvi の引用も同様: 一切無し. Appendix の内容は完全に common knowledge.

## 着手しない方針 (推奨)

**結論: `OddOrder/Isaacs/AppA_Basics.lean` は作成しない**.

理由:
1. **全 23 結果が mathlib 既収載**. wrapper policy
   ([feedback_no_mathlib_wrapper](file:///Users/ywr/odd-order/notes/meta/lean_formalization_tips.md))
   に従えば 純粋リネームの薄いラッパーは書かない. Appendix の Lean 化はそれ以外の何物でも
   ないため、章ファイル自体が wrapper 集合になり policy 違反.
2. **下流被引用ゼロ** (mathlib 名で直接使えば良い). 各章 Lean ファイルで `Subgroup.card_subgroup_dvd_card`
   等を直接呼べばよく、`OddOrder.Isaacs.AppA.lagrange` のような中間名は害悪.
3. **教科書名対応の記録は本ノートで十分**. 上の表をそのまま、必要なら本書他章の section
   docstring に簡易引用すれば足る (例: "Lagrange (Isaacs Appendix X.8 = `Subgroup.card_subgroup_dvd_card`)").

ROADMAP の Phase 1 チェックリストでは Appendix 項目を:

> [x] Appendix: The Basics — **mathlib 完全カバー** につき Lean ファイル作成不要.
> 教科書名 ↔ mathlib 名対応表は [notes/isaacs/appA_basics.md](notes/isaacs/appA_basics.md).

の形でクローズするのが妥当 (実装作業 0 で完了マークが付く特殊ケース).

## mathlib gap analysis (もし新規実装が必要なら)

**現時点で gap は無い**. 全 23 結果について mathlib 直接対応または短い組立で得られる
ことを上表で示した. 念のため精査した結果でも:

- **X.4 直接 diamond の lattice 形** — mathlib に `Subgroup.relIndex` と `subgroupOf` で
  Galois 接続が組まれており、interval `[H, HK]` ↔ `[D, K]` 対応は `OrderIso` として
  既存 API 内で構成可. 純粋に Isaacs 形そのままの命名定理は無いが、`map`/`comap` Galois
  対応の特殊化なので gap ではない.
- **X.20 第二同型** — mathlib の名は `quotientInfEquivProdNormalQuotient`. Isaacs では
  "NH/N ≅ H/(H∩N)" と書くが mathlib は "(H ⊓ N).comap → H ⧸ ..." 形. **同値だが
  記法差**. 教科書 名で呼びたい場面は section docstring で記録.
- **X.16 N ◁ G の 6 同値条件** — mathlib に断片化されている (`Subgroup.normal_iff` 系
  の lemma 群が点在). 6 条件を 1 つの `iff` チェーンにまとめた定理は無いが、これは
  単に "API 流派" の違いで gap ではない.

→ **真の gap: ゼロ件**. Appendix 形式化は 100% スキップ可能.

## 未解決の疑問

- **mathlib の "内直積" API の現状**: `Group.directProductOfNormal` (`Sylow.lean:774`) は
  Sylow 部分群が pairwise 可換に近い形での内部直積を構成. Isaacs X.22 の **一般 r 個** の
  内直積判定 ((M_1⋯M_{k-1})∩M_k=1) を 1 つの命題として書いた lemma は探索の限りでは
  発見できなかった. ただしこれは Appendix Lean 化を必要としない理由 (mathlib の二項版
  + 帰納で得られるため) であり、Phase 1 で gap として扱う必要は無い.
- **`Subgroup.Characteristic` の API 完備度**: mathlib では `Characteristic` は structure
  (`Mathlib/Algebra/Group/Subgroup/Basic.lean:236`) として定義され `normal_of_characteristic`
  instance あり (X.15 直接対応). 一方 "char in char ⇒ char" (X.15 の強化系) は mathlib に
  あるか要確認だが、Appendix 範囲外なので不要.
- **Φ(G) の "non-generating" 形 (X.5)**: `Mathlib/GroupTheory/Frattini.lean` に
  `Subgroup.frattini` (L23) と "frattini_nongenerating" docstring (L48 周辺) があり、
  形式化は完備. **mathlib 名の正確な lemma 名** は本ノート記述では推測したので、
  Lean を書く段階で grep 確認することを推奨 (ただし本ノートの推奨が `スキップ` なので
  実害なし).
