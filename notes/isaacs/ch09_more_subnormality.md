# Isaacs Ch.9: More on Subnormality — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.9 (pp. 271-294).
形式化先 (予定): `OddOrder/Isaacs/Ch09_MoreSubnormality.lean` (未作成).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 4880-5310.
ROADMAP 上の位置: **第 3 波 (Ch.2 完了後、並列可)** — 直接前提は Ch.2 (Thm 2.6 minimal normal が subnormal を正規化, socle 概念), 軽く Ch.1 (Fitting, 冪零).

## TL;DR — FT 経路ではほぼ全章スキップ可

BG / Peterfalvi mmd を厳密検索した結果, Ch.9 の主結果群はすべて **使用 0 件**:

| Ch.9 概念 | BG 出現 | Peterfalvi 出現 |
|---|---|---|
| `\mathbf{F}^{*}` (generalized Fitting) | 0 | 0 |
| quasisimple | 0 | 0 |
| `\mathbf{E}(G)` (layer) / "the layer" / "components of [G]" | 0 | 0 |
| automorphism tower / Wielandt aut tower | 0 | 0 |
| subnormal closure / strong conjugate | 0 | 0 |
| "generalized Fitting" / `C_G(\mathbf{F}(G))` パターン | 0 | 0 |

(BG に "Wielandt" の hit は 1 件あるが §IV.A の 群代数 \(\mathbf{F}G\) 上の固定点定理 — 別物.
Peterfalvi の "Wielandt" hits も全て fixed-point theorem または Hall-Wielandt p-group theorem
で、Ch.9 とは無関係.)

**理由**: FT は odd-order ⇒ solvable を示すので, 主役の \(G\) は (最終的に) 可解.
可解群では \(\mathbf{F}(G) \supseteq \mathbf{C}_G(\mathbf{F}(G))\) が既に成立 (Isaacs Prob 3B.14 /
Cor 9.9) し, \(\mathbf{F}^{*}(G) = \mathbf{F}(G)\) で augmentation 不要. quasisimple 成分や
layer は FT の解析対象に現れない.

→ §1G Chermak-Delgado と同じ位置付け. **Phase 1 では着手せず**, BG/Peterfalvi の章を
進める過程で必要が判明したら戻る運用が合理的.

## 章のセクション分割と全 31 結果

mmd 抽出では `### 9a`, `### Problems 9A`, `### 9b`, `**Problems 9B**`, `### 9c`,
`### Problems 9C`, `**Problems 9D**` は捕捉できているが, `### 9d` ヘッダ自体は欠落
(`[MISSING_PAGE_FAIL:302]` で消失). 9D は Theorem 9.28 の直前 (mmd L5199 周辺) から開始
と推定.

| § | mmd 行 | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 9A | 4883-4983 | quasisimple / component / layer / F*(G) 定義と基本性質 | 9.1 – 9.9 | F* 定義 (L4970), F* ⊇ C_G(F*) (9.8, Bender) |
| 9B | 4999-5141 | Wielandt の automorphism tower theorem | 9.10 – 9.22 | Wielandt aut tower (9.10), Schenkman C(S^∞) ⊆ S^∞ (9.21) |
| 9C | 5144-5188 | Thompson の corefree maximal subgroup bound (Wielandt 簡略化) | 9.23 – 9.27 | Thompson \|H:O_p(H)\| ≤ ((m!)²)! (9.23) |
| 9D | ~5199-5290 | Bartels: 強共役と subnormal closure の一致 | 9.28 – 9.31 | Bartels X^{(G)} = X^{*G} (9.28) |

### § 9A — Generalized Fitting subgroup F*(G) (lines 4883-4983)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 9.1  | Lemma   | G/Z(G) simple ⇒ G/Z 非可換, G' perfect, G'/Z(G') ≅ G/Z | L4892 |
| 9.2  | Lemma   | G quasisimple, N◁G proper ⇒ N ⊆ Z(G); 全 nontrivial 商も quasisimple | L4904 |
|      | Def     | **quasisimple** = G/Z(G) simple かつ G perfect (L4900) | |
|      | Def     | **component** of G = subnormal quasisimple subgroup (L4910) | |
| 9.3  | Lemma   | N minimal normal in G, H component, H⊄N ⇒ [N,H]=1 | L4912 |
| 9.4  | Theorem | 異なる 2 つの components H, K ⇒ [H,K]=1 (∴ 互いに正規化) | L4916 |
|      | Def     | **layer** \(\mathbf{E}(G)\) = product of components, characteristic in G (L4926) | |
|      | Def     | **semisimple** = product of nonabelian simple normal subgroups (L4928) | |
| 9.5  | Lemma   | semisimple ⇒ direct product of その simple factors, minimal normals = factors | L4932 |
| 9.6  | Lemma   | N minimal normal in finite G ⇒ N abelian or semisimple | L4942 |
| 9.7  | Theorem | E=E(G), Z=Z(E): (a) E'=E, (b) E/Z semisimple, (c) ∀ solvable M◁G で [E,M]=1 | L4954 |
|      | Def     | **generalized Fitting subgroup** \(\mathbf{F}^{*}(G) = \mathbf{F}(G)\mathbf{E}(G)\) (L4970) | |
| 9.8  | Theorem | **Bender**: \(\mathbf{F}^{*}(G) \supseteq \mathbf{C}_G(\mathbf{F}^{*}(G))\) | L4972 |
| 9.9  | Corollary | F*(G) ⊇ F(G); 等号 ⇔ F(G) ⊇ C_G(F(G)) | L4978 |

### § 9B — Wielandt's Automorphism Tower (lines 4999-5141)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 9.10 | Theorem | **Wielandt aut tower**: Z(G)=1 ⇒ aut tower Gᵢ = Aut(Gᵢ₋₁) は有限種 | L5006 |
| 9.11 | Lemma   | Inn(G) ◁ Aut(G), Z(G)=1 ⇒ C_{Aut(G)}(Inn(G))=1, Z(Aut(G))=1 | L5020 |
| 9.12 | Lemma   | tower で C_{Sᵢ₊₁}(Sᵢ)=1 chain ⇒ C_G(S₁)=1 | L5045 |
| 9.13 | Theorem | S◁G, C_G(S)=1 ⇒ \|G\| は isomorphism type(S) のみで bounded | L5055 |
| 9.14 | Lemma   | N◁G, N⊇C_G(N) ⇒ \|G\| ∣ \|Z(N)\|·\|Aut(N)\|; さらに \|G\| ∣ \|N\|! | L5059 |
| 9.15 | Lemma   | G=SF, S, F◁G, F nilpotent ⇒ G^∞ = S^∞ | L5069 |
| 9.16 | Cor     | S subnormal in G ⇒ F(G) ⊆ N_G(S^∞) | L5075 |
| 9.17 | Lemma   | S◁◁G, S nonabelian simple ⇒ S^G minimal normal, S ⊆ Soc(G) | L5081 |
| 9.18 | Cor     | S subnormal ⇒ E(G) ⊆ N_G(S^∞) | L5085 |
| 9.19 | Lemma   | N◁G, N⊆Φ(G), G/N nilpotent ⇒ G nilpotent | L5091 |
| 9.20 | Lemma   | N◁G, G/N nilpotent ⇒ ∃ nilpotent H⊆G with NH=G | L5095 |
| 9.21 | Theorem | **Schenkman**: S◁G, C_G(S)=1 ⇒ C_G(S^∞) ⊆ S^∞ | L5099 |
| 9.22 | Theorem | Z(G)=1 ⇒ C_G(G^∞) ⊆ G^∞ (9.21 の S=G ケース) | L5103 |

主要 dependency: 9.14 ← 9.21 ← (9.15-9.20) と 9.13/9.10 ← (9.16, 9.18 → F*(G) が S^∞ 正規化).

### § 9C — Thompson-Wielandt corefree maximal bound (lines 5144-5188)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 9.23 | Theorem | **Thompson**: corefree maximal H, m=\|H:H∩H^g\| ⇒ ∃p, \|H:O_p(H)\| ≤ ((m!)²)! | L5151 |
| 9.24 | Theorem | 一般版 (H, K distinct, D=H∩K, M=core_H(D), N=core_K(D), E=M∩N, U=core_H(E), V=core_K(E) ⇒ U or V が p-群) | L5155 |
| 9.25 | Lemma   | F(G)=1, E(G)⊆H ⇒ E(G)=E(H) | L5161 |
| 9.26 | Lemma   | G=SP, S◁G, P◁G p-group ⇒ O^p(G) = O^p(S) | L5167 |
| 9.27 | Cor     | S◁G, P◁G p-group ⇒ P normalizes O^p(S) | L5173 |

(Sims conjecture の文脈. Thm 9.23 は CFSG-free な部分結果. Thm 9.24 の証明で §9A の F*(G) と §9B の S^∞ を使う.)

### § 9D — Bartels' subnormal closure theorem (lines ~5199-5290)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
|      | Def     | **strongly conjugate**: Y = X^g かつ g ∈ ⟨X,Y⟩ | (定義ページ MISSING_PAGE_FAIL:302 で欠損) |
|      | Def     | X^{(G)} = ⟨ all strong conjugates of X ⟩ | |
| 9.28 | Theorem | **Bartels**: X^{(G)} = X^{*G} (subnormal closure) | L5201 |
| 9.29 | Lemma   | X^{(G)} の基本性質: S◁G ⊇ X ⇒ X^{(G)}⊆S; Y⊆X ⇒ Y^{(G)}⊆X^{(G)} 等 | L5209 |
| 9.30 | Lemma   | N◁G ⇒ \(\overline{X^{(G)}} = \overline{X}^{(\overline{G})}\) | L5224 |
| 9.31 | Lemma   | S◁G, P ∈ Syl_p(G) ⇒ P∩S ∈ Syl_p(S) | L5236 |

注: 9.31 は実は §9D 内に置かれているだけで, §9C 証明や §9B でも使える一般補題. mathlib `Sylow.subgroupOf` 等の周辺で類似ありそう (要確認).

## mathlib カバレッジ

Ch.9 の主要概念は **どれも mathlib 未収載** (mmd grep 結果: quasisimple 0 件, Subgroup.layer 0 件, fittingStar / FStar 0 件, subnormalClosure 0 件, stronglyConjugate / StrongConjugate 0 件, GroupTheory 内 socle 0 件).

| Isaacs | mathlib | 備考 |
|---|---|---|
| quasisimple | **無し** | `Mathlib/GroupTheory/IsPerfect.lean` は perfect 群を扱う. `G/Z(G) simple` 部分を独立に書く |
| component | **無し** | `IsSubnormal` + quasisimple の合成として定義 |
| layer E(G) | **無し** | components の sup として定義. `IsSubnormal` API は存在 |
| F*(G) | **無し** | `Subgroup.fitting` (`OddOrder.Isaacs.Ch01` で実装済) と `Subgroup.layer` の積 |
| socle Soc(G) | **無し** | minimal normal の sup. Thm 9.17 で使用 |
| S^∞ (nilpotent residual) | **無し** | lower central series の極限. `Mathlib/GroupTheory/Nilpotent.lean` 周辺に直接無し (要再確認) |
| strongly conjugate | **無し** | §9D 専用. 独立に定義 |
| X^{*G} (subnormal closure) | **無し** | "smallest subnormal subgroup containing X". `IsSubnormal` ベースで `sInf` |
| Lemma 9.31 (S◁G, Sylow_p ∩ S) | **存在?** | `Sylow.subgroupOf` 周辺で類似がありそう (要確認) |

`Subgroup.IsSubnormal` の基本 API は `Mathlib/GroupTheory/IsSubnormal.lean` に整備済 (Ch.2 ノート参照) なので, Ch.9 の subnormal 関連は base API 上に書ける.

## 着手しない方針 (推奨)

Phase 1 内での Ch.9 の扱い:

1. **§9A-D 全てスキップ** が最有力. FT critical path で要 0 件.
2. ROADMAP Phase 1 チェックリストの `Ch.9` 項目は「**FT 経路では未着手 — BG/Peterfalvi 進行中に必要が判明したら戻る**」と注記.
3. Phase 2a / 2b 進行中, BG mmd や Peterfalvi mmd で予想外に quasisimple / F* / layer が出現したら戻って実装.
4. §1G Chermak-Delgado, Ch.10 の一部 (FT で不要な部分) と扱いを揃える.

## 着手する場合の最小構成

もし F*(G) を Phase 1 で書きたくなった場合 (例: mathlib upstream を視野に入れたい), 最小依存で書ける順:

1. **`Group.IsQuasisimple G`**: `G.IsPerfect ∧ IsSimpleGroup (G ⧸ center G)`
2. **`Subgroup.IsComponent (H : Subgroup G) := H.IsSubnormal ∧ IsQuasisimple H`**
3. **`Subgroup.layer G := ⨆ H ∈ components G, H`** — Thm 9.4 で component 同士が互いに正規化することを使い well-defined product になる
4. **`Subgroup.fittingStar G := Subgroup.fitting G ⊔ Subgroup.layer G`**
5. **Thm 9.8 (Bender)**: \(\mathbf{F}^{*}(G) \supseteq \mathbf{C}_G(\mathbf{F}^{*}(G))\). 9.6 (minimal normal の二分律) + 9.7(c) (E(G) と solvable normal の commutator) 経由.

これだけで §9A 単体は閉じる. §9B (aut tower), §9C (Thompson), §9D (Bartels) は更にスコープ大で, FT 不要が確定している以上 Phase 1 では実装しないのが妥当.

§1G Chermak-Delgado を Ch.1 で省略している前例を踏襲する.

## 未解決の疑問

* §9C Thm 9.24 の証明は F*(G) と S^∞ を使う. もし §9A を書くなら §9C も自然な続きになるか?
  → 書くなら §9A → §9B → §9C のシーケンス (§9D は独立で別途).
* Lemma 9.31 (S◁G なら Sylow ∩ S ∈ Syl_p(S)) は mathlib に類似があるか?
  → `Sylow.subgroupOf`, `Sylow.smul` 周辺を grep する価値あり. もし既存なら Ch.2 の他補題と一緒に
  ラッパー除外 ([[feedback_no_mathlib_wrapper]]).
* S^∞ (nilpotent residual / lower central series limit) は mathlib `Mathlib/GroupTheory/Nilpotent.lean`
  の `lowerCentralSeries` を使って `⨅ n, lowerCentralSeries G n` で書けるはず. 既存 lemma 量を要調査.
* "subnormal core" (Problem 9D.1) — `Subgroup.IsSubnormal` の最大下界として `sSup` で構成可能.
  mathlib 一般化候補だが Phase 1 では不要.
