# Isaacs Ch.9: More on Subnormality — mini-roadmap

> 🚧 **形式化進行中 (レーン a, 2026-07-17〜)** — 全 3 冊フェーズ (2026-07-16〜) で deferred 解除。
> 旧 banner「FT 経路外につき deferred (2026-07-02)」は失効。
> 進捗 (全 sorry-free): §9A `Quasisimple.lean` (`IsQuasisimple` + Lem 9.1/9.2) →
> `Components.lean` (`IsComponent` + Lem 9.3 + Thm 9.4 distinct components commute) →
> `Semisimple.lean` (`IsSemisimpleGroup` + Lem 9.5 直積性/centerless + Lem 9.6
> minimal normal は abelian/semisimple) → `Layer.lean` (`layer G` = E(G) 定義・共役不変で
> `G`-normal + Thm 9.7 (a) E'=E, (b) E/Z(E) semisimple, (c) [E,M]=1 for solvable normal M)。
> → `GeneralizedFitting.lean` (`genFitting G` = F\*(G) 定義 + Cor 9.9 `←`:
> `F ⊇ C(F) ⇒ F*=F`, 9.7(c) 依存)。**§9A 残 = Thm 9.8 (Bender 一般形
> `C_G(F*) ⊆ F*`) + Cor 9.9 `→`** のみ (同 `GeneralizedFitting.lean` に追記予定)。
>
> Thm 9.8 の設計 (書籍 p.275 忠実): `C := C_G(F*)`, `Z := C ⊓ F*`, 反証で `Z < C` →
> `G/Z` の minimal normal `N̄ ≤ C.map q` を取り Lem 9.6 で abelian/semisimple 分岐。
> abelian: `M := comap q N̄` は `⁅M,M⁆ ≤ Z ≤ Z(M)` ゆえ nilpotent → `M ≤ F(G) ⊆ F*` かつ
> `M ≤ C` → `M ≤ Z` で `N̄ = ⊥` 矛盾 (nilpotent 補題は `isNilpotent_of_ker_le_center` +
> `isMulCommutative_of_commutator_eq_bot`)。semisimple: `↥N̄` の minimal normal `T̄`
> (nonabelian simple, `IsSemisimpleGroup.isSimpleGroup_of_isMinimalNormal`) を `Ḡ` へ押し上げ
> `S := comap q` → `S ◁ M ◁ G` subnormal, `Z = Z(S)`, Lem 9.1 で `⁅S,S⁆` quasisimple =
> component `⊆ E ⊆ F*` かつ `⊆ C` → `⊆ Z` で `S̄` abelian, nonabelian simple と矛盾。
> semisimple 枝は T̄ (↥N̄) → Ḡ → G の 3 段 subtype 輸送が重い。

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.9 (pp. 271-294).
形式化先: `OddOrder/Isaacs/Ch09_MoreSubnormality/` (topic leaves; 2026-07-17 開始).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 4880-5310.
ROADMAP 上の位置: **第 3 波 (Ch.2 完了後、並列可)** — 直接前提は Ch.2 (Thm 2.6 minimal normal が subnormal を正規化, socle 概念), 軽く Ch.1 (Fitting, 冪零).

4 視点 framework 適用 (2026-05-23 audit 統合): 詳細クロス参照 [`../meta/ch08_10_audit_2026_05_23.md`](../meta/ch08_10_audit_2026_05_23.md).

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

## Definitions inventory (2026-05-23 audit 統合)

Ch.9 で導入 (または recall) される全 14 定義. 上記 §9A-§9D 表の "Def" 行 + 暗黙導入分を集約.

| # | 定義名 | mmd | 説明 | mathlib 対応 |
|---|---|---|---|---|
| 1 | perfect | L4890 | `G = G'` (recalled from Ch.2) | `IsPerfect` (`GroupTheory/IsPerfect.lean`) ✅ |
| 2 | quasisimple | L4900 | `H/Z(H)` simple ∧ `H` perfect | 無し (合成定義) |
| 3 | component of `G` | L4910 | subnormal quasisimple subgroup of `G` | 無し |
| 4 | layer `E(G)` | L4926 | ⟨all components⟩, characteristic in `G` | 無し |
| 5 | semisimple | L4928 | nonabelian simple normal subgroups の product (Isaacs convention; abelian factor 不可) | 無し |
| 6 | generalized Fitting `F*(G)` | L4970 | `F(G) · E(G)` | 無し |
| 7 | automorphism tower | L5000-L5002 | `G ◁ Aut(G) ◁ Aut(Aut(G)) ◁ …` | 無し (`MulAut` iterated 自前) |
| 8 | complete group | L5012 | `Z(G) = 1 ∧ Aut(G) = Inn(G)` | 無し |
| 9 | `S^∞` nilpotent residual | L5063 | `lowerCentralSeries G` の final term (= `⨅ n, lowerCentralSeries G n`) | `lowerCentralSeries` ✅ あるが `∞` term 補題なし |
| 10 | corefree (subgroup) | L5145 | `core_G(H) = 1` | `Subgroup.normalCore = ⊥` ✅ |
| 11 | strongly conjugate | def at MISSING_PAGE L5199 | **`Y` strongly conj to `X` :⇔ `∃ g ∈ ⟨X, Y⟩, Y = X^g`** (下記復元) | 無し |
| 12 | `X^{(G)}` | L5205 | `⟨ Y : Y strongly conjugate to X ⟩` | 無し |
| 13 | `X^{*G}` subnormal closure | L5201 (RHS of 9.28) | smallest subnormal subgroup containing `X` (recalled from Ch.2) | 無し |
| 14 | subnormal core | Problem 9D.1 L5294 | largest subnormal subgroup contained in `H` | 無し |
| (補) | characteristically simple | Problem 9A.8 L4995 | proper characteristic subgroup 無し | 無し |

### §9D strongly conjugate def 復元 (MISSING_PAGE workaround)

mmd L5199 が `[MISSING_PAGE_FAIL:302]` で消失. Thm 9.28 (L5203) と Lem 9.29(b) (L5218) の使用文脈から
**一意に復元** 可能:

**`Y` strongly conjugate to `X` in `G` :⇔ `∃ g ∈ ⟨X, Y⟩, Y = X^g`**

復元根拠: Lem 9.29(b) は `Y ⊆ X` の場合の `Y^{(X)} ⊆ X^{(G)}` を主張するが, この argument が成立
するためには共役元 `g` を `⟨X, Y⟩` 内に取れる必要がある (`Y ⊆ X` のとき `⟨X, Y⟩ = X`). 単純な
`Y = X^g for some g ∈ G` だと Lem 9.29 が破綻するので, `g ∈ ⟨X, Y⟩` 制約が必須.

Lean 実装では `Subgroup.IsStronglyConjugate (X Y : Subgroup G) : Prop := ∃ g : G, g ∈ X ⊔ Y ∧ Y = X.map (MulAut.conj g).toMonoidHom` 形式.

## 視点 1: forward dependencies — Ch.9 は完全 leaf (2026-05-23 audit 統合)

- **Isaacs Ch.10 への被引用 0 件**: `grep -nE "(Theorem|Lemma|Corollary|Proposition) 9\.[0-9]+"` を
  Ch.10 範囲 (L5310-5914) で実行 → **0 件**.
- **BG mmd 0 件**: `quasisimple`, `\mathbf{F}^*`, `\mathbf{E}(`, `automorphism tower`, `Bartels`,
  `Schenkman`, `subnormal closure`, `strongly conjugate` 全 0. 表面的 hit (`Wielandt` 2 件 +
  `component` 2 件) は全て false positive = §III.C の Wielandt fixed-point thm + Wedderburn/Clifford
  components.
- **Peterfalvi mmd 0 件**: 同パターン全 0. 表面 hit (`Wielandt` 10 件 + `component` 23 件) も全て
  false positive = 同 fixed-point + Clifford component analysis.

**結論**: Ch.9 は本 1 冊内 leaf + 後続 2 冊で被引用 0. forward dep ゼロ.

## 視点 2: 章節内部の依存 (hub-and-spoke) (2026-05-23 audit 統合)

Ch.9 主要 hub (proof body で章内他結果を 2 件以上引く頻出 lemma):

- **9.4** (異なる 2 つの components は commute) — §9A spine の起点 hub
- **9.8 Bender** (`F*(G) ⊇ C_G(F*(G))`) — §9A 終局, 6.5, 9.7, 9.6 を統合
- **9.10 Wielandt aut tower** — §9B 看板, 9.13/9.12/9.11(d) 統合
- **9.21 Schenkman** — §9B 後半 motor, 9.20, 9.22, 9.15 + induction
- **9.24** (Thompson 一般版) — §9C 全体の支配定理
- **9.28 Bartels** — §9D 主結果
- **9.31** (Sylow ∩ subnormal) — §9D 内に置かれるが §9B/§9C でも汎用

**主要 chain**:
- §9A spine: `9.1 → 9.2 → 9.4 → 9.7 → 9.8`
- §9B tower bound: `9.14 → 9.21 → 9.13 → 9.10`
- §9C reduction: `9.25, 9.26, 9.27 → 9.24 → 9.23`
- §9D: `9.29 → 9.30 → 9.31 → 9.28`

**sharpening**: 既存ノートが 9.31 の mathlib 状況を「存在?」と flag していた件は本 audit で
**不在** 確定 (`Sylow.exists_comap_eq Sylow.lean:193` は別ステートメント). mathlib 表で更新済.

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
| Lemma 9.31 (S◁G, Sylow_p ∩ S) | **無し** (2026-05-23 audit 確定) | mathlib v4.29.1 直接 lemma 無し (`Sylow.exists_comap_eq` `Sylow.lean:193` は別ステートメント, `IsPGroup.inf_normalizer_sylow` `:277` も別). ~10 行 induction on `|G|` で新規 |

`Subgroup.IsSubnormal` の基本 API は `Mathlib/GroupTheory/IsSubnormal.lean` に整備済 (Ch.2 ノート参照) なので, Ch.9 の subnormal 関連は base API 上に書ける.

## 視点 3: mathlib status — proof-internal API per major theorem (2026-05-23 audit 統合)

statement-level coverage は上記表のとおりほぼ全て **無し**. ここでは **証明本体で呼ぶ mathlib API**
を per-target で列挙 (Ch.9 全結果は bucket (b)/(c), bucket (a) は無し).

| Thm | bucket | proof-internal mathlib API (v4.29.1, 必要箇所) |
|---|---|---|
| 9.1 | (b) | `IsPerfect` (`GroupTheory/IsPerfect.lean`), `Subgroup.center`, `QuotientGroup.mk`, `IsSimpleGroup`. helper: `G/Z(G) simple ⇔ G nonsolvable` 補強 |
| 9.2 | (b) | `Subgroup.Normal`, `QuotientGroup.quotientInfEquivProdNormalQuotient` (2nd iso) |
| 9.3 | (b) | **Three Subgroups** `Subgroup.commutator_commutator_eq_bot_of_rotate` (`Commutator/Basic.lean:109`); `Subgroup.commutator_le` |
| 9.4 hub | (b) | 9.3 + 9.2 + induction on `Nat.card G`; `IsSubnormal.map` (`IsSubnormal.lean:243`) |
| 9.6 | (b) | `Subgroup.fitting` (Ch.1 ✅), `Subgroup.center_normal`, `Subgroup.IsMinimalNormal` (Ch.2 ✅), Thm 2.6 (Ch.2 ✅) |
| 9.7 | (b) | Three subgroups + `IsSolvable` + 9.4, 9.5 |
| **9.8 Bender** | (c) | 9.6 + 9.5 + 9.1 + `Subgroup.fitting` + induction `|G:Z|` |
| **9.10 Wielandt aut tower** | (c) | `MulAut G` (`Algebra/Group/End.lean:698`), `MulAut.conj` (`Pointwise.lean:482`); iterated `Aut`. **mathlib に `Inn`/`Out` named subgroup 無し** ⇒ `Inn G := MonoidHom.range (MulAut.conj)` 自前. Bound: 9.13 + 9.12 + 9.11(d) |
| 9.13 | (c) | 9.21, 9.16, 9.18, 9.14; `Nat.card_perm`; helper `MulAut.card_le_factorial` 新規 |
| 9.14 | (b) | `MonoidHom.range` + `QuotientGroup.quotientKerEquivRange`, `Fintype.card_perm` |
| **9.15** | (b) | **`nilpotentResidual G := ⨅ n, lowerCentralSeries G n` 新規 helper**, mathlib `lowerCentralSeries` `Nilpotent.lean:299` あるが `infinityTerm` lemma なし |
| 9.17 | (b) | **`Subgroup.socle` 新規**, Thm 2.6 (Ch.2 ✅), 9.4, 9.5 |
| 9.19 | (b) | `Mathlib/GroupTheory/Frattini.lean` `frattini G`, `frattini_le_coatom` (mathlib 既存) |
| **9.21 Schenkman** | (c) | 9.20 + 9.22 + 9.15 + Dedekind + induction |
| **9.23 Thompson** | (c) | 9.24 (general); `Subgroup.normalizer`, `Subgroup.normalCore` (`Algebra/Group/Subgroup/Basic.lean:557`), `Sylow.opCore` |
| **9.28 Bartels** | (c) | 9.29-9.31 + 6 Steps L5240-5290 + induction on `|G|, |X|`; ~150 行 |
| **9.31** Sylow ∩ subnormal | (b) | **mathlib 不在 (上記カバレッジ表 確定)**, `Sylow.exists_comap_eq` を induction で wrap, ~10 行 |

**Helper 不在 list (新規, `OddOrder/GroupTheory/` 候補)**:

1. `Group.IsQuasisimple` (mathlib `IsPerfect` + `IsSimpleGroup G⧸Z` 合成)
2. `Subgroup.IsComponent`
3. `Subgroup.layer`
4. `Subgroup.fittingStar`
5. `Subgroup.socle` (Ch.2 min-normal infra 利用)
6. `Group.nilpotentResidual` (= `S^∞`)
7. `Subgroup.subnormalClosure` (`X^{*G}`)
8. `Inn G` named subgroup (= `MonoidHom.range (MulAut.conj)`)
9. `MulAut.card_le_factorial` (auxiliary)
10. `Sylow.inf_normal_isSylow` (= 9.31)

## 視点 4: 先行章節への依存 (per-target) (2026-05-23 audit 統合)

mmd L4880-5310 grep 結果:

| Ch.9 target | Ch.1-8 cite | 回数 | OddOrder 状態 |
|---|---|---|---|
| 9.3, 9.4, 9.6, 9.17, 9.18 | **Thm 2.6** (min normal が subnormal を正規化) | **5** | ✅ Ch.2 既実装 `isMinimalNormal_le_normalizer_of_isSubnormal` |
| 9.6 | Thm 1.19 (nilpotent ⇒ Z(N) nontrivial) | 1 | ✅ Ch.1 |
| 9.6 | `Subgroup.fitting` (Ch.1 §1D) | 1 | ✅ Ch.1 |
| 9.19 | Thm 1.26 (max normalizer ⇒ nilpotent) | 1 | ✅ Ch.1 |
| (intro prose only L4886) | Lem 3.21 (Hall-Higman) | 0 proof body | prose のみ — Ch.3 依存 **無し** |
| (intro prose only) | Thm 8.32, 8.33 (SL quasisimple) | 0 proof body | prose のみ |

**結論**: Ch.9 は **Ch.1 + Ch.2 のみ** に依存. Ch.3 Hall-Higman は prose 言及のみで proof body 内
では引かない. Ch.4-8 ゼロ. **§1G Chermak-Delgado 依存もゼロ** (`Chermak`, `Delgado`, `m_{CD}` ヒット 0).
⇒ Ch.9 は Ch.2 Thm 2.6 (既実装) 完了済の今, 着手 unblocked.

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

## Shared module 配置提案 (`OddOrder/GroupTheory/` 5-6 files) (2026-05-23 audit 統合)

Ch.4-7 audit (2026-05-22) で確立した **`OddOrder/GroupTheory/` shared module パターン** を Ch.9
にも適用. §9A 最小 bundle の場合のファイル分割:

```
OddOrder/GroupTheory/Quasisimple.lean         -- Group.IsQuasisimple, Lem 9.1, 9.2
OddOrder/GroupTheory/Component.lean           -- Subgroup.IsComponent, Thm 9.4
OddOrder/GroupTheory/Layer.lean               -- Subgroup.layer, characteristic, Thm 9.7
OddOrder/GroupTheory/FittingStar.lean         -- Subgroup.fittingStar, Thm 9.8 Bender, Cor 9.9
OddOrder/GroupTheory/Socle.lean               -- Subgroup.socle (Ch.2 min-normal infra 利用)
OddOrder/GroupTheory/NilpotentResidual.lean   -- Group.nilpotentResidual (S^∞)
-- 以下は §9D が必要になった場合:
OddOrder/GroupTheory/Subnormal.lean (拡張)    -- subnormalClosure, IsStronglyConjugate
```

**rationale**: `IsQuasisimple`, `Subgroup.socle`, `nilpotentResidual` はいずれも一般群論で頻出
する概念で plausibly **mathlib upstream 候補**. §9A 5-6 ファイルで `OddOrder/GroupTheory/` 配下
に置けば後の mathlib PR が容易.

§9B (aut tower) / §9C (Thompson) / §9D (Bartels) は `OddOrder/Isaacs/Ch09_MoreSubnormality/{S9B,
S9C,S9D}.lean` 階層配置だが **Phase 1 skip** (BG/Peterfalvi 0 件のため).

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

## 関連ノート (2026-05-23 audit 統合)

- [`../meta/chapter_investigation_framework.md`](../meta/chapter_investigation_framework.md) — 4 視点 framework template.
- [`../meta/ch08_10_audit_2026_05_23.md`](../meta/ch08_10_audit_2026_05_23.md) — 本 audit (Ch.8/9/10 統合) doc.
- [`ch01_sylow.md`](ch01_sylow.md) — Ch.1 依存 (Thm 1.19, 1.26).
- [`ch02_subnormality.md`](ch02_subnormality.md) — **Ch.2 Thm 2.6 ⭐ 5x dep** (9.3, 9.4, 9.6, 9.17, 9.18 すべての hub).
- [`ch01_sylow_d_fitting.md`](ch01_sylow_d_fitting.md) — `Subgroup.fitting` (9.6 で利用).
- [`../meta/mathlib_coverage.md`](../meta/mathlib_coverage.md) — 全体 mathlib カバレッジ.
