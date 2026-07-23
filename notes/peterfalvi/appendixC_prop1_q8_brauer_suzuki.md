# Peterfalvi App.C Prop 1 — Q₈ 部分ケースと Brauer–Suzuki / modular character theory 調査

> **⚠ 凍結（ユーザー裁定 2026-07-23）**: Q₈ を閉じる modular char theory 整備は**書籍選定を含む
> 長期プロジェクトとして凍結**。project spec = [`../meta/q8_modular_char_theory_frozen_project.md`](../meta/q8_modular_char_theory_frozen_project.md)、
> 追跡 = issue 0147（pending）/ 9318（closed、|S|≥16 完了）。**本 note は当時の前提調査**として保持。

> **作成 2026-07-22**（Q₈ gap の frontier 戦略調査）。対象 = `OddOrder/Peterfalvi/Appendices/NearFields.lean`
> の `rankOne_affine_nearField`（App.C Prop 1）に残る唯一の sorry。
> **問い**: この Q₈（`|S| = 8`）部分ケースを、**modular character theory を新設せずに**閉じる経路はあるか？
> **結論（確定）**: 文献上、**character-free / modular-free な経路は存在しない**。Q₈ は真に character theory
> （`|S| = 8` は modular）を要する。ユーザーの当初の直感が正しい。ただし **App.C は FT critical path 外**
> （mathcomp が App.C 無しで FT 完成）ゆえ低優先繰延が妥当。

## 0. 検証の出所（自分で直接確認 vs secondary）

- **直接確認**: Gorenstein *Finite Groups* Ch.12 Thm 1.1 原文（`references/gorenstein/finite-groups.pdftotext.txt`）/
  Peterfalvi App.C pp.137–138 原文（`references/peterfalvi/pdftotext/07.0_..._On_Near-Fields.txt`、OCR 語順崩れを再構成）/
  `coq/theories/` の grep（BS・near-field の**不在**を実測）/ repo の `RankOneHypothesis` 定義。
- **secondary（未直接読）**: Wong 1972 の内部論法・Mousavi (Comptes Rendus 2020s) の証明技法は
  **web 検索要約 + 論文 abstract 経由**（Wong の PDF はスキャン画像で本文抽出不可だった）。
  ⚠ 以下 Wong の「Suzuki's results を invoke」は secondary description。ただし (a) character-free BS が
  未知である一般事実、(b) Mousavi も参考文献に BS を含む事実、で裏打ちされる。

## 1. 障壁の正体（精密化）

`RankOneHypothesis`（= Peterfalvi (A1)(A2) + 2-rank 1）は **(A1) `G` が Ω に 2-可移 + (A2) faithful +
2-rank 1**（`NearFields.lean:635`〜）。near-field 結論は `G = F ⋊ H`（`F` = regular normal、`Q ≅ F*`）。

**Burnside の 2-可移群 dichotomy（character-free, CFSG 不要）**:

```
2-可移群 G ─┬─ affine type（regular elementary abelian normal 部分群 F あり）→ G = F ⋊ H → near-field ✓（BS 不要）
            └─ almost simple type（nonabelian simple socle）← これを排除するのが Prop 1 の核心
```

2-rank 1 の almost-simple には **cyclic か generalized quaternion Sylow-2 を持つ nonabelian simple 群**が要る:

| Sylow-2 | simple を排除する手段 | character-free? |
|---|---|---|
| cyclic | Burnside の normal 2-complement（transfer） | ✅ 初等的 |
| gen. quaternion **`\|S\| ≥ 16`** | exceptional character（Gorenstein Ch.12 Lem 1.2–1.9, ordinary） | ⚠ ordinary だが character 使用 |
| **quaternion `Q₈`（`\|S\| = 8`）** | **Brauer–Suzuki のみ** | ❌ **modular 必須** |

⟹ **「no simple group has `Q₈` Sylow-2」≡ BS-`Q₈` ≡ modular character theory の場合**。
Frobenius/Zassenhaus 経路（near-field 乗法群 = Frobenius complement、Sylow は cyclic/quaternion で
character-free）は **「affine であること」を前提**とするが、それを示すこと自体が almost-simple 排除 = BS
なので **bypass にならない**。

## 2. Gorenstein / Peterfalvi 原文（直接確認）

- **Gorenstein Ch.12 Thm 1.1**（原文）: 「gen. quaternion Sylow-2 **of order at least 16** … center of
  `G/K` is of order 2. **The same result holds when `S` is quaternion, but all known proofs require the
  theory of modular characters.**」→ `|S| = 8` の modular 必須は Gorenstein の明言。
- **Peterfalvi App.C Prop 1 証明**（pp.137–138, 原文再構成）: 「By [H]（Huppert III 8.2）Sylow-2 は cyclic
  or gen. quaternion」→「**By Brauer–Suzuki, `G = O₂'(G)·C_G(u)`**」→「Feit–Thompson で `O₂'(G)` solvable」
  →「Huppert II 3.2 で elementary abelian regular normal」→ near-field。
  **Peterfalvi は BS を black box として cite し cyclic/quaternion を区別しない** → full BS（`Q₈` 込み）依存。

## 3. mathcomp/Coq の scope（直接確認・重要）

`coq/theories/` を grep: **Brauer–Suzuki も near-field（App.C）も一切形式化されていない**
（`grep -riE 'brauer|near.?field|quaternion'` が完全に空、PF appendix ファイルなし。PFsection1–14 のみ）。

⟹ **App.C Prop 1 は FT critical path 外**。mathcomp は App.C 無しで FT を完成させた。Peterfalvi 本文が
App.C を cite する箇所（First Case 等）を mathcomp がどう回避したかは別途要調査だが、少なくとも
**Q₈ gap を閉じても FT 形式化には寄与しない拡張完全性 work**。形式化の前例も無い。

## 4. Wong 1972 の深掘り（bypass 候補 → 否定）

Wong, *Finite groups with a self-centralizing subgroup of order 4*（J. Aust. Math. Soc.）。

- **Theorem 2** = **cyclic `C4` の self-centralizing**（`Q₈` の `⟨i⟩` が該当、Klein four `V4` ではない）を扱い、
  「`S` は gen. quaternion or cyclic order 4」でまさに `Q₈` を含む。involution `r = i²` は `Z(S)`。
- ⚠ しかし secondary description によれば、その quaternion 部分で **「by Suzuki's results, `G/K ≅`
  SL(2,3)/SL(2,5)/A₇/PSL(2,7)/PSL(2,9) or index-2 normal」** と **Suzuki の character-theoretic 結果を
  invoke** している。→ **quaternion case は character-free でない**。
- 先の検索が「character-free」と述べたのは Wong の**別定理（`V4`, 2-rank ≥ 2）**の話か過度の要約。
- 結果リストの quaternion-Sylow-2 群（SL(2,3), SL(2,5)）は**非 simple**（center `Z2`）で BS と整合。simple な
  A₇/PSL(2,7)/PSL(2,9) は **dihedral** Sylow-2 で `Q₈` でない。⟹ Wong も「simple に `Q₈` Sylow-2 なし」を
  **Suzuki の character 経由**で得ている。

## 5. 現代文献（Mousavi 2020s）

Mousavi, *Finite groups with Quaternion Sylow subgroup*（Comptes Rendus）: 「quaternion Sylow-2 の `G` は
`3∤|G|` **or**（`G` solvable かつ `|S| > 16`）なら 2-nilpotent」。参考文献に **Brauer–Suzuki + Glauberman
factorization**。clean な結論が `|S| > 16` 条件付き = **`Q₈`（`|S| = 8`, `3∣|G|`、例 SL(2,3) 位数 24）は
依然 BS 依存**。character-free 化していない。

## 6. 結論と repo への含意

- **Q₈ を BS 経由で閉じる = modular 表現論の新設が不可避**（大規模。Gorenstein/文献が裏打ち）。
- **character-free な代替は文献上存在しない** — Wong も Mousavi も結局 Suzuki/Brauer–Suzuki（character、`Q₈` は
  modular）を使う。「no simple group has `Q₈` Sylow-2」の character-free 証明は 2013 時点でも未知。
- **App.C は FT 非依存**（mathcomp 実測）ゆえ **Q₈ gap は低優先繰延が正しい**。
- **正しい落とし所**: lane c の transport（`GroupTheory/NearFieldFromSharplyTransitive.lean`）が Prop 1 を
  **cyclic + gen. quaternion `|S| ≥ 16` の全ケースで閉じ**、残 sorry を **`Q₈`（`|S| = 8`）1 点に孤立化**する。
  その 1 点だけが modular 待ち。将来 Q₈ を本気で閉じるなら「1 gap 埋め」でなく「modular 表現論基盤の新設」
  という別スケールのプロジェクト（あるいは Zassenhaus 例外 near-field 7 個の有界列挙という泥臭い中規模路線）。

## 7. 未解決の副次論点（やるなら）

- Peterfalvi 本文が App.C Prop 1 を実際に **どこで cite し、mathcomp がそれをどう回避したか** の精査
  （→ repo でも App.C を bypass して First Case を書けるなら、Prop 1 自体が不要になる可能性。ただし
  「3 冊全形式化」方針では App.C は in-scope）。
- `|S| = 8` 有界ケースの直接列挙（Zassenhaus 例外 near-field）が modular 無しで書けるかの feasibility。

## Sources

- Gorenstein, *Finite Groups*（AMS 1968）Ch.12 Thm 1.1（原典・直接確認）
- Peterfalvi, *Character Theory for the Odd Order Theorem*（LMS LNS 272）App.C pp.137–138（原典・直接確認）
- `coq/theories/`（mathcomp odd-order、BS・App.C 未形式化を grep 実測）
- Wong, *Finite groups with a self-centralizing subgroup of order 4*, doi:10.1017/S1446788700004511（secondary）
- Mousavi, *Finite groups with Quaternion Sylow subgroup*, doi:10.5802/crmath.131（abstract）
- Brauer–Suzuki theorem / Frobenius complement / Z\* theorem（Wikipedia、方法の裏取り）
