# 【長期プロジェクト（2026-07-25 解凍）】Q₈ Brauer–Suzuki のための modular character theory 整備

> **状態: THAWED（ユーザー裁定 2026-07-25）** — 書籍選定確定（spine = **Navarro 1998**、§2）、
> **PDF 確保済（2026-08-04、`references/navarro/`）** ⟹ 着手可能。
> 担当レーンは未割当（着手時に hub/ユーザーが指定）。
> ⚠ **経路訂正（2026-08-04 原文実測、§2''）**: 必要 slice は **Ch.1–6 + Ch.7 前半**で、
> **Z\*-定理は不要**（BS は Z\* の系ではなく前提）。
> ✅ **本プロジェクトは 2026-08-06 に完了**（Q₈ BS = `q8_exists_proper_normal`、issue 0147/9506）。
> ⚠ **その後 Z\*-定理は別スコープとして 2026-08-20 に完成**（ユーザー裁定で Ch.7 の残り
> (7.7)–(7.9) を対象化、issue 0186 closed）。`glauberman_zStar` /
> `glauberman_zStar_oddCore` / `glauberman_zStar_sup_centralizer_eq_top` が axiom-clean。
> したがって上の「Z\*-定理は不要」は **Q₈ BS を閉じるための経路としては不要**という意味で、
> 「repo に Z\* が無い」ではない — 再開時に取り違えないこと。
> 本 note は本プロジェクトの **project spec**（目的・書籍選定・infra 内訳・pickup 手順）。
> （旧状態: FROZEN、ユーザー裁定 2026-07-23 — §1 の凍結根拠は経緯の記録として保持。）

## 0. 一行

Peterfalvi Appendix C Proposition 1（`rankOne_affine_nearField`）に残る唯一の `sorry` =
**Brauer–Suzuki 定理の Q₈（`|S| = 8`）ケース**を閉じるには、mathlib に**皆無**の
**modular character theory（Brauer 指標・p-blocks・分解行列・defect group）を一から整備**する必要がある。
これは 3 冊の残作業とは**別スケールの独立プロジェクト**。2026-07-23 に凍結 → **2026-07-25 に解凍・
書籍選定確定（spine = Navarro 1998; §2）** → **2026-08-04 に PDF 確保 + 経路確定
（Ch.1–6 + Ch.7 前半、Z\* 不要; §2''）**。

## 1. 凍結の経緯（ユーザー裁定 2026-07-23 の根拠 — 2026-07-25 に解凍、記録として保持）

- **FT critical path 外**: mathcomp/Coq odd-order は App.C を**一切形式化せず** FT を完成させた
  （`coq/theories/` に BS も near-field も無し、grep 実測）。Q₈ を閉じても `feitThompson` には寄与しない
  **拡張完全性 work**。
- **terminal・下流消費者ゼロ**: `RankOneHypothesis.brauerSuzuki` の Q₈ 分岐を消費するのは
  `rankOne_affine_nearField` のみで、その先に FT spine への配線は無い。
- **mathlib-absent subfield**: modular 表現論（Brauer 指標・block・decomposition matrix）は mathlib に
  存在せず（`Mathlib/RepresentationTheory/` は char-0/ordinary のみ、2026-07-23 実測）、
  他の証明支援系（Lean/Isabelle 等）にも**先行形式化が無い**（web 実測 2026-07-23）= 完全 greenfield。
- **|S| ≥ 16 は既に完成**: ordinary exceptional character 経由の `brauerSuzuki_of_quaternionSylow`
  （`BrauerSuzukiEndgame.lean`、axiom-clean）が cyclic + 一般化四元数 `|S| ≥ 16` を被覆済み。
  **Q₈ だけ**が別ルート（Gorenstein Ch.12 Thm 1.1 明言:「all known proofs require the theory of
  modular characters」）。ordinary route は `|X| = 4 ⟹ R = ⟨x⁴⟩ = 1` で TI subset `A = C − RH` が
  退化して使えない（詳細 = `appendixC_prop1_q8_brauer_suzuki.md`）。
- ⚠ **恒久対象外ではない**（CLAUDE.md「文献に証明がある結果は低優先繰延であって除外しない」）。
  Q₈ BS は文献に完全な証明があるので、**in-scope の低優先・長期繰延**。cost/規模が繰延理由ではなく、
  **doc-order/terminal 性 + 別スケール infra**が理由（cost 非基準は維持）。

## 2. 書籍選定 — ★確定（ユーザー裁定 2026-07-25）

**spine = Navarro, *Characters and Blocks of Finite Groups*（Cambridge LMS LNS 250, 1998）
一冊のみ**（旧案「infra + 証明本体の 2 source」は不要になった）。

- **章構成（手元 PDF の目次で実測 2026-08-04、書籍ページ）**: 1 Algebras p.1 / 2 Brauer
  Characters p.16 / 3 Blocks p.48 / 4 第一主定理 p.80 / 5 第二主定理 p.99 / 6 第三主定理 p.119 /
  **7 The Z\*-Theorem p.131** / 8 p.150 / 9 p.192 / 10 p.222 / 11 p.243（8–11 は本件に不要）。
  2026-07-25 の Cambridge TOC と一致。
- ~~**Q₈ への bridge は初等**: Z\* で `z` の像が `Z(G/O(G))` に入る → …~~
  **⟹ 不要（§2'' の経路訂正）**。BS は Z\* を経由せず Ch.7 で直接証明される。
- **Dade 1971 / Brauer 1964 / Feit 1982 は併読に降格**（Gorenstein と同じ posture =
  行間補完・証明戦略の参照専用）。quaternion-defect block 分析の形式化は不要。
- **再サーベイ不要（2026-07-25 web 実測）**: Navarro 2018（McKay 本）にブロック章は無い。
  2020 年代の新刊教科書も無い。より新しい系統違いは Linckelmann 2018（module 圏・source algebra 系、
  行間補完 reference 向き）/ Craven 2019（証明なし survey）/ Webb 2016・Schneider 2013（入門どまり、
  三大定理・Z\* に届かない）。character-theoretic block 論の教科書としては Navarro 1998 が現在も最新。
- **PDF: ★確保済（2026-08-04）** — ユーザーが手配（正規無料版は無し）。
  `references/navarro/characters-and-blocks.pdf` + `.pdftotext.txt` + `SOURCE.md`
  （ISBN 978-0-521-59513-1 / DOI 10.1017/CBO9780511526015 / SHA-256 は SOURCE.md）。
  無料の併読素材: J. Miquel Martínez の Valencia 講義ノート（Navarro 流 modular rep、uv.es 公開）。
  - **⚠ PDF ページ = 書籍ページ + 10**（書籍 p.1 = PDF p.11、書籍 p.131 = PDF p.141 で実測）。
  - スキャン（300 dpi bitonal）+ OCR レイヤ。**Peterfalvi 型のグリフ分解は無い**
    （single-char token 率 20.8% = 正常域）ので素の `pdftotext -layout` で散文が読め grep も効く。
  - ⚠ **数式・記号の OCR 崩れは重い**: `∈`→`G`/`£`/`e`、`N`→`TV`、`R`→`ii`/`i?`、`→`→`—>`、
    `Irr`→`IYT`、`1_B`→`!#`、`Q_8`→`Qs`。**statement・添字・仮定の確定はページ画像で**
    （切り出したら `references/navarro/pages/navarro-p<書籍ページ>.png` に残す）。

### 2''. ★経路の訂正（2026-08-04、Ch.7 原文の実測）— **Z\*-定理は経路から落ちる**

PDF 到着後に Ch.7 を実際に読んだ結果、**当初計画（Q₈ BS = Z\* の系、bridge は初等）は逆だった**。
Navarro の Ch.7 は BS を**先に**証明し、それを使って Z\* に進む:

| 書籍 pp. | 内容 |
|---|---|
| 131 | Ch.7 冒頭 "we finally give a proof of Glauberman's Z\*-theorem. **First, we need to prove the Brauer–Suzuki theorem**" / (7.1) BS statement |
| 131 | "The deep part of the theorem involves the case when the Sylow 2-subgroup is the **quaternion group of order 8**, and this is what we will focus on here"（`|S| > 8` は Isaacs *Characters* Thm 7.8 に外出し） |
| 133–138 | (7.2) Klein four Sylow-2 / (7.3) basic set の定義 / (7.4) / (7.5) / (7.6) — BS の feeder |
| **139–146** | **"Proof of the Brauer–Suzuki Theorem"**（Q₈ 本証明。y での解析 → t での解析 → 主 block の非自明指標が t を kernel に含む） |
| 146 | "To prove Glauberman's Z\*-theorem, **we need one more result**…" → (7.7) / (7.8) |
| 146–149 | (7.9) Z\*-THEOREM（Glauberman） |

**帰結**:

- **必要 slice = Ch.1–6 + (7.1)–(7.6) + BS 本証明（pp.139–146）**。
  **(7.7)–(7.9) と「Z\* → Q₈ bridge」は不要**（bridge の初等補題を書く手間も消える）。
- Navarro が名指しで狙っているのが**まさに Q₈ ケース**で、`|S| > 8` は Isaacs に外出ししている
  ⟹ repo 側の既存分担（`brauerSuzuki_of_quaternionSylow` が `|S| ≥ 16` を被覆、Q₈ だけ残 sorry）と
  **教科書の分担が一致**する。橋渡しの設計を考える必要が無い。
- BS 本証明が直接引く結果: **Cor (6.13)**（normal 2-complement な群の主 block: `IBr(b₀)` 単元・
  Cartan 行列 (4)）/ **Cor (5.8) + 第三主定理** / **Lemma (5.13.b)** / **block orthogonality** /
  (7.2) の Klein four ケース / (7.3) basic set。
- 副作用として「`|S| ≥ 16` も同時被覆され既存 ordinary route の独立検算になる」という旧 §2 の
  見込みは**消える**（Navarro は `|S| > 8` を証明しないため）。既存 route の置換は元々しない方針。

### 2'. 選定の経緯（候補比較、2026-07-23 時点の記録 — 上記★確定で supersede）

Q₈ BS の証明本体と、その前提となる modular char theory infra は**別々の source**から取るのが自然
と当初は想定していた（下記は当時の候補と判断材料）。

### 2a. Q₈ BS 証明本体の source 候補

| 候補 | 内容 | 形式化適性 |
|---|---|---|
| **Dade 1971**, *Character Theory Pertaining to Finite Simple Groups*（Powell–Higman 編 *Finite Simple Groups*, Academic Press, Ch. VIII） | **Wikipedia が「detailed proof」として挙げる正典**。block 論による BS の自己完結的な講義録。 | ★ 第一候補（証明が明示的・自己完結） |
| **Brauer 1964**, "Some applications of the theory of blocks of characters of finite groups. II"（J. Algebra） | Brauer 自身の block-理論的証明。 | ○（原論文、密） |
| **Brauer–Suzuki 1959**（PNAS）+ **Suzuki 1962**（"Applications of group characters"） | 原典。 | △（簡潔すぎ・古い記法） |
| **Gorenstein**, *Finite Groups* Ch.12 | `|S| ≥ 16` は形式化済（repo）。Q₈ は「modular 要」と cite するのみで**証明を載せない**。 | ✗（Q₈ の証明源にならない） |

### 2b. modular char theory infra の source 候補

| 候補 | 内容 | 形式化適性 |
|---|---|---|
| **Navarro**, *Characters and Blocks of Finite Groups*（Cambridge LMS 250, 1998） | modern・clean・自己完結な block 論。定理文が formalization-friendly と定評。 | ★ 第一候補 |
| **Feit**, *The Representation Theory of Finite Groups*（North-Holland, 1982） | 網羅的（Brauer の三大定理・block・defect すべて）。密。 | ○（網羅的だが重い） |
| **Nagao–Tsushima**, *Representations of Finite Groups*（Academic Press, 1989） | 網羅的な代替。 | ○ |
| **Isaacs**, *Character Theory of Finite Groups* | 大半が ordinary。modular/block は限定的で Q₈ には不足。 | △（単独では不十分） |

### 2c. 選定基準

1. **自己完結性**（外部前提が少なく、mathlib + repo の既存 ordinary char theory の上に積める）。
2. **statement の clean さ**（Navarro が定評、Dade は講義録ゆえ明示的）。
3. **Q₈ の完全証明に到達可能**（Dade/Brauer/Feit は到達、Isaacs 単独は不足）。
4. **repo 資産との整合**（既存の `ClassFunction`/`IrreducibleCharacter`/induced/TI-isometry API と接続しやすいか）。

**暫定推奨（2026-07-23; 2026-07-25 の★確定で supersede — Navarro 一本化、Dade は併読へ）**:
infra = **Navarro**、証明本体 = **Dade 1971**（または一冊で通すなら **Feit**）。
⚠ これらは**新規参照書**（3 冊スコープ外）で、Gorenstein と同じ posture = **行間補完・証明戦略の参照専用**
（逐語コピーはしない、ライセンス複製可否のみが基準、[[feedback-external-formalization-reference-ok]]）。
PDF/所在の確保も pickup 時のタスク。

## 3. 整備すべき infra の内訳（Q₈ BS が要求する最小セット）

mathlib は char-0 ordinary のみ。以下は全て新設（`OddOrder/GroupTheory/RepresentationTheory/Modular/` 等）:

1. **p-modular system**: 完備 DVR `O`（剰余体 `k` char `p`、商体 `K` char `0`）、"large enough"/splitting。
2. **Brauer 指標（IBr）**: mod-`p` 還元の `p`-regular 元上のトレースを char 0 に持ち上げたもの。
   `p`-regular class の個数 = `|IBr|`。
3. **分解行列 `D`**（`χ = Σ_φ d_{χφ} φ` on `p`-regular）+ **Cartan 行列 `C = DᵀD`**。
4. **block 論**: `Irr ∪ IBr` の central character mod `p` による分割、**defect group**、Brauer 対応。
5. ~~**Q₈ 固有部分**: principal 2-block + quaternion defect の構造分析~~ → **不要（2026-07-25 確定）**:
   Z\* 経由に置換。残るのは「Z\* → `G = O_{2'}(G)·C_G(z)`」の初等 bridge（Sylow 共役・coprime、repo 既存）。
6. **採用枠組み（2026-07-25 確定）**: Glauberman の **Z\*-定理**（**Navarro Ch.7 がフル証明** —
   2nd/3rd main theorem の応用）。旧記述「証明はやはり modular か CFSG 要」の modular 側を
   Navarro Ch.1–7 で正面から形式化する。

⚠ 上記 1–4 + 6 は互いに依存する大きな塔だが、**最小 slice は Navarro Ch.1–7 に確定**（2026-07-25）。
章内でも Z\* の証明が実際に使う補題に絞る精査（さらに縮む余地）は着手時に行う。

## 4. 既存 repo 資産（pickup 時に再利用）

- **ordinary char theory**: `GroupTheory/RepresentationTheory/**`（`ClassFunction`・`IrreducibleCharacter`・
  induced character・inner product・`ClassSumCoefficientFormula`・column/row orthogonality・
  `inner_induce_eq_of_isTISubset` TI 等長）— modular の**底**として使える。
- **BS `|S| ≥ 16`**: `GroupTheory/BrauerSuzuki*.lean`（cyclic + 一般化四元数、Lem 1.2–1.9 + endgame、
  axiom-clean、AxiomsCheck 登録）。Q₈ で**再利用可能な純群論部分**（involution 共役類・`⟨involutions⟩`
  正規性・Burnside 2-補群）が既にある。
- **Q₈ sorry の所在**: `Peterfalvi/Appendices/RankOneAffineModel.lean` の
  **`brauerSuzuki_quaternionSylow_q8`**（2026-07-24 に単離: 従来 quaternion 分岐全体を覆っていた
  sorry から `|S| ≥ 16` setup 組み立て + `t = z` を実証明で切り出し、凍結面は「Q₈ Sylow +
  その involution z で `O_{2'}(G) ⊔ C_G(z) = ⊤`」という正確な statement のみになった）。
  消費点 `RankOneHypothesis.brauerSuzuki` → `rankOne_affine_nearField`。
- **前提調査**: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`（Gorenstein Ch.12 原文照合・
  Wong 1972/Mousavi 2020s の bypass 否定・character-free ルート不在の確定）。

## 5. pickup 手順（将来の着手時）

1. 本 note + Q₈ 調査 note を読む → **書籍は Navarro 1998 に確定済（§2、2026-07-25）**。残タスク =
   PDF を references（別 private リポ）に確保して `pdftotext -layout` 抽出 → **Ch.5–7（2nd/3rd main +
   Z\*）を原文で精読**し、Ch.1–4 のうち実際に使う補題に slice を絞る。
2. shared-infra claim（9000 番台）を切る → `RepresentationTheory/Modular/` に p-modular system → Brauer 指標 →
   分解/Cartan → block・Brauer 対応（1st main）→ 2nd/3rd main → **Z\*-定理（Navarro Ch.7）** の順で
   bottom-up。各段 axiom-clean・AxiomsCheck 登録。
3. Z\* → Q₈ bridge（初等）で `brauerSuzuki_quaternionSylow_q8` の `sorry` を置換 →
   `rankOne_affine_nearField` axiom-clean 完成 → Peterfalvi App C Prop 1 の残 sorry ゼロ。
4. ⚠ 行間で詰まったら最強モデル（ChatGPT Pro）で証明再構成（[[feedback-ask-chatgpt-for-elided-gaps]]）。

## 6. 参照

- 追跡 issue: [0147](../../issues/0147-q8-modular-char-theory-frozen.md)（本プロジェクト、2026-07-25 解凍）/
  [9318](../../issues/closed/9318-brauer-suzuki-theorem.md)（closed、|S|≥16 完了）
- Q₈ 前提調査: [`appendixC_prop1_q8_brauer_suzuki.md`](../peterfalvi/appendixC_prop1_q8_brauer_suzuki.md)
- 文献: Brauer–Suzuki 1959（PNAS）/ Suzuki 1962 / Brauer 1964（J.Algebra）/ Dade 1971（Powell–Higman
  *Finite Simple Groups* Ch.VIII）/ Navarro 1998（Cambridge LMS 250）/ Feit 1982（North-Holland）/
  Gorenstein *Finite Groups* Ch.12
- CLAUDE.md「進捗の測り方」（cost/規模は非着手基準・恒久対象外にしない）/
  [[feedback-cost-scope-not-a-criterion]] [[feedback-external-formalization-reference-ok]]
