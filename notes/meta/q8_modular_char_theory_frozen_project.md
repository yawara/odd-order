# 【凍結・長期プロジェクト】Q₈ Brauer–Suzuki のための modular character theory 整備

> **状態: FROZEN（ユーザー裁定 2026-07-23）**。着手は将来の deliberate な長期プロジェクトとして行う。
> 本 note はその **project spec**（目的・凍結根拠・書籍選定・infra 内訳・pickup 手順）。
> live な lint/形式化 frontier ではない。lane c は本件を primary にしない。

## 0. 一行

Peterfalvi Appendix C Proposition 1（`rankOne_affine_nearField`）に残る唯一の `sorry` =
**Brauer–Suzuki 定理の Q₈（`|S| = 8`）ケース**を閉じるには、mathlib に**皆無**の
**modular character theory（Brauer 指標・p-blocks・分解行列・defect group）を一から整備**する必要がある。
これは 3 冊の残作業とは**別スケールの独立プロジェクト**であり、**書籍選定を含めて**将来行うものとして凍結する。

## 1. なぜ凍結が妥当か（ユーザー裁定 2026-07-23 の根拠）

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

## 2. 書籍選定（本プロジェクトの最初のタスク）

Q₈ BS の証明本体と、その前提となる modular char theory infra は**別々の source**から取るのが自然。
**最終選定は pickup 時に原文を突き合わせて確定する**（下記は候補と判断材料）。

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

**暫定推奨（pickup 時に再検討）**: infra = **Navarro**、証明本体 = **Dade 1971**（または一冊で通すなら **Feit**）。
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
5. **Q₈ 固有部分**: 四元数 Sylow-2 を持つ群の **principal 2-block の構造**、中心 involution が
   "isolated" でないこと（= `G/O(G)` の中心が位数 2）。
6. **代替枠組み**: Glauberman の **Z\*-定理**（BS を一般化、ただし証明はやはり modular か CFSG 要）。
   Z\* 経由が formalization で楽かは pickup 時に評価。

⚠ 上記 3–5 は互いに依存する大きな塔。**Q₈ 単独に必要な最小 slice**（full block 論の全部でなく
principal 2-block + quaternion defect の局所部分だけで足りるか）を pickup 時に精査すると縮小余地あり。

## 4. 既存 repo 資産（pickup 時に再利用）

- **ordinary char theory**: `GroupTheory/RepresentationTheory/**`（`ClassFunction`・`IrreducibleCharacter`・
  induced character・inner product・`ClassSumCoefficientFormula`・column/row orthogonality・
  `inner_induce_eq_of_isTISubset` TI 等長）— modular の**底**として使える。
- **BS `|S| ≥ 16`**: `GroupTheory/BrauerSuzuki*.lean`（cyclic + 一般化四元数、Lem 1.2–1.9 + endgame、
  axiom-clean、AxiomsCheck 登録）。Q₈ で**再利用可能な純群論部分**（involution 共役類・`⟨involutions⟩`
  正規性・Burnside 2-補群）が既にある。
- **Q₈ sorry の所在**: `Peterfalvi/Appendices/RankOneAffineModel.lean` の `RankOneHypothesis.brauerSuzuki`
  内。消費点 `rankOne_affine_nearField`。
- **前提調査**: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`（Gorenstein Ch.12 原文照合・
  Wong 1972/Mousavi 2020s の bypass 否定・character-free ルート不在の確定）。

## 5. pickup 手順（将来の着手時）

1. 本 note + Q₈ 調査 note を読む → 2b の infra source（Navarro 等）と 2a の証明 source（Dade 1971 等）の
   PDF を確保し、**Q₈ の証明を 1 本、原文で精読**して**最小 infra slice を確定**（§3 の縮小）。
2. shared-infra claim（9000 番台）を切る → `RepresentationTheory/Modular/` に p-modular system → Brauer 指標 →
   分解/Cartan → principal block → quaternion defect の順で bottom-up。各段 axiom-clean・AxiomsCheck 登録。
3. Q₈ BS を証明 → `RankOneHypothesis.brauerSuzuki` の Q₈ 分岐の `sorry` を置換 →
   `rankOne_affine_nearField` axiom-clean 完成 → Peterfalvi App C Prop 1 の残 sorry ゼロ。
4. ⚠ 行間で詰まったら最強モデル（ChatGPT Pro）で証明再構成（[[feedback-ask-chatgpt-for-elided-gaps]]）。

## 6. 参照

- 追跡 issue: [9318](../../issues/9318-brauer-suzuki-theorem.md)（|S|≥16 完了 + Q₈ 凍結）/
  凍結 issue（pending、本 note を指す）
- Q₈ 前提調査: [`appendixC_prop1_q8_brauer_suzuki.md`](../peterfalvi/appendixC_prop1_q8_brauer_suzuki.md)
- 文献: Brauer–Suzuki 1959（PNAS）/ Suzuki 1962 / Brauer 1964（J.Algebra）/ Dade 1971（Powell–Higman
  *Finite Simple Groups* Ch.VIII）/ Navarro 1998（Cambridge LMS 250）/ Feit 1982（North-Holland）/
  Gorenstein *Finite Groups* Ch.12
- CLAUDE.md「進捗の測り方」（cost/規模は非着手基準・恒久対象外にしない）/
  [[feedback-cost-scope-not-a-criterion]] [[feedback-external-formalization-reference-ok]]
