# Isaacs Ch.1: Sylow Theory — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.1 (pp. 1-44).
形式化先: [`OddOrder/Isaacs/Ch01_Sylow.lean`](../../OddOrder/Isaacs/Ch01_Sylow.lean).

## 全 46 定理の分布 + 進捗

| § | 内容 | Isaacs 番号 | 進捗 |
|---|---|---|---|
| 1A | 群作用と Fundamental Counting Principle | Thm 1.1–1.6 (6 件) | 1.1, 1.2, 1.3, 1.4, 1.5, 1.6 ✅ |
| 1B | Sylow E, Cauchy | Thm 1.7–1.10 (4 件) | 1.7, 1.8, 1.9, 1.10 ✅ |
| 1C | Sylow C / D, Frattini argument | Thm 1.11–1.18 (8 件) | 1.11-1.18 ✅ (全 8/8, 2026-05-21) |
| 1D | 冪零群, Fitting 部分群 `F(G)` | Thm 1.19–1.29 (11 件) | 1.19, 1.20, 1.21, 1.22, 1.23, 1.24(弱形), 1.25, 1.26, 1.27 ✅, opCore + Problem 1B.2 + fitting + fitting.normal ✅, 1.28(a), 1.28(b), 1.29 ✅ (全 11/11 + Fitting) |
| 1E | 小位数群, 指数 2 正規部分群 | Thm 1.30–1.36 (7 件) | 1.30 (前半 + cyclic), 1.31 一般, 1.32, 1.33, 1.34, 1.35, 1.36 ✅ (2026-05-22 全完) |
| 1F | Brodkey (abelian Sylow) | Thm 1.37–1.40 (4 件) | 1.37, 1.38, 1.39, 1.40 ✅ (2026-05-21) |
| 1G | Chermak–Delgado | Thm 1.41–1.46 (6 件) | 1.41, 1.42, 1.43, 1.44 (a)(b)(c), 1.45 (M ∈ L, abelian, Z(G) ≤ M, characteristic), 1.46 ✅ (2026-05-23 完了, 全 6 結果). 実装本体は [`OddOrder/GroupTheory/ChermakDelgado.lean`](../../OddOrder/GroupTheory/ChermakDelgado.lean), helper は [`OddOrder/Mathlib/Subgroup.lean`](../../OddOrder/Mathlib/Subgroup.lean). 計画: [`../meta/ch01_chermak_delgado_plan.md`](../meta/ch01_chermak_delgado_plan.md) |

## mathlib 対応表

CLAUDE.md `## 開発規約 ### mathlib ラッパー方針` に従い, 以下は **本ファイルで
ラッパーを書かず, 呼出側で直接 mathlib 名を使う** (純粋なリネームは禁止). 例外
として `cauchy` と `lt_normalizer_of_isNilpotent_of_lt_top` (Thm 1.22),
`isNilpotent_iff_forall_sylow_normal` / `Sylow.normal_of_isNilpotent` (Thm 1.26) は
**章内 2 回以上の慣用名** として残置.

| Isaacs | 呼び出し方 |
|---|---|
| Thm 1.1   | `H.normalCore_eq_ker` (`Subgroup.normalCore_eq_ker`) を直接呼ぶ |
| Thm 1.4   | `MulAction.orbitEquivQuotientStabilizer` を直接呼ぶ |
| Cor 1.5   | `ConjAct.orbit_eq_carrier_conjClasses` + `MulAction.index_stabilizer` + `Subgroup.centralizer_eq_comap_stabilizer` |
| Cor 1.6   | 同上 (Pointwise locale で `Subgroup G` への conjAct 作用) |
| Thm 1.7   | `Sylow.nonempty` |
| Lemma 1.8 | `Choose.choose_pow_mul_pow_mul_modEq_choose_nat (b := 1)` |
| Cor 1.9   | `cauchy` (慣用名, 中身 `exists_prime_orderOf_dvd_card'`) — Ch.2 ほかで再使用 |
| Lemma 1.10 | typeclass `Subgroup.normal_of_characteristic_of_normal` instance → `inferInstance` |
| Thm 1.11  | `IsPGroup.exists_le_sylow` + `Sylow.orbit_eq_top` |
| Thm 1.12  | `MulAction.exists_smul_eq` (`Sylow.isPretransitive_of_finite`) |
| Lemma 1.13 | `Sylow.normalizer_sup_eq_top'` |
| Thm 1.14  | `IsPGroup.exists_le_sylow` |
| Cor 1.15  | `Sylow.card_eq_index_normalizer` |
| Cor 1.17  | `card_sylow_modEq_one` |
| Lemma 1.18 | `IsPGroup.inf_normalizer_sylow` |
| Thm 1.20  | `isNilpotent_of_finite_tfae.out 0 1` |
| Thm 1.21  | `upperCentralSeries_nilpotencyClass` |
| Thm 1.22  | `lt_normalizer_of_isNilpotent_of_lt_top` (慣用名, 中身 `normalizerCondition_of_isNilpotent`) |
| Cor 1.24 弱 | `Sylow.exists_subgroup_card_pow_prime_of_le_card` |
| Cor 1.25  | `Sylow.exists_subgroup_card_pow_prime` |
| Thm 1.26  | `isNilpotent_iff_forall_sylow_normal` / `Sylow.normal_of_isNilpotent` (慣用名, 中身 `isNilpotent_of_finite_tfae.out 0 3`) |
| Lemma 1.34 | 自前 (`MulAction.toPermHom` + `Equiv.Perm.sign` + `Int.units_eq_one_or` + `Subgroup.index_ker`) — Isaacs 流の独立補題 |
| Thm 1.35  | 自前 (Lemma 1.34 + `cauchy` + `Equiv.Perm.sign_of_pow_two_eq_one`) |

新規実装が必要な主要項目 (mathlib 未収載 — Phase 1 の山場):

* **§1D Def + Thm 1.28** Fitting 部分群 `Fit(G)` — 最大正規冪零部分群.
  全冪零正規部分群の sup として定義し, sup が再び冪零であることを示す.
  Lemma 1.27 (互いに素な位数の正規部分群の積は直積) → Cor 1.28 (F(G) の冪零性).
* **§1E Thm 1.35** `|G|=2n` (n 奇) ⇒ 指数 2 正規部分群.
  → Feit-Thompson の "p=2 の最易 case".  Lemma 1.34 ("奇に作用する元" の存在) + 正則表現を経由.
* **§1G Chermak–Delgado** measure `m_G(H) = |H|·|C_G(H)|` と最大値部分群族 `L(G)`.
  これは Isaacs 独立の話題で BG/Peterfalvi 直依存はない可能性が高い (要確認).
  優先度低めで後回し可.

## 着手順 (実績 + 案)

依存と Phase 1 全体 (Ch.1 → Ch.2 → ... → Ch.9) を考えると:

1. **§1A の Thm 1.1, 1.4** ✅ (2026-05-21, commit `dc21ce9`)
2. **§1B 全て (Thm 1.7, Lemma 1.8, Cor 1.9, Lemma 1.10)** ✅ — mathlib 直ラッパー
3. **§1E Lemma 1.34, Thm 1.35** ✅ — 符号写像 `G → Sym(G) → ℤˣ` 経由で実装
4. **§1A 残り (Cor 1.2, 1.3, 1.5, 1.6)** ← 次の候補. ConjAct 周辺の練習
5. **§1C (Thm 1.11-1.18: Sylow C/D, Frattini)** — mathlib 直 + 小工夫
6. **§1D 前半 (1.19-1.27: 冪零群の基本)** — mathlib `IsNilpotent` と擦り合わせ
7. **§1D Fitting `F(G)` (Def + Cor 1.28, 1.29)** — 本章の主要新規実装. 設計済み ([`ch01_sylow_d_fitting.md`](ch01_sylow_d_fitting.md))
8. **§1E 残り (Thm 1.30-1.33, 1.36)** — 小位数の構造定理
9. **§1F, §1G** — 後回し可 (FT 本筋の必須性が低い)

## 未解決の疑問

* Isaacs § 1F は明示的なセクションヘッダが mmd に無い (1E から 1G の間).
  本では p.31 付近で "1F" の表記がある可能性. 後で PDF 確認.
* §1G Chermak–Delgado は BG/Peterfalvi で参照されているか? 引用が見つからなければ
  Phase 1 から省略可.  → 後で BG/Peterfalvi の mmd を grep "Chermak" で確認.
* `core_G(H)` の Isaacs 表記 vs mathlib `Subgroup.normalCore` の対応は問題なさそう.
  ただし simp 補題が薄いかもしれない (要 lemma 拡充検討).
