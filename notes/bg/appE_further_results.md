# BG App.E: Further Results of Feit and Thompson — mini-roadmap

**スコープ**: BG Appendix E (pp.157-164, mmd L5074-5446), **5 結果 (Thm E.1-Cor E.5)**.
形式化先 (予定): `OddOrder/BG/AppE_FurtherResults.lean` (~400-600 行想定).
ROADMAP 上の位置: **Phase 4 後 (FeitThompson メイン定理完成後の発展材料)**.
役割: **Feit-Thompson 追加成果 (subsequent papers 1963-1991)**; **p-群の lower central series 論 + regular operator 作用下の構造制御**; **BG §1-§16 本体では未使用** (App.E は独立 appendix).

## TL;DR — Phase 4 後の発展・応用材料

**App.E の本質**: 1963 年の Feit-Thompson メイン定理 (奇数位数群は可解) を超えた、その後の追加成果群. 特に **Philip Hall の Lower Central Series** (Thm E.1, Prop E.2) と **Feit-Thompson 1991** (Thm E.3, E.4) による **p-群の regular operator 作用下における精密構造** (exponent, abelianization 階層, サイズ制約). これらは「奇数位数定理の証明内では不要」だが、「証明を簡潔化する」または「さらなる改善」に寄与.

**BG 本文での役割**: ゼロ. App.E は独立 appendix で、§1-§16 のどこからも直接参照されない. 形式化は Phase 4 完成後の **発展教材** または **論文リポジトリの完全性** のため.

---

## App.E 全 5 結果 (詳細表)

| # | 種別 | mmd 行 | 著者 | statement 概要 | 主要仮定 | 結論 | 形式化難度 |
|---|------|--------|------|---------------|----------|------|----------|
| **E.1** | **Thm** | **5084-5094** | **Philip Hall** | Lower central series: ∀x,y∈G, ∃c_r∈G_r: x^n y^n = (xy)^n c_2^{e_2}···c_n^{e_n} (e_r=binomial coeff) | G の lower central series G_1⊇G_2⊇… | 高さ n の commutator 明示公式 | 低 (~50 行) |
| **E.2** | **Prop** | **5096-5119** | **Philip Hall** | p-group R, nilpotence class ≤p-1 ⇒ (a) Ω_1(R) exponent 1 or p, (b) R'⊆Ω_1(R) ⇒ φ(x)=x^p が homomorphism | p odd, R p-群, cl(R)≤p-1 | φ:R→R (x↦x^p) の homomorphism 性 + Ω_1 exponent 制御 | 中 (~100 行, induction) |
| **E.3** | **Thm** | **5123-5314** | **Feit-Thompson (1991)** | p,q distinct odd primes, R p-group, R_0, R_1 nonidentity subgroups, A⊆B operators with \|A\|=q, \|R_0\|=p, R_1 cyclic, C_R(R_0)=R_0×R_1, A fixes R_0 & acts regularly on R ⇒ (a) q\|(p-1)/2, (b) Ω_1(R) exponent p, R_0⊄(Ω_1(R))', \|Ω_1(R)/(Ω_1(R))'\|=p^2, (c) \|Ω_1(R)\|≤p^q, (d) B fixes R_0Φ(Ω_1(R)) ⇒ B fixes R_0 | q\|(p-1), A regular, p≥7 | p-群 R の層状 exponent/abelianization/size の精密特徴づけ | **大** (~400+ 行, 4 Step x proof) |
| **E.4** | **Prop** | **5316-5388** | **Feit-Thompson (1991)** | Setup of E.3 + \|S\|≥p^4 (S=Ω_1(R)), B acts regularly, B ∄ fix R_0 ⇒ C_S(Z_2(S)) abelian, index p in S | E.3 の状況 + size bound | C_S(Z_2(S)) が abelian かつ指数 p (abelianization の higher-level 構造) | **大** (~200 行, embedding into E.3) |
| **Cor E.5** | **Cor** | **5390-5445** | **Feit-Thompson** | Maximal subgroup M, x∈M_σ prime order p, C_G(x)⊄M, N∈M(C_G(x)) ⇒ [condition on M, Ω_1(O_p(M))] ⇒ all maximal subgroups Type I or II | N∉M_F, (i) \|M/M'\| prime or (ii) Ω_1(O_p(M)) ∄ normal abelian index p | maximal subgroup classification (Thm 14.7 等との結合) | **大** (~250 行, BG Thm 14.7 への implicit 参照) |

---

## Feit-Thompson 追加結果の内容

### 1. Philip Hall の Lower Central Series (Thm E.1, Prop E.2)

**来歴**: Philip Hall, 1950s-1960s. "commutator collecting process" として知られる.

**Thm E.1 の意義**:
- **binomial coefficient を used as commutator weight**: x^n y^n を (xy)^n に「変換」する際、commutator が明示的に出現. 
- **Application to p-groups**: p-group の lower central series 長さ推定に活用 (Thm E.3 proof の Step 2 で使用).
- **Lean 形式化**: binomial coefficient の定義 + lower central series API ⇒ induction on n.

**Prop E.2 の意義**:
- **exponent p の p-group で φ(x)=x^p が homomorphism になる条件**: nilpotence class ≤p-1 ⇒ (a) Ω_1(R) の exponent 制御, (b) R'⊆Ω_1(R) ⇒ homomorphism.
- **Step 2 (Prop E.2 の対偶)**: \|R\|≥p^4 かつ exponent p なら、R は「非常に制約された構造」を持つ ⇒ Thm E.3 Step 2 での size bound p^q に接続.

### 2. Feit-Thompson 1991 (Thm E.3, E.4)

**来歴**: Feit-Thompson 1963 (奇数位数定理本体) とは別の 1991 年の論文. 「奇数位数定理の証明を簡潔化する」ための **追加成果**.

**Thm E.3 の構造**:
- **Regular operator 作用 A の制御**: \|A\|=q (odd prime), A が R_0 を fix + R 上で regularly act.
- **結論 (a)-(d) の hierarchy**:
  - **(a)** q \| (p-1)/2 — A の order が p-1 の divisor を divide.
  - **(b)** Ω_1(R) が exponent p + abelianization \|Ω_1(R)/(Ω_1(R))'\| = p^2 — **elementary abelian structure**.
  - **(c)** \|Ω_1(R)\| ≤ p^q — **size bound**: q の order により p-群のサイズが指数的に制限.
  - **(d)** B が R_0Φ(Ω_1(R)) を fix ⇒ B が R_0 を fix — **Frattini-like argument**: derived series の一層上で control ⇒ 元の層での control.

**Thm E.4 の構造**:
- **C_S(Z_2(S)) abelian + index p**: S = Ω_1(R), Z_2(S) = upper central series second term.
- **高さ 2 の中心化子が abelian になる** ⇒ S 自体の 2-stage abelianization が「rank 1 に接近」.
- **用途**: Thm E.3 の size estimate p^q がより tight になる; 「B が regularly act しるなら、B の order q は p よりはるかに小さい」という制約をさらに明確化.

### 3. Corollary E.5 の役割

**BG §14-§16 との接続**:
- **背景**: BG Thm 14.7 (maximal subgroup 分類: Type I, Type II) が主結果. Cor E.5 はこれを「特定の M, x, N の状況」で再述.
- **結論**: M/M' が cyclic (prime order) なら、すべての maximal subgroup が Type I or II になる.
- **技巧**: Theorem E.3 の size constraint + E.4 の abelianization control を合成して、maximal subgroup の「混在不可能性」を導出.

---

## Phase 4 メイン結合との関係

**Feit-Thompson メイン定理（奇数位数群は可解）** を 3 段階で分解：

```
[Stage 1] BG §1-§5: 基礎 (maximal subgroup, p-stability, solvable reduction)
            ↓
[Stage 2] BG §6-§9: 特異点の消滅 (uniqueness, Z(J(P)) normal)
            ↓
[Stage 3] BG §10-§16: Maximal subgroup 全面分類 + 矛盾導出
                      (Thm 14.7 Type I/II, §16 Main Results)
```

**App.E の位置**:
- **時間的**: Stage 3 終了後（Phase 4 完成後）.
- **論理的**: **App.E は§1-§16 の証明に含まれない**. 代わり、「もし E.3, E.4 の p-群構造制御を使えば、Stage 2 または Stage 3 の特定箇所をより簡潔化できる」という potential.
- **数学的例**: Cor E.5 は Stage 3 の maximal subgroup Type 分類を「shortcut」できることを示唆. ただし BG 本体では使わず.

---

## BG 本書での被引用

**完全リスト: ゼロ**. App.E は:
- BG §1-§16 どこからも参照されない
- BG App.A, B, C, D からも参照されない
- **App.E は独立 appendix として「参考資料」の扱い**

**理由**:
1. App.E (Feit-Thompson 1991 + Philip Hall) は奇数位数定理の本来の 1963 証明に **含まれない**.
2. BG の目標は 1963 定理の完全形式化であり、App.E は「その後の改善・応用」.
3. Cor E.5 は BG §14-§16 の maximal subgroup 分類と同様の結論に到達するが、BG 著者は §14-§16 の元々の論証を採用.

---

## mathlib カバレッジ (完全新規)

| 結果 | mathlib 既存 | BG §1-§16 from | App.E 新規部分 | 必要な定義/補題 |
|------|-------------|----------------|----------------|----------------|
| **E.1** | Lower central series (partial) | Thm 7.5, 7.6 ケース分析 | **Binomial coefficient を commutator weight として使用** | `LowerCentralSeries`, `Nat.choose` |
| **E.2** | Ω_1 exponent (Sylow p subgroup module theory) | Thm 5.3, 5.5, 6.2 | **Nilpotence class ≤p-1 下での φ(x)=x^p の homomorphism 性** | `Subgroup.Omega_one`, `nilpotencyClass` (要定義) |
| **E.3** | Regular operators (Aut theory, SCN) | Thm 5.5 (narrow p-groups) | **size bound \|Ω_1(R)\|≤p^q の全証明 + 4-Step structure** | `RegularAction`, `OperatorGroup`, SCN (socle construction) |
| **E.4** | Central subgroups (Z_2, higher center) | Z(P), Z_2(P) 定義 | **C_S(Z_2(S)) abelian + index p の full proof** | `Subgroup.center`, `upperCentralSeries` |
| **Cor E.5** | Maximal subgroup type (Type I/II classification) | Thm 14.7, 15.8, 15.9 | **Cor E.5 の E.3, E.4 への reduction + Type classification の結合** | `MaximalSubgroup.Type`, Frattini argument |

**総量**: ~600-800 行の新規 Lean 証明. うち:
- **Thm E.1**: ~50 行 (binomial + induction)
- **Prop E.2**: ~100 行 (2-step, nilpotence class 制約)
- **Thm E.3**: ~400 行 (4-Step, size bound, regular action 制御)
- **Thm E.4**: ~200 行 (embedding into E.3 proof, higher center)
- **Cor E.5**: ~250 行 (BG Thm 14.7, 15.8, 15.9 との結合)

---

## Phase 2 形式化着手順 (skip 推奨)

**推奨**: **Phase 2a では App.E 着手不要**.

**理由**:
1. App.E は BG §1-§16 に含まれず、Phase 4 (FeitThompson メイン定理完成) の前提ではない.
2. Thm E.1, E.2 は Hall の古い結果 (1950s), Thm E.3-Cor E.5 は 1991 追加成果 ⇒ **BG メイン証明の external supplement**.
3. Phase 4 後で「時間に余裕がある場合」の着手が妥当.

**早期着手が有用な場合**:
- Feit-Thompson subsequent papers を complete coverage する場合
- App.E が Phase 3 (Peterfalvi §1-§16 character theory 翻訳) で活用される場合 ⇒ ただし現在予定されていない

**実装方針（Phase 4 後）**:
| 段階 | 結果 | 行数 | 時間 | 前提 |
|------|------|------|------|------|
| 第 1 | E.1, E.2 | ~150 | 2-3 日 | BG §5 (lower central series, Ω_1) |
| 第 2 | E.3 Step 1-2 | ~200 | 3-4 日 | BG §5 (SCN, narrow p-groups), Thm 5.3, 5.5 |
| 第 3 | E.3 Step 3-4 | ~200 | 3-4 日 | E.3 Step 1-2 + Thm 5.2, 5.3 |
| 第 4 | E.4 | ~200 | 2-3 日 | E.3 全体 + upper central series API |
| 第 5 | Cor E.5 | ~250 | 3-4 日 | BG Thm 14.7, 15.8, 15.9 + E.3, E.4 |
| **合計** | **E.1-E.5** | **~1000** | **~13-18 日** | **Phase 4 完成後** |

---

## CLAUDE.md `feedback_no_mathlib_wrapper` との整合

- **E.1**: Hall の古典結果 + binomial commutator → 新規形式化 (wrapper 不可)
- **E.2**: Nilpotence class 制約下の Ω_1 exponent → 新規形式化 (Hall 理論の application)
- **E.3-E.4**: Feit-Thompson 1991 → **完全新規** (subsequent paper, mathlib に未実装)
- **Cor E.5**: Type I/II classification の E.3, E.4 への reduction → **新規形式化** (BG Thm 14.7 とは independent proof path)

**特徴**: App.E 全体が「mathlib にない」+ 「BG §1-§16 メイン証明に含まれない」 → **形式化の優先度は低いが、完全性・historical record として価値あり**.

---

## 関連する BG 部分

| App.E 결과 | 참考 BG 箇所 | 연결점 |
|---------|---------|---------|
| **E.1, E.2** | §5 Lower Central, §7 Fitting, Thm 5.3, 5.5 | φ(x)=x^p の homomorphism 性、narrow p-groups の characterization |
| **E.3** | §5 SCN/narrow, Thm 5.2, 5.3, 5.5 | Regular operator 作用下の p-群 size bound (§5 の上位互換) |
| **E.4** | §5 Upper central, §6-§9 Uniqueness | Z_2(S) の abelianization, higher center structure |
| **Cor E.5** | **§14 Thm 14.7, §15 Thm 15.8/15.9, §16 Main Results** | **Maximal subgroup Type I/II classification の alternative proof** |

---

## 未解決 / TODO

1. **E.3 の 4-Step proof の Lean 実装戦略**: Step 1 (簡単) vs Step 2 (hard, size bound derivation) vs Step 3 (intermediate) vs Step 4 (Frattini argument). 証明の粒度とコード分割の最適化.

2. **Regular operator のモジュール化**: `RegularAction` 定義が Lean に存在するか確認. 存在しなければ `OperatorGroup` から define + API 整備.

3. **SCN (socle construction) の formal definition**: BG §5 で informal に使用. App.E Step 2 では `V ∈ SCN(S)` を技巧的に活用. Lean での formalization level の決定.

4. **Size bound \|Ω_1(R)\| ≤ p^q の modular arithmetic**: 順序 q の cyclic group で exponent structure を制御する際の「rank argument」(E.3 Step 2 L5228-5232) を Lean で清潔に実装.

5. **Cor E.5 の Type I/II classification との統合**: BG Thm 14.7 (主定理) vs Cor E.5 (App.E 증명). どちらを形式化の「canonical」とするか. 推奨は BG Thm 14.7 (本体), Cor E.5 は lemma.

6. **Philip Hall reference [26]**: Cite: "Philip Hall, p-Groups", Handbook entry or original papers. BG では pp.37-41 引用. Lean 자동 증명에서 Hall's theory 명시 reference 필요여부.

---

**作成**: 2026-05-22.
**出典**: `/Users/ywr/odd-order/references/bg/local-analysis.mmd` L5074-5446 (App.E full text, mmd format).
**参考資料**: `notes/bg/_overview.md`, `notes/bg/appA_pstability.md`, `references/bg/local-analysis.mmd` §1-§16, Feit-Thompson (1963), Feit-Thompson (1991 subsequent), Philip Hall classical works.
**関連スコープ**: Phase 4 FeitThompson メイン定理 (BG §1-§16), App.E は独立 external supplement.
