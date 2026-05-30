# BG Thm 1.13 (Thompson critical subgroup) 実装設計 — issue 0016 (2026-05-30)

> **生成**: `bg-thm113-design` workflow (run wf_000d0ff2-91b, 6 agent / 469k tok / 8.8 min)。BG mmd / Gorenstein / Isaacs / repo API / mathlib API を並列調査 + ソース直接検証 → 統合設計。
> **ルート**: Gorenstein 原文 (Isaacs に critical subgroup 定理は無い)。`references/gorenstein/finite-groups.mmd` L3878-3945 に証明全文 (Lemma 5.3.9 / Thm 5.3.10 / 5.3.11+5.3.12 / 5.3.13)。
> 着手判断: 本セッション (parallel_execution_plan の W-3)。実装は full port 前提、5 stage。

# 0016 実装設計: BG Thm 1.13 (Thompson critical subgroup)

調査 5 本を統合し、ソースで全 load-bearing 事実を直接検証した上での実装設計。検証で判明した重要な訂正・簡略化を本文に反映済み。

---

## 0. 検証で確定した事実 (調査結果の訂正含む)

- **Gorenstein mmd は完全**: `references/gorenstein/finite-groups.mmd` L3878-3945 に Lemma 5.3.9 / Thm 5.3.10 / **Thm 5.3.11 (証明全文 + 埋め込み Lemma 5.3.12)** / Thm 5.3.13 が verbatim で存在。PDF 不要。調査が「未読」とした証明本体を確認済 (下に要点引用)。番号は mmd 章相対 ("Theorem 3.11" = 教科書 5.3.11)。
- **`Omega` の正しいシグネチャは `Omega G p n`** (`OmegaSubgroup.lean:58`, `G` は explicit, `p n` の前)。よって `Ω₁(C)` = `Omega (↥C) p 1`。複数調査が `Omega p n G` と誤記。
- **characteristic 推移律は mathlib に無い** (grep 確認、空)。ただし後述の通り **0016 では推移律を自作する必要はない** — `IsAInvariant.map_subtype_of_characteristic` (Ch04 L2229) が "K char C ∧ C A-不変 ⇒ K.map C.subtype A-不変" を既に与えるので、Ω₁(C) を `IsAInvariant` 枠で直接扱える。これは調査が「最大 GAP の一つ」とした項目の解消。
- **`isaacs_thm_4_36` 実シグネチャ確認** (Ch04 L4173): `h_fix : ∀ g, g^p=1 → ∀ a, (φ a) g = g` (全位数 p 元を固定) ⇒ `actionCommutator φ = ⊥`。`[Finite A] [Finite G] [Fact p.Prime] (hp_odd : p ≠ 2) (hA_p' : ¬ p ∣ Nat.card A)`。これは Gorenstein Thm 5.3.10 (p 奇, Ω₁ で自明な p'-auto ⇒ 自明) の Lean 化に**ほぼ等価**で、性質 (d) のエンジン。
- **OmegaSubgroup 消費者は `Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean` のみ** (+ S7B2 が `Omega` 文字列言及)。Ch07 が active frontier なので worktree 衝突対象 (§7 参照)。
- issue 0016 / `S01_Solvable.lean:15,69` の「§13 で参照」は**誤り**。実 grep の下流利用は **§3 (L1095), §4 Lem4.17 (L1712), §5 Thm5.5 (L1887), §12 (L3468)** の 4 箇所。issue 文面も修正対象。
- **Isaacs に critical subgroup 定理は無い** (3 調査が独立に確認)。`phase2_cross_refs.md:124` の「Isaacs Thm 1.13 = 4.31」は stale 誤記 (Isaacs 1.13 = Frattini Argument, 4.31 = P×Q lemma)。

---

## 1. 確定 statement

### 1.1 critical subgroup の定義 (Gorenstein 5.3.11 の条件 = 定義)

Gorenstein は「Thm 5.3.11 の (i)(ii)(iii) を満たす characteristic subgroup を critical と呼ぶ」(mmd L3936)。条件は (verbatim L3907-3911):

- (i) `cl(C) ≤ 2` かつ `C/Z(C)` elementary abelian
- (ii) `[P, C] ⊆ Z(C)`
- (iii) `C_P(C) = Z(C)` (self-centralizing)
- (iv) [(iii) から導出される派生性質] 全 nontrivial p'-automorphism が C に nontrivial に作用

Lean predicate (構造でなく Prop。理由は §3):

```lean
/-- **Gorenstein Thm 5.3.11** の条件を満たす部分群 = `P` の critical subgroup.
`P` 全体に対する性質なので `C : Subgroup G` を `G = P` で扱う. -/
def IsCritical {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  C.Characteristic
    ∧ _root_.commutator C ≤ Subgroup.center C                      -- (i-a) cl(C) ≤ 2
    ∧ (Subgroup.center C).Subgroup.IsElementaryAbelian_quotient    -- (i-b) C/Z(C) elem.ab (※下記)
    ∧ ⁅(⊤ : Subgroup G), C⁆ ≤ Subgroup.center C |>.map C.subtype   -- (ii) [P,C] ⊆ Z(C)
    ∧ Subgroup.centralizer (C : Set G) = (Subgroup.center C).map C.subtype  -- (iii)
```

正確な (i-b)/(ii)/(iii) の Lean 表記には設計上の注意がある (`center ↥C` は `Subgroup ↥C`、ambient と混ざる)。**推奨は repo 既定の class≤2 idiom `_root_.commutator (↥C) ≤ Subgroup.center (↥C)` を中核に置き、(ii)(iii) は ambient `G` 側で `Subgroup.centralizer (↑C)` と `(center ↥C).map C.subtype` を使う**。(i-b) elementary abelian は (i-a) + `C'` が p-elementary から `isElementaryAbelian_quotient_center_of_class_le_two` (Ch04 L255) で**導出可能**なので、def に入れず補題化する方がクリーン (下流が実際に使うのは exponent-p 版 D の方なので、5.3.11 の C は中間生成物で十分)。

### 1.2 critical subgroup の存在 (Gorenstein 5.3.11 本体)

```lean
theorem isCritical_exists {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    ∃ C : Subgroup G, IsCritical C
```
全 p で成立 (奇数不要)。`Nontrivial G` は不要 (`G = 1` なら `C = ⊥` が自明に satisfy する; ただし下流で非自明性が要るなら付与)。

### 1.3 (iii) ⇒ (iv) 派生 (faithful action)

(iv) は Aut(P) を量化するので**独立補題**が最も綺麗 (調査の合意):

```lean
/-- **Gorenstein 5.3.11 (iii)⇒(iv)**: critical (より弱く self-centralizing characteristic) C に
自明に作用する p'-automorphism は trivial. three-subgroup lemma + stability で. -/
theorem IsCritical.faithful_on_p' {G : Type*} [Group G] [Finite G]
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    {C : Subgroup G} (hC : IsCritical C)
    (h_triv : ∀ a, OddOrder.Isaacs.Ch03.IsAInvariant.restrict ... ) :  -- A acts trivially on C
    actionCommutator φ = ⊥
```
(正確な「A が C に自明作用」の述語は `restrictAction (IsAInvariant.of_characteristic φ) = 1` 等で書く。)

### 1.4 BG Thm 1.13 = Gorenstein 5.3.13 (odd p, H = Ω₁(C))

BG-facing の最終形 (S01 §1D に載る本体):

```lean
/-- **BG Theorem 1.13** (J. G. Thompson) — `references/bg/local-analysis.mmd:461`.
**Gorenstein Finite Groups Thm 5.3.13** (p.186) の Lean 化. `p` 奇素数, `G` 非自明 p-群 ⇒
characteristic subgroup `H` (= Ω₁ of a critical subgroup) が存在し四性質を持つ. -/
theorem thompson_critical_omega {G : Type*} [Group G] [Finite G] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) (hG : IsPGroup p G) :
    ∃ H : Subgroup G,
      H.Characteristic                                              -- characteristic
      ∧ ⁅H, (⊤ : Subgroup G)⁆ ≤ (Subgroup.center H).map H.subtype   -- (a) [H,G] ⊆ Z(H)
      ∧ _root_.commutator H ≤ Subgroup.center H                     -- (b) cl(H) ≤ 2
      ∧ Monoid.exponent H = p                                       -- (c) exponent p
      ∧ ∀ (A : Type) [Group A] [Finite A] (φ : A →* MulAut G),      -- (d) C_{Aut G}(H) は p-群
          (∀ a, IsAInvariant φ H → ...) → ¬ p ∣ Nat.card A → (acts trivially on H → trivial)
```

性質 (d) の Lean 表現は §1.6 で確定する (universe-polymorphic な `∀ A` 量化は扱いにくいので、**`Subgroup (MulAut G)` 版**を推奨)。

---

## 2. ルート決定: **Gorenstein 原文ルート (Isaacs 読み替え不可)**

CLAUDE.md 方針 = 「Isaacs に対応があれば優先、無ければ Gorenstein」。**3 つの独立調査が Isaacs に critical subgroup 定理が無いことを確認**:

- Isaacs FGT 全文 grep で "critical subgroup" は定義語でなく口語 ("critical characteristic subgroup" = Z(P), J(P) を指す慣用句) 1 件のみ。索引エントリ無し。
- 最も近い Isaacs 結果 = **Problem 4B.2** (演習、証明本文なし、nilpotent G の self-centralizing class≤2 char subgroup) だが exponent p / C_Aut p-群を欠き critical の代替不可。Thm 4.31 (P×Q lemma)・Thm 4.36 (= BG 1.11) はいずれも別物。

→ **本件は CLAUDE.md が明示する例外「Isaacs が欠く (ZJ/p-stability 周り) のみ Gorenstein 参照」に該当**。critical subgroup は Gorenstein Ch.5 §3 (`finite-groups.mmd` L3878-3945) を直接 Lean 化する。BG notation 維持のため Isaacs 4.31 ラッパーを書くのは誤り (issue にこの訂正を含める)。

ただし**証明の部品 (commutator API, class≤2 構造補題, Ω₁ exponent, faithful action) は既存 Isaacs Ch03/Ch04 + repo shared module で大半が揃う** (§4)。Gorenstein からポートするのは「critical の存在の two-case 構成」と「Ω₁ exponent p」の中核論証のみ。

---

## 3. 新規 shared module 設計: `OddOrder/GroupTheory/CriticalSubgroup.lean`

**predicate (`IsCritical : Subgroup G → Prop`) を採用** (構造でなく)。理由:

- mathlib 互換 (mathlib は `IsPGroup`, `IsNilpotent`, `IsElementaryAbelian` 等すべて Prop / `def ... : Prop`)。`IsSCN` (`SCN.lean`) も structure だが repo 内で predicate 化の流れ。
- no-wrapper 方針: 条件 (i)(ii)(iii) はすべて既存 mathlib/repo 述語の合成で、新規フィールドを持つ構造にする価値がない。
- 存在定理が `∃ C, IsCritical C` の形で自然。

新規 module の理由 (Ch04/S01 内でなく独立ファイル): (1) §4/§5 BG で再利用、(2) Ch07 (active) と OmegaSubgroup を共有するので import 階層を浅く保つ、(3) ~300-450 行になり Ch04 (既に巨大) を膨らませない。`SCN.lean` / `OmegaSubgroup.lean` と同階層。

シグネチャ案 (命名は記述的、番号なし):

```lean
namespace OddOrder.GroupTheory

def IsCritical {G : Type*} [Group G] (C : Subgroup G) : Prop := ...      -- §1.1

theorem IsCritical.characteristic   ...    -- 射影
theorem IsCritical.commutator_le_center ...  -- [P,C] ⊆ Z(C)  (ii)
theorem IsCritical.centralizer_eq   ...    -- C_P(C) = Z(C)  (iii)
theorem IsCritical.nilpotencyClass_le_two ... -- (i-a) → repo idiom
theorem isCritical_exists [Finite G] (hG : IsPGroup p G) : ∃ C, IsCritical C  -- 5.3.11 本体

-- 派生 (faithful)
theorem IsCritical.p'_aut_trivial ...      -- (iii)⇒(iv)

-- Ω₁ 版 (5.3.13)
theorem IsCritical.omega1_isElementaryExponent  -- D = Ω₁(C) exponent p (odd)
end OddOrder.GroupTheory
```

`Subgroup.centralizer` の characteristic は mathlib `Subgroup.characteristic_centralizer` (`Centralizer.lean:90`) 既存。

---

## 4. 補題分解 (sorry-free 化の段階)

Gorenstein 証明をそのまま段階化。各段の難所と既存 API 対応:

| # | 段 | Gorenstein | 難所 | 既存 API / 対応 |
|---|---|---|---|---|
| **S1** | `Lemma 5.3.12`: maximal abelian normal `M` ⇒ `C_P(M)=M` | L3921-3926 | quotient `P/M`, 「正規部分群が中心と交わる」, cyclic-over-center ⇒ abelian | mathlib `IsPGroup` の中心交差 (`IsPGroup.center_nontrivial`/`exists_subgroup_le_center_card_prime` `ElementaryAbelian.lean:378`), `commutator_eq_bot_iff_center_eq_top` |
| **S2** | `Thm 5.3.11` existence (two-case) | L3928-3934 | **最難**。Case2: `P/D₀` に落とし `Ω₁(Z(P̄))` と交わる。pullback が char | S1 + `Subgroup.Characteristic.comap_quotient_mk` (`QuotientGroup/Basic.lean:395`) + `MulEquiv.subgroupMap`。`Ω₁(Z(P̄))` = `Omega (↥(center (G⧸D₀))) p 1` だが「abelian なので set 形」→ `omega1OfAbelian` 使用可 (center は可換) |
| **S3** | (iii)⇒(iv) faithful | L3915-3917 | three-subgroup lemma + stability (p'-auto が normal series 安定 ⇒ trivial) | three-subgroups: mathlib `commutator_commutator_eq_bot_of_rotate` (`Commutator/Basic.lean:109`) + Ch04 Cor 4.10 (L1535)。**stability の Lean 化が要 (Gorenstein Thm 5.3.2)** — repo に専用補題があるか要確認 (GAP 候補) |
| **S4** | `D = Ω₁(C)` の A-不変/char | L3942 | char-in-char | **`IsAInvariant.map_subtype_of_characteristic` (Ch04 L2229) で解決** (推移律自作不要)。Ω₁(C) が C で characteristic は別途要 (§5) |
| **S5** | (b) `cl(D) ≤ 2` | L3942 "Clearly" | C から継承 (`D ⊆ C`) | `_root_.commutator` の `commutator_mono` + `Subgroup.center` 単調性。`D ≤ C` から機械的 |
| **S6** | (c) `exp(D)=p` (odd) | `Lemma 5.3.9(i)` L3878 | **非自明**。非可換 class≤2 で `(xy)^p=1`。Gorenstein 証明: `(xy)^p = z^{p(p-1)/2}·x^p·y^p`, `z=[y,x]∈Z`, p 奇で `z^{p(p-1)/2}=1` | Ch04 `pow_mem_center_of_class_le_two_of_commutator_pow` (L240) が `x^n∈Z` を与える。Hall-Petrescu/Lemma 2.2.2 の `(xy)^i = z^{i(i-1)/2} x^i y^i` は **新規** (Ch04 §4D Baer trick 基盤あり)。`Monoid.exponent_eq_prime_iff` (`Exponent.lean:302`) で仕上げ |
| **S7** | (d) `C_Aut(H)` p-群 | `Thm 5.3.10` 経由 | p'-part が H=Ω₁ を固定 ⇒ 自明 | **`isaacs_thm_4_36` (Ch04 L4173) がほぼそのままエンジン** (`h_fix` = 全位数 p 元固定 = Ω₁ 固定)。Schur-Zassenhaus 系で p'-part 抽出 (`OddOrder/Mathlib/SchurZassenhausConj.lean`) |
| **S8** | (a) `[H,G]⊆Z(H)` | BG L468 (BG 自前) | 3 段包含 | `commutator_mono` + `commutator_le_right` + S5 の `D≤C` + (ii)。BG 証明 `⁅⊤,Ω₁(C)⁆ ⊆ ⁅⊤,C⁆∩H ⊆ Z(C)∩H ⊆ Z(H)` をそのまま |

**最重 = S2 (two-case 構成) と S6 (exponent p の `(xy)^p` 恒等式)**。S7 は既存資産で最も綺麗に通る (調査一致)。

---

## 5. 新規に建てる補助補題/API (repo/mathlib に無いもの)

honest gap list (誇張なし):

1. **`(xy)^i = [y,x]^{i(i-1)/2} · x^i · y^i` for class≤2** (Gorenstein Lemma 2.2.2 / Hall-Petrescu の class-2 特殊化)。mathlib に無い。Ch04 §4D の `BaerMul` / commutator API で組むが**専用補題が新規**。S6 の核。~40-80 行。

2. **stability theorem** (Gorenstein Thm 5.3.2: p'-group が `P ⊇ N ⊇ 1` を安定化 ⇒ trivial)。S3 で要。**repo に既にあるか未確定** (GAP)。`isaacs_thm_4_36` の証明内部で類似論証を使っている可能性が高いので、まず Ch04 内を探索 → 無ければ新規 (~30-50 行)。

3. **`Omega (↥C) p 1` が C で characteristic** (= `Subgroup.IsElementaryAbelian` 不要、closure 形の char)。OmegaSubgroup.lean は現状 `def + mono` のみで characteristic 未証明。`Omega` は「全自己同型が generator set `{g | g^(p^n)=1}` を保つ」から characteristic — これは**汎用に証明でき OmegaSubgroup.lean に追加すべき** (§7 worktree 注意):
   ```lean
   instance Omega.characteristic {G} [Group G] {p n : ℕ} : (Omega G p n).Characteristic
   ```
   `Subgroup.characteristic_iff_map_eq` + `closure_map` で `{g|g^(p^n)=1}` が `e : G≃*G` で保たれる (`(e g)^(p^n) = e (g^(p^n)) = e 1 = 1`)。**これさえ入れれば S4 は `map_subtype_of_characteristic` 経由で即閉じる** (推移律不要)。~15-25 行。

4. **性質 (d) の最終形定式化**。推奨 = `Subgroup (MulAut G)` で `C_{Aut G}(H) := { ψ : MulAut G | ∀ h ∈ H, ψ h = h }` (= restriction `MulAut G →* MulAut ↥H` の kernel) が `IsPGroup p`。`MulAut G →* MulAut ↥H` の morphism 自体が mathlib に無い (要 `H char G`、`MulEquiv.subgroupMap` から組む)。新規 ~30 行。`fixedPointsOfMulAut` (`OddOrder/Mathlib/Subgroup.lean:149`) の双対パターン流用。

**`omega1OfAbelian` (abelian 専用) は S2 の `Ω₁(Z(P̄))` (中心は可換) には使えるが、最終 H=Ω₁(C) (C は非可換 class≤2) には使えない** — closure 形 `Omega (↥C) p 1` が正しく、その exponent p (S6) と char (#3) が新規作業の本体。

---

## 6. BG-facing theorem の形 (S01_Solvable.lean §1D)

- 現状 §1D は **`/-! ## §1D: 未実装 (Phase 1 Ch.4 §4D 待ち) -/` のプレースホルダ** (L819) と、mapping-table L50-51 の行のみ。実 theorem は無い。
- **載せ方**: `thompson_critical_omega` (§1.4) を S01 §1D に置く。証明本体は `CriticalSubgroup.lean` の `isCritical_exists` + `IsCritical.omega1_*` + `isaacs_thm_4_36` を呼ぶ薄い組み立て (no-wrapper には抵触しない: 引数・型を変えた合成定理であり純粋リネームではない)。
- mapping-table L50-51 を `✅ sorry-free` に更新。`Thm 1.11` 行 (L50) は 0015 (別 issue) が触るので**編集衝突注意** (調査指摘) — §1D docstring ブロックは 0015 と共有。0016 worktree では L51 (`Thm 1.13`) 行のみ触る。
- issue 0016 (L15) と `notes/bg/s01_solvable.md:77` の「§13 参照」誤記、`phase2_cross_refs.md:124` の「Isaacs 1.13 = 4.31」誤記を本 issue で訂正 (独立 commit)。

**§4 (Blackburn rank theory) の消費形** (mmd L1712 Lem 4.17, L1887 Thm 5.5):

- §4 Lem 4.17 / §5 Thm 5.5 は外部作用群 `A`(`φ : A →* MulAut G` の形)が R に作用する文脈で「Thm 1.13 の H を取り、`C_A(H)` が p-群 ⇒ A の構造制御」を使う。つまり**消費側は §1.4 の (d) を `φ : A →* MulAut G` 版で欲しがる**。
- よって (d) を `Subgroup (MulAut G)` 版 (§5 #4) で証明しつつ、**§4 が使いやすいよう `φ : A →* MulAut G` で「A が H を固定 ⇒ p ∣ |A| でなければ A は G に自明作用」系として再パッケージする補題**も `CriticalSubgroup.lean` に併設すると下流が滑らか (これは `isaacs_thm_4_36` の H=Ω₁(C) 特殊化なので自然)。§3/§12 は characteristic + exponent のみ消費なので (a)(b) 抜きでも開通。

---

## 7. 工数見積 + worktree 計画

### LOC / 補題内訳 (XL)

| 段 | 新規 LOC | 補題数 | 難度 |
|---|---|---|---|
| `IsCritical` def + 射影 | 40-60 | 5-6 | 低 |
| S1 (Lemma 5.3.12) | 50-80 | 1-2 | 中 |
| S2 (5.3.11 existence two-case) | **150-250** | 1 (+補助 3-4) | **高** |
| S3 (iii)⇒(iv) + stability (#2) | 60-100 | 2-3 | 中-高 |
| S4 (Ω₁ A-不変) + Omega char (#3) | 25-40 | 2 | 低 (橋既存) |
| S5 (cl(D)≤2) | 20-30 | 1 | 低 |
| S6 (exp(D)=p) + (xy)^p 恒等式 (#1) | **80-130** | 2-3 | **高** |
| S7 (d) C_Aut p-群 + (#4) | 60-100 | 2-3 | 中 (4.36 既存) |
| S8 (a) [H,G]⊆Z(H) | 20-30 | 1 | 低 |
| BG-facing 組み立て + §4 用 repackage | 30-50 | 2 | 低 |
| **合計** | **~535-870 LOC** | **~20-26 補題** | — |

**XL の根拠**: 実 sorry-free 化のボトルネックは S2 (Gorenstein two-case 構成、quotient 往復) と S6 (class-2 の `(xy)^p` 恒等式、mathlib 不在)。残りは既存 `IsAInvariant`/`isaacs_thm_4_36`/commutator API で機械的。「scaffold = sorry-free だが未証明」の罠 (memory) を避けるため、S2/S6 を hypothesis に逃がす conditional は**避け、真に証明する**前提。ただし時間制約があれば「`IsCritical C` を仮定する conditional Thm 1.13 を先に S01 に置き S2/S6 を別 sub-issue」も退路 (調査の現実案、ただし doneness は仮説の constructibility で判定)。

### worktree 計画

- **slug = `bg-thm113-critical`** (branch 同名)。path `/Users/ywr/odd-order-bg-thm113-critical` (CLAUDE.md は `/Users/...` だが env は `/home/ywr` — 実 path は `/home/ywr/odd-order-bg-thm113-critical`、worktree_setup.md に従う)。`ODD_ISSUE_BASE=2000` レンジ (main 以外の並行)。
- **Ch07 衝突回避が最重要**: `OmegaSubgroup.lean` を **Ch07 (active frontier, S7A1 が import) と共有**。本 issue の #3 (`Omega.characteristic` instance 追加) は OmegaSubgroup.lean を編集するので、Ch07 worktree と**同一ファイルを同時編集すると合流衝突**。回避策:
  1. `Omega.characteristic` instance 追加は**独立 micro-commit を main で先に入れる** (汎用・無害・Ch07 にも有益) → 両 worktree が rebase で取り込む。または
  2. 0016 worktree 側で OmegaSubgroup を触らず、`CriticalSubgroup.lean` 内に局所補題として置く (重複だが衝突ゼロ)。**推奨は 1** (`Omega.characteristic` は明らかに OmegaSubgroup.lean の正しい住所、Ch07 も将来使う)。
- `.lake/packages` / `references` は main から symlink 共有 (CLAUDE.md)。`lake update` は worktree で禁止。

### workflow stage 数 (1 本で回す場合)

依存が線形なので **5 stage** 推奨:

1. **Stage 1 (足場)**: `CriticalSubgroup.lean` scaffold + `IsCritical` def + `Omega.characteristic` (main micro-commit) + S4/S5/S8 (既存橋で即通る軽量段)。build-green。
2. **Stage 2 (S1+S2)**: Lemma 5.3.12 → 5.3.11 existence。**最大の山、ここが詰まりやすい**。`isCritical_exists` まで。
3. **Stage 3 (S6)**: `(xy)^p` 恒等式 + Ω₁ exponent p。2 番目の山。
4. **Stage 4 (S3+S7)**: faithful (iii)⇒(iv) + stability + C_Aut p-群。`isaacs_thm_4_36` 接続。
5. **Stage 5 (BG-facing)**: `thompson_critical_omega` を S01 §1D に載せ、mapping-table 更新、stale 誤記訂正、`lake build OddOrder.AxiomsCheck` 緑。

各 stage は `lake build OddOrder.GroupTheory.CriticalSubgroup` (Stage 1-4) / `...S01_Solvable` (Stage 5) で検証。Stage 2,3 は単一定理 build-green でないため `/goal` 単独条件には不向き (memory `goal-command-spec`: design/multi-sub 向きでない)。Stage 1,5 は build-green タスクとして `/goal` 適性あり。

---

## 関連ファイルパス (絶対パス)

- issue: `/home/ywr/odd-order/issues/0016-bg-s01-thm-1-13-critical.md`
- 新規 module: `/home/ywr/odd-order/OddOrder/GroupTheory/CriticalSubgroup.lean` (新規)
- BG-facing 設置先: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` (§1D L819 placeholder, mapping L51)
- Ω₁ 土台 (+ char 追加先): `/home/ywr/odd-order/OddOrder/GroupTheory/OmegaSubgroup.lean` (`Omega G p n` L58)
- エンジン: `/home/ywr/odd-order/OddOrder/Isaacs/Ch04_Commutators/Main.lean` (`isaacs_thm_4_36` L4173, `pow_mem_center_of_class_le_two_of_commutator_pow` L240, `isElementaryAbelian_quotient_center_of_class_le_two` L255, `IsAInvariant.map_subtype_of_characteristic` L2229)
- 作用枠: `/home/ywr/odd-order/OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean` (`IsCritical`→`IsAInvariant.of_characteristic` L2950, def L2894)
- restrictAction: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` L690
- C_Aut パターン: `/home/ywr/odd-order/OddOrder/Mathlib/Subgroup.lean` (`fixedPointsOfMulAut` L149)
- Gorenstein 原典 (verbatim 証明全文): `/home/ywr/odd-order/references/gorenstein/finite-groups.mmd` L3878-3945 (Lemma 5.3.9 / Thm 5.3.10 / Thm 5.3.11+5.3.12 / Thm 5.3.13)
- BG 原文: `/home/ywr/odd-order/references/bg/local-analysis.mmd` L461-472
- 訂正対象 stale notes: `/home/ywr/odd-order/notes/meta/phase2_cross_refs.md` L124, `/home/ywr/odd-order/notes/bg/s01_solvable.md` L77