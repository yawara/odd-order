# Pf §6 standalone (6.2)/(6.3) coherence producer — lane-h relane #7 (issue 2021)

> 割当: 2026-06-23 relane #7 (origin/main `4e4c5ca7`, issue 2021 RESOLVED)。lane-h = Pf §6
> coherence producer。lane-c の `S13_MaximalIII_IV` が cite する coherence obligation の
> **standalone 版**を §6/§8 機構から生産する (producer[lane-h] → consumer[lane-c S13])。
> このノートは本タスクの scoping + 中心 design question + plan の正本。

## 1. consumer (lane-c S13 のローカル obligation) — 生産先 signature

`OddOrder/Peterfalvi/S13_MaximalIII_IV.lean`:

- **Thm 6.3** `coherent_S_of_coherent_SH0C` (S13:188): `S(H₀C) coherent ⟹ S coherent`。
  = Pf (6.3) を (L,K,M,H,H₁)=(§13 の M, M', 1, HC, H₀C) で適用。`_hcoh : Nonempty (S07.IsCoherent
  hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)` → `Nonempty (S07.IsCoherent hyp.base.tau hyp.base.Sset
  hyp.base.A0)`。obligation signature には (6.3.a) nilpotent / (6.3.c) index bound は無い → lane-c が
  wiring で §13 facts ((9.6)/(11.1) 等) から供給する想定。
- **Thm 6.2** `coherent_quotient_bound` (S13:215): `S(H₁) coherent (H₁◁M, H₁<M') ⟹ |M':H₁| ≤ 2q|U:C|+1`。
  = Pf (6.2) の §13 instance。`hH1_norm`/`hH1_lt`/`hcoh` 前提 → `H1.relIndex (derivedInG M) ≤
  2 * hyp.q * hyp.C.relIndex hyp.U + 1`。

両者の coherence data = `hyp.base : S12.Hypothesis M` の `tau`/`Sset`/`A0` (下記 §3)。

## 2. Pf 原文 (6.2)/(6.3) — `references/peterfalvi/04.8_pp_30_37_*.mmd`

**Hypothesis (6.1)** (L4): Hypothesis (C) [§5 の filtration/coherence 仮説、要特定] + K solvable
normal subgroup of L + `S = {Ind_K^L θ | θ∈Irr K, θ≠1}`。`S(A) = {Ind_K^L θ | A⊆Ker θ, θ≠1}` (A◁L, A⊆K)。

**(6.2)** (L7-22): (6.1) + [A⊊K, B⊂D⊂C⊂K, D/B⊂Z(C/B), S(A) coherent, S(B) not] ⟹
`2|L:C|·√|C:D| ≥ |K:A|−1`。
証明: (C.b) で S₁,S₂={ψ,ψ̄}, S(A)⊆S₁⊆S(A)∪S(B), S₁ coherent, S₁∪S₂ not。K solvable ⟹ K/A に
degree-1 非自明既約 ⟹ S(A) は degree |L:K| の char を含む ⟹ |L:K| ∣ ψ(1)。**Theorem (5.6)** で
`2ψ(1)|L:K| ≥ ∑_{χ∈S₁} χ(1)²/‖χ‖² ≥ ∑_{χ∈S(A)} χ(1)²/‖χ‖²`。(C.c,d) で
`∑_{χ∈S(A)} χ(1)²/‖χ‖² = |L:K|∑_{θ∈T}θ(1)² = |L:K|(|K:A|−1)`。⟹ `2ψ(1) ≥ |K:A|−1`。
ψ=Ind θ で **θ(1) ≤ |K:C|√|C:D|** (Theorem (C) の degree bound) ⟹ ψ(1) ≤ |L:C|√|C:D| ⟹ 結論。

**(6.3)** (L24-48): (6.1) + [M⊂H₁⊂H⊂K, **(a) H/M nilpotent**, (b) S(H₁) coherent,
(c) |H:H₁|>4|L:K|²+1] ⟹ S(M) coherent。
証明: (b) で minimal A◁L (M⊂A⊂H₁, S(A) coherent)。A≠M と仮定。maximal B◁L (M⊂B⊊A)。H/M nilpotent ⟹
(A/B)∩Z(H/B)≠1、B 極大性で A/B⊂Z(H/B)。**(6.2) を C=H,D=A** で適用: `2|L:H|√|H:A| ≥ |K:A|−1`。
x=|H:A| とおくと `2|L:K||K:H|√x ≥ |K:H|x−1` ⟹ `2|L:K| ≥ √x−1/√x` ⟹ `x−2+1/x ≤ 4|L:K|²`。
(c) で x≥|H:H₁|>1 ⟹ |H:H₁|−1 ≤ x−1 ≤ 4|L:K|²、(c) と矛盾。∴ A=M、S(M) coherent。□

## 3. 既存機構 (building blocks)

### (6.2) core = `S08_Theorem63.lean` (`SibleyDadeHypothesis G L H` 形)
- `sum_re_div_normSq_SsubFiltration_eq` : `∑_{χ∈S(A)} χ(1)²/‖χ‖² = |L:H|·(|H:A|−1)` (= 6.2 の
  degree-square sum 恒等式; ここ H = (6.1) の K)。
- `exists_SsubFiltration_member_degree_index` : S(A) は degree |L:H| の member を含む。
- `sSubFiltration_sum_le_two_psi_caseB` (+ `_columnBreak`) : S₁ coherent が break {ψ,ψ̄} で拡張不能 ⟹
  `|L:H|·(|H:A|−1) ≤ 2·ψ(1)·η(1)` (case (c2))。= (6.2) 証明の core 不等式。

### Theorem (5.6) = `S07_RetargetScaled.lean` (5.6.3 reducible break) + S07_Coherence (orthonormal break)
coherence extension の不等式。(6.2) の `2ψ(1)|L:K| ≥ ∑χ(1)²/‖χ‖²` の source。

### `SibleyDadeHypothesis` (`S08_CoherenceCorePart1.lean:3265`) = Hypothesis (6.8)/(6.4) 形
fields: W1, H (≠⊥, normal, **nilpotent**), `split : L = H ⋊ W1` (complement), L odd, H^# TI in G,
dade datum, S = {Ind_H^L θ | θ≠1}, cases = (c1) Frobenius L=H⋊W1 ∨ (c2) Hypothesis46 (|W₂| prime,
W₂⊆[H,H], coprime |H||W1|)。**⚠ kernel H は nilpotent + complement を要求** (= (6.8) 特殊形)。

### §12/§13 coherence setup = general (6.1) 形 (NOT SibleyDadeHypothesis)
`S12.Hypothesis M` (`S12_MaximalIII_IV_V.lean:119`): `dadeData : S10.DadeSupportHypothesisData M
(typePA0 M typeP)` → `tau`/`Sset`/`A0` を honest projection で定義。`CertainTypeHypothesis (typePA0
M typeP) M` 利用可 (S12:734)。coherence = `IsCoherent hyp.tau hyp.Sset hyp.A0` (5.1)。

## 4. 🔑 中心 design question (rework 回避の要)

**既存 (6.2) core は `SibleyDadeHypothesis` (K=H nilpotent + complement, 6.8 形) で proven。
しかし §13 consumer は general (6.1) 形 (K=M' solvable・非 nilpotent かも、CertainTypeHypothesis/
DadeSupportHypothesisData ベース) で coherence を持つ。** この gap = 「repo の §6 は SibleyDadeHypothesis
filtration 経由で standalone (6.1)-form が無い」(LAUNCH/S13 docstring) の正体。

standalone (6.2)/(6.3) を生産するには次のいずれか (要次セッションで確定):
- **(A) 既存 core を general (6.1) 設定に一般化** — `sum_re_div_normSq_SsubFiltration_eq` 等を
  SibleyDadeHypothesis でなく「K solvable normal + S=Ind_K^L family + (5.6) coherence」だけで再証明。
  core の証明が H_nilpotent/split/TI/cases をどこまで使うか精査が要 (degree-square sum 恒等式自体は
  K normal + induction だけで出るはず; (c2) bound は (5.6)+filtration ⟹ 一般化可能性高)。
- **(B) §13→SibleyDadeHypothesis bridge** — §13 の (6.3) 適用は H=HC nilpotent。但し SibleyDadeHypothesis
  の kernel は (6.1) の K=M' に当たり、M' nilpotent でないと不成立 ⟹ 直接 bridge は無理筋の可能性大。
- **(C) general (6.1) hypothesis を新規定義し (6.2)/(6.3) を直接証明** — (A) の徹底版。

**最有力 = (A)/(C)**: (6.2)/(6.3) は教科書で general (6.1) (K solvable) に対し述べられ、SibleyDadeHypothesis
の nilpotent/complement/TI/cases は (6.8) capstone 固有。(6.2) 証明が実際に使うのは: K solvable (degree-1
char 存在)、S/S(A) の induction 構造、(5.6) coherence extension、degree bound θ(1)≤|K:C|√|C:D| (Thm C)。
これらを抽出した general 仮説 (≒ (6.1)) を立てるのが筋。

## 5. plan (次セッション)

1. **§5 Hypothesis (C) / (5.2) / Theorem (5.6) を特定** (`references/peterfalvi/04.7*` §5 + repo S05/S07)。
   (6.1) が前提する (C) の正体と、degree bound `θ(1)≤|K:C|√|C:D|` (Thm C) の repo 所在を確定。
2. **design question を確定** (A vs C): 既存 core lemma の hypothesis 依存を精査
   (`sum_re_div_normSq_SsubFiltration_eq` / `sSubFiltration_sum_le_two_psi_caseB` が H_nilpotent/split/
   cases を本当に使うか)。使わない部分が多ければ (A) で general 化、本質的なら (C) で新仮説。
3. **新 leaf** `S08_Theorem62_63_Standalone.lean` (or §6 leaf) に standalone (6.2)/(6.3) を立てる。
   上流優先: (6.2) を先に (degree-square sum + (5.6) bound + degree bound の assembly)、次に (6.3)
   (filtration descent: minimal A / maximal B / nilpotent⟹central / (6.2) 適用 / √ 算術 contradiction)。
4. lane-c が S13 `coherent_S_of_coherent_SH0C` / `coherent_quotient_bound` を cite して discharge
   (producer→consumer、signature-first)。
5. ⚠ 規約: §5-§8 は lane-b 名目領域 (dormant) ゆえ **既存 S05-S08 本体は触らず cite のみ、生産は新 leaf
   に隔離** (lane-b 復帰時の衝突回避)。境界で迷ったら hub issue。

## 6. status

2026-06-23 relane #7 受領 + 本 scoping 完了 (consumer signature / Pf 原文 6.2/6.3 / 既存 core /
design question の特定)。Lean 実装は次セッション (design question 確定 → 新 leaf assembly)。
build green 3882 jobs (main merge 状態、Lean 変更なし)。
