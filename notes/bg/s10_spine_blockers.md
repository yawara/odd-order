# BG §10 直列スパイン: ブロッカー精査 (2026-06-07)

worktree `bg-s10-spine` (branch `bg-s10-spine`, `ODD_ISSUE_BASE=4000`)。
対象ファイル `OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadical.lean`。

## 着地済み

- **Prop 10.14(d)** `normalizer_le_of_nontrivial_beta_subgroup` (commit `f21eb12`):
  sorry-free, axioms = `[propext, Classical.choice, Quot.sound]`。
  10.14(a)(b)(c) (`beta_global_structure`, 既証) のみに依存する唯一の grounded ターゲットだった。
  併せて base `isSylow_sylowMap_of_mem_sigma` を private→public 化 (σ Sylow-lifting、複数ファイル使用)。

## 直列スパインは Theorem 10.6 に全面ブロックされている

ユーザ指定の直列順 `proper_hasPLengthOne (10.6) → isHall_Mbeta (10.8) → 10.14/10.9/10.10` は、
**10.6 を起点に推移的に全滅**している。依存を精査した結論:

| ターゲット (file:line は landing 前の番号) | 直接依存 | 状態 |
|---|---|---|
| **10.6** `proper_hasPLengthOne` | r_p≤2: `maximal_hasPLengthOne_of_not_mem_alpha` (✅ base) + **p-length 部分群単調性** (❌); r_p≥3: **Thm 3.6** (❌) + **Lem 10.4(b)** (❌) + **Lem 6.3(a)** (❌) | **BLOCKED** |
| **10.7** `sylow_structure` | 10.6 ("P ⊆ O_{p',p}(M)") + Lem 6.6 (✅) | BLOCKED via 10.6 |
| **10.8** `isHall_Mbeta` | 10.6 + Thm 5.6 `narrow_sylow_solvable_structure` (✅ S05:3268) | BLOCKED via 10.6 |
| **10.9** `beta_complement_*` (3 本) | 10.8 + Lem 6.5 (✅) + Frattini (✅) + Hall (✅) | BLOCKED via 10.8→10.6 |
| **10.10** `normalizer_factorization` | §7 Prop 7.3/7.4/7.5 (✅) + **Cor 10.7** + Lem 6.5 (✅) | BLOCKED via 10.7→10.6 |

## 未形式化の upstream (10.6 の 4 ゲート)

1. **BG Theorem 3.6** (mmd L955): 「`G` 可解奇数位数, `H ⊴ G` normal Hall, `R` を `H` の補群,
   `R₀ ≤ R` prime order で `C_H(R₀)` が Z-群 ⇒ 任意素数 `p` で `[H,R]` は p-length one」。
   **最小反例法の多ページ証明** (V=F(H) が elementary abelian を示す等、表現論的)。
   §3 の独立した大仕事。リポジトリに無い (S03c は Thm **3.7** = Frobenius kernel nilpotent のみ)。
   → 10.6 の r_p≥3 ケースのエンジン。これが最大ブロッカー。
2. **BG Lemma 10.4(b)** (mmd MISSING_PAGE, PDF p.87): 「`p∈α(M), M_α≠1` ⇒
   `∃ x∈Ω₁(Z(P))#: ℳ(C_G(x))={M} ∧ C_{M_α}(x) Z-群`」。
   **未 statement**。`S10_LocalLemmas.lean` (lane A1) の `alpha_criterion` は (a)(c) のみで (b) は欠落
   (docstring に「Ω₁(Z(P)) の入れ子 encoding は後続」と明記)。Ω₁(Z(P)) encoding が要る。
   → 10.6 の r_p≥3 ケースで「order-q 元 x で C_{M_α}(x) が Z-群」を供給。lane A1 の領域。
3. **BG Lemma 6.3(a)** (mmd L1981): 「`H ⊴ G` normal Hall, `K` 補群, `H⊆G'` ⇒ `H=[H,K]` かつ
   `C_H(K)⊆H'`」。証明は clean (H*=[H,K]⊴G, G/H*=H̄×K̄, H̄⊆Ḡ'=H̄'×K̄' ⇒ H̄=H̄' ⇒ solvable で H̄=1)。
   ~80-150 行で形式化可能。`S06_Additional` の `inf_commutator_eq_of_coprime` は Lem **6.5**(a)、別物。
   → 10.6 で `M_α=[M_α,K]` を供給。
4. **p-length 部分群単調性**: `H ≤ G ∧ hasPLengthOne p G ⇒ hasPLengthOne p ↥H`。
   10.6 の reduction (M∈ℳ(H) を取り l_p(H) ≤ l_p(M)) に必要。isolate された lemma は無い。
   `hasPLengthOne := ¬ p∣|G/O_{p',p}(G)|` encoding で O_{p',p} の部分群版補題が要り、~50-150 行。

## 推奨される次アクション (優先度順)

- **(本命) BG Theorem 3.6 を §3 で形式化** (`OddOrder/BG/Ch1_Preliminary/S03*` に新ファイル)。
  これがスパイン全体の律速。最小反例法 + §1 (Prop 1.5/1.6, Lem 1.21) + §2 表現論 を要する大仕事。
  併せて clean な prerequisite (p-length 単調性, Lem 6.3a) も landing。
- **(代替) lane A1 = `S10_LocalLemmas` を先に進める**: Thm 3.6 と独立。10.4(b) を statement 化 +
  10.3/10.4/10.5/10.11/10.12/10.13 を埋める。10.6 とは別の高レバレッジ leaf 群。
- **(妥協) forward-axiom でスパインを配線**: Thm 3.6 / Lem 10.4b / Lem 6.3a / p-length 単調性を
  named axiom 化し 10.6→10.8→10.9→10.10 を上に組む。§10 ロジックは検証されるが axiom 負債が増える
  ([[scaffold-sorry-free-not-done]] の懸念)。要ユーザ判断。

## 検証済み (✅ 利用可能、再調査不要)

Thm 10.1 `fusion_control_of_mem_sigma` / Thm 10.2 `isHall_Msigma_Malpha`,`Msigma_le_derived`,`Malpha_isHall` /
Thm 4.18 `solvable_structure_of_pRank_le_two` / Thm 5.5 narrow core + Thm 5.6 `narrow_sylow_solvable_structure` (S05) /
Lem 6.5(a) `inf_commutator_eq_of_coprime`, 6.5(c) `exists_conj_eq_of_isHall_subgroupOf`, Lem 6.6
`exists_mem_centralizer_inf_conj_le_sylow` / §7 (sorry-free) / 10.14(a)(b)(c) `beta_global_structure` /
Uniqueness `isUniquelyMaximal_of_mem_e2_not_maximal` / `isSylow_sylowMap_of_mem_sigma` (今 public 化)。

## Lemma 10.13 / §11 も rep-theory keystone に推移ブロック (2026-06-07 検証)

§11.5/11.6/11.7 の単一ゲート **Lemma 10.13** (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`,
`S10_LocalLemmas.lean:1063`, 全 (a)(b)(c) が 1 sorry) は **独立に landing できない**:
- 証明 (BG p.79-80) の r(S)=2 ケースが **Cor 10.7(b)** (`r(S)=2 ⇒ Z(S) cyclic`) を使う。
- **Cor 10.7** (`sylow_structure`, `S10_BetaRadical.lean:43`, **sorry**) の (a) は "P ⊆ O_{p',p}(M)"
  = **Theorem 10.6** (`proper_hasPLengthOne`, sorry) を使い、(b)=(a)+Thm 4.16。
- Theorem 10.6 → **Theorem 3.6** → **Theorem 3.4** → 代数閉体 extraspecial 表現論 (= rep-theory keystone, `bg-reptower` レーン)。

⟹ **§11.5-7 → 10.13 → Cor 10.7(b) → 10.6 → 3.6 → rep-theory keystone** で推移ブロック。
§10 spine と同じく、§11 の残りも **keystone (Thm 3.4/3.6) がクリティカルパス**。

**ただし self-contained で unblocked な部分**: Lemma 10.13(c) のコア = 「(ℤ/p)² の位数 p の自己同型が
1 本の line を固定すると残り p 本の line を transitive に置換する」(GL(2,p) transvection 事実、純線型代数、
FT のブロックと無関係)。これは独立補題として今でも構築可能で、10.13(c) に最終的に必要 (非無駄)。
GL(2,p) 既存 infra = `Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean`。
