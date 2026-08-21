# BG §10: The Subgroups M_α and M_σ — mini-roadmap

## ✅✅ 2026-06-05 完了 — Thm 10.1 (keystone) sorry-free + axiom-clean

`fusion_control_of_mem_sigma` (BG Thm 10.1, 5-part a–e) 完成。`#print axioms` =
`[propext, Classical.choice, Quot.sound]`、full build 3580 jobs green。詳細・実装メモは
`issues/closed/0060-bg-thm101-fusion-control.md`「✅ DONE」節。

**要点**:
- part (b) = `fusion_b` (private): `Nat.card G - Nat.card X` の強帰納 (maximal-order counterexample)。
  WLOG「M を共役で取り替え P⊆M」は M^s=`conj s•M` を「M の共役 maximal」として扱い、`sigma_conj`
  (σ equivariance) で一般 `fusion_d_of_mem_sigma` を M₁ に直接適用して処理 (M を literal に取り替えない)。
  r(P)≥3 = Thm 9.6 (`uniquenessTheorem`) で P∈𝒰⟹L⊆M^s⟹矛盾; r(P)≤2 = Thm 4.18(e)
  (`solvable_structure_of_pRank_le_two`) + §6 Frattini (`frattini_decomp_of_rank_le_two`) + IH-for-P。
- (a) = `g=m*c` (M·C 順); (c)/(d)/(e) は (a)/(b) の系。**(e) は `X≤M` を明示追加**
  (`C_G(X)⊆M` だけからは X⊆M が一般に従わない: X 非可換だと X⊄C_G(X); BG の暗黙前提を明示)。
- 新 private helper 群: normalizer 成長 / σ⟹Sylow-of-G / conjOrderIso+coatom保存+随伴 /
  card・normalizer の共役同変 / σ_conj / card_lt_card_of_lt。AxiomsCheck は §9 同様未登録 (S10 未 import)。

**次**: Thm 10.2 は reduced capstone 完成。§10 残 frontier は Thm 10.6 →
Cor 10.7 → Lem 10.8 / Cor 10.9 / Prop 10.10-10.14。


## ✅ 2026-06-06 完了 — Thm 10.2 reduced capstone (`isHall_Msigma_Malpha`)

`isHall_Msigma_Malpha` の `sorry` を削除し、reduced 版 Thm 10.2 を axiom-clean で完成。BG Step 4 は
小さな bridge ではなく、以下の quotient/Fitting 証明ブロックとして実装済み:

- finite nilpotent 群の `π`/`π'` core decomposition: `O_π(K) ⊔ O_{π'}(K)=⊤`、よって `O_π(K)` は Hall。
- Hall `σ(M)` subgroup `S≤M` の像 `S/M_α` を `F(M/M_α)` 内の Hall subgroup として扱い、nilpotent core uniqueness から
  `S/M_α = O_{σ(M)}(F(M/M_α))`。
- characteristic-in-normal と quotient core preimage により `S≤M_σ`、normal Hall 吸収により逆包含、従って `S=M_σ`。
- Hall-E の局所 Hall subgroup を `M_σ` と同定して `Msigma_subgroupOf_isHall`、さらに
  `[M:M_σ]·[G:M]` と `p∈σ(M)⇒p∤[G:M]` で ambient `Msigma_isHall`。

検証: `lake build OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma` green、主要 theorem の
`#print axioms` は全て `[propext, Classical.choice, Quot.sound]`。issue 0061 closed。

## 🔨 2026-06-05 (続) — Thm 10.2 着手 (issue 0061)

`isHall_Msigma_Malpha` = §10 MAIN・gateway。issue `issues/closed/0061-bg-thm102-hall-structure.md` に証明構造
+ 依存マップ (Focal/Thm4.20/Hall存在 全て ✅、商 F(M/M_α) の機械が (a)/(b) の最重・要調査)。
**landed (axiom-clean, target build green)**: 商を要さない foundational lemma 3 本 —
- `alpha_subset_sigma` (α(M)⊆σ(M), BG step 1): r_p(M)≥3 ⟹ Sylow P̄ で rank≥3 ⟹ Thm 9.6 で P̄∈𝒰 ⟹
  N_G(P̄)≤M (10.1 r(P)≥3 分岐と同パターン)。
- `Malpha_le_Msigma` (M_α⊆M_σ): α⊆σ + `oPiCore_mono`。
- `Msigma_le_derived` (M_σ⊆M′, 2026-06-06): finite Sylow-generation helper + `Msigma_isPiGroup` で
  p∈π(M_σ) ⟹ p∈σ(M)、各 Sylow を M の Sylow に含め、`sylow_le_derived_of_mem_sigma` (Focal+10.1) で M′ に押し込む。
**完了後の状態**: `Msigma_ne_bot`、Hall `α(M)`、Hall `σ(M)`、capstone は全て完成。次 frontier は Thm 10.6。

## ✅ 2026-06-05 着手 — 依存 DAG 検証 + Thm 10.1 を first target に確定 (§9 完成で解禁)

**§9 (Uniqueness Thm 9.6) 完成 (commit 12ae441) で §10 解禁**。§10 = 18 scaffold sorry の大型節。
mmd L2657-2743 精読で **依存順序を検証** (本ノートの旧「Thm 10.1 が p-length-1 を要し Thm 10.6 で自動 →
循環?」は **誤り = red herring**):

- **Thm 10.1 (`fusion_control_of_mem_sigma`) = §10 keystone・first target・今 unblocked**。proof (mmd L2665-2711):
  (d) 先 (Sylow 共役 + `N_G(X)⊆M`) → (b)⟹(a)(c)(e) → (b) は **maximal-order counterexample X の帰納**。
  使う上流 = **Thm 9.6 (✅)** [r(P)≥3 分岐で P∈𝒰⟹L⊆M で矛盾] + **Thm 4.18(e)** [r(P)≤2 分岐] + Frattini。
  **Thm 10.6 (p-length-1) は使わない** (10.1→10.6 の循環は無い; 逆に 10.6 が 10.2→10.1 に依存)。
- **prerequisite 検証済 (repo 内 全存在)**:
  - Thm 9.6 = `Ch2.S09.uniquenessTheorem` / `scn3_isUniquelyMaximal` (✅ 2026-06-05)。
  - **Thm 4.18(e)** = `S04.solvable_structure_of_pRank_le_two` (S04g:878) の第5連言 `hasPLengthOne p L`
    (+ `G/O_{p',p}` abelian)。L=N_G(X) は proper⊆min-simple ⟹ solvable+odd, P 非自明で p∣|L|, r_p(L)=r(P)≤2。
  - **L=N_L(P)·O_{p'}(L) (Frattini step, mmd L2699)**: `hasPLengthOne p L` + **§6 Lemma 6.6 foundation**
    `S06.oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow` (O_{p',p}=O_{p'}⊔S) + Frattini で導く
    (P=Sylow-p of O_{p',p}(L), O_{p'}(L)∩X=1 ⟹ O_{p'}(L)⊆C_G(X))。
  - **Focal Subgroup Thm (Thm 1.17 BG)** = `Ch05.focalSubgroupTheorem` (Thm 10.2 用、10.1 では未使用)。
  - **σ 基本** (mmd L2655): p∈σ(M)⟹∀ Sylow-p P of M, N_G(P)⊆M ∧ P=Sylow-p of G。`mem_sigma_iff` (S10:149)
    は「∃ Sylow」形 ⟹ 共役で「∀ Sylow」へ拡張する小補題が要 (N_G 共役同変)。
- **攻略順 (BG-faithful)**: Thm 10.1 → Thm 10.2 (10.1 + Focal + Thm 4.20) → Thm 10.6 (10.2 + 4.18 + 3.6)
  → Cor 10.7 (10.1 + 10.6 + Lem 6.6) → Lem 10.8 / Cor 10.9 / Prop 10.10-10.14。
- **規模**: Thm 10.1 単独で BG ~50 行 = Lean 推定 250-400 行 (maximal-counterexample 帰納 + Sylow/conj
  bookkeeping + 5-part 連言)。dedicated 着手単位。issue 化推奨。

## 2026-06-02 B7 foundation checkpoint

Lean file: `OddOrder/BG/Ch3_MaximalSubgroups/S10_MalphaMsigma.lean`.

Concrete surfaces now present:
- Definitions: `idealPrime`, `alpha`, `beta`, `sigma`, `Malpha`, `Mbeta`, `Msigma`, `Fsigma`, `Fsigma'`, `elemAbelianOfRankIn`, `omega1CenterInG`.
- Basic API: membership rewrites for `idealPrime`/`alpha`/`beta`/`sigma`, subset lemmas `alpha_subset_primeFactors`, `beta_subset_alpha`, `beta_subset_primeFactors`, ambient containment lemmas for `Malpha`/`Mbeta`/`Msigma`/`Fsigma`/`Fsigma'`, `subgroupOf` identities for the three `M_*` radicals, `Malpha_isPiGroup`/`Mbeta_isPiGroup`/`Msigma_isPiGroup`, and `elemAbelianOfRankIn`/`omega1CenterInG` projection lemmas.

Current Lean inventory: 17 theorem-level `sorry`s remain in §10. These are not definitional blockers; they are BG hard results or downstream-facing theorem surfaces.

Main proof blockers: §7 Thompson transitivity/§9 uniqueness, BG §4 rank and cyclic p-group results, §5 narrow p-group gates, and the full local-analysis proofs of BG 10.1--10.14. Do not turn these into fields of a setup structure.

**スコープ**: BG §10 (pp.69-79 in PDF), mmd L2637-2912. 6 結果を扱う.
**形式化先 (予定)**: `OddOrder/BG/Ch3_MaximalSubgroups/S10_MalphaMsigma.lean`
**ROADMAP 上の位置**: Phase 2a 第 4 波（§9 完成必須）
**役割**: BG Ch.III 入口. maximal subgroup M の内部構造解析. M_α (α-部分), M_σ (σ-部分) という 2 つの特別な Hall subgroup 族の定義と性質. §11-§13 (Exceptional Maximal, Subgroup E, Prime Action) への橋渡し.

---

## TL;DR — maximal subgroup の家族化

§10 は **第 9 節の Uniqueness Theorem から卒業して，単一の maximal subgroup M の内部構造を徹底解剖** する最初の節. 最小反例 G の任意の maximal subgroup M に対して，素数の集合 α(M), σ(M) を M 内 p-group の rank に基づいて定義し，それらに対応する Hall subgroup M_α, M_σ を導入する.

**キーコンセプト**:
- **σ(M)**: M 内で N_G(P) ⊆ M (P = Sylow p-subgroup) を満たす素数 p の集合. M_σ = O_{σ(M)}(M) は Hall σ(M)-subgroup.
- **α(M) ⊆ σ(M)**: r_p(M) ≥ 3 なる素数 p の集合.
- **β(M) ⊆ α(M)**: "ideal" 素数（Theorem 5.3 下で Sylow p-群が narrow でない）の集合.

主定理 **Theorem 10.2** では:
- M_σ は (M と G 両者の) Hall σ(M)-subgroup
- M_σ ≠ 1 かつ M_α ≠ 1 （ただし r(M) ≤ 2 でない限り）
- r(M/M_α) ≤ 2 かつ M'/M_α は nilpotent

さらに **Theorem 10.6** は本セクション唯一の「フリースタンディング」深い結果：**G の任意の真部分群 H に対して，H は すべての素数 p に対して p-length 1 を持つ**. これは §7-§9 の局所一意性から区間 H 自体の局所 p-length 制限へのジャンプであり，§11-§13 の maximal subgroup 分析に本質的.

---

## §10 全 6 結果（表）

| # | 名前 | mmd 行 | 形式 | 簡述 | FT 役割 |
|---|------|--------|------|------|---------|
| 10.1 | Theorem 10.1 | 2657-2711 | Theorem (55 行証明) | p ∈ σ(M) なら C_G(X) の acting; conjugacy と normalization の制御. | **pivotal** |
| 10.2 | Theorem 10.2 | 2713-2743 | Theorem (31 行証明) | M_α, M_σ は Hall; r(M/M_α) ≤ 2; M_σ ≠ 1. | **MAIN** |
| 10.6 | Theorem 10.6 | 2779-2783 | Theorem (5 行証明) | G の真部分群 H は all p に対し p-length 1. | **structural** |
| 10.7 | Corollary 10.7 | 2787-2805 | Corollary (a-e, 19 行証明) | Sylow p-group の深い性質; [P,V] = P (V complement); r(P) ≤ 2 構造. | **applications** |
| 10.8 | Lemma 10.8 | 2809-2823 | Lemma (a-c, 15 行証明) | M_β (β-部分) の Hall 性; 各 p ∈ π(M)-β(M) での p-complement. | **supporting** |
| 10.9 | Corollary 10.9 | 2825-2842 | Corollary (a-b, 18 行証明) | p, q ∈ β(M)' での X 作用; Frattini factorization. | **applications** |

**加算**: mmd L2844-2911 に Proposition 10.10 (A ∈ ℰ_p² ∩ ℰ_p*, Q ∈ H_G*(A;q) の場合) と Proposition 10.11, 10.12, 10.14 の 4 つ追加. これらは §11-§13 の準備だが，本セクション "主" 6 結果に次ぐ重要性.

---

## M_α, M_σ, M_β の精密定義

### 前置記法（§10 冒頭, L2637-2647）

maximal subgroup M に対して，以下を定義:

```
α(M) = {p ∈ π(M) : r_p(M) ≥ 3}
β(M) = {p ∈ α(M) : p is ideal}
σ(M) = {p ∈ π(M) : N_G(P) ⊆ M for some Sylow p-subgroup P of M}

M_α = O_{α(M)}(M)     [p-radical over α(M)]
M_β = O_{β(M)}(M)     [p-radical over β(M)]
M_σ = O_{σ(M)}(M)     [p-radical over σ(M)]

F_σ(M) = O_{σ(M)}(F(M))      [Fitting 内の σ-radical]
F_{σ'}(M) = O_{σ(M)'}(F(M))  [Fitting 内の σ'-radical]
```

### 素数分類の意味

**ideal prime** p ∈ β(M):
- r_p(G) ≥ 3（G 全体の p-rank は 3 以上）
- ℰ²(P) ∩ ℰ*(P) = ∅（P = Sylow p-subgroup において，rank 2 の部分は「exceptional」ではない）
- 同値: Theorem 5.3 により，Sylow p-群は **not narrow**.
- **物理的意味**: p-group が「単純」で，rank の視点からも複雑でない.

**σ(M) の定義**:
- p ∈ σ(M) ⟺ ある Sylow p-subgroup P ⊆ M に対して N_G(P) ⊆ M.
- **核心**: P が「M-normalized」（つまり，M で最大化）なら，G 全体での P の normalizer が M に含まれる.
- これは rank 3 以上の p に加えて，「幾何的に M で特別な」素数も捕捉.

**包含関係**:
```
β(M) ⊆ α(M) ⊆ σ(M)
M_β ⊆ M_α ⊆ M_σ
```

### Theorem 9.6 （Uniqueness）との継承

§9 の終結で，**rank ≥ 2** なる任意の K ⊆ G に対して K ∈ 𝒰（一意的に maximal に含まれる）ことが確立. §10 ではこれを逆用: **単一 M ∈ ℳ に対して，Sylow p-subgroup P の形状から σ(M) や α(M) を認識できるか** という局所問題に転化.

---

## Theorem 10.1: Conjugacy と Transfer の制御

### 主張

M ∈ ℳ, p ∈ σ(M), X = nonidentity p-subgroup ⊆ G に対して:

1. X ⊆ M and X^g ⊆ M ⇒ g = cm for some c ∈ C_G(X), m ∈ M.
2. C_G(X) acts transitively on {M^g : g ∈ G, X ⊆ M^g}.
3. X ⊆ M ⇒ N_G(X) = N_M(X)C_G(X).
4. X = Sylow p-subgroup of M, X^g ⊆ M ⇒ g ∈ M.
5. C_G(X) ⊆ M, X^g ⊆ M ⇒ g ∈ M.

### 証明梗概（L2665-2711）

**Step 1**: (d) を先に証明. X と X^g が同じ M のSylow p 部分なら，conjugate: (X^g)^h = X for some h ∈ M. すると gh ∈ N_G(X) ⊆ M より g = (gh)h^{-1} ∈ M.

**Step 2**: (a) は (d) + (b) から従う. (b) を反証法で: 反例 X を最大 order で選ぶ. L = N_G(X), M_1, M_2 ∈ {M^g : X ⊆ M^g} が C_G(X)-共役でないと仮定.

**Step 3**: M_2^g = M_1 for some g ∈ G. X, X^g ⊆ M_1 だが，X は M_1 の Sylow p-subgroup ではない（否，(d) で矛盾）. よって X ⊂ X_1 ⊆ L ∩ M_1 ⊆ ...（細かい subgroup ネスト）.

**Step 4**: P を L の Sylow p-subgroup とし，P ⊆ M（§9 の Uniqueness で可能）. r(P) ≥ 3 なら Thm 9.6 で P ∈ 𝒰，L ⊆ M から矛盾（異なる maximal が同時）. ゆえ r(P) ≤ 2.

**Step 5**: r(P) ≤ 2 なら Theorem 4.18(e) （p-length 1 下での Sylow structure）で P は O_{p',p}(L) の Sylow p-subgroup. L = N_L(P)O_{p'}(L) を Frattini で分解. ここで p-length 1 が鍵（が，H が真部分なら Thm 10.6 で自動）.

### 役割

**Theorem 10.1 全 5 部** は「p ∈ σ(M) なら，p-subgroups は maximal の conjugacy と centralization で厳しく制御されている」という深い structural result. 後続の Thm 10.2 の Hall 性証明の土台になるだけでなく，§11-§13 の detailed maximal 分析でも頻出. **特に (c), (e) は Corollary 10.7 での transfer arguments に直結**.

---

## Theorem 10.2: M_α, M_σ の Hall 性（主結果）

### 主張（L2713-2719）

M ∈ ℳ に対して:

**(a)** M_α is a Hall α(M)-subgroup of M and of G.

**(b)** M_σ is a Hall σ(M)-subgroup of M and of G.

**(c)** M_α ⊆ M_σ ⊆ M'.

**(d)** r(M/M_α) ≤ 2 and M'/M_α is nilpotent.

**(e)** M_σ ≠ 1.

### 証明梗概（L2721-2743）

**Step 1**: M(α) = Hall α(M)-subgroup of M. For any P (nontrivial Sylow of M(α)), r(P) ≥ 3 ⇒ P ∈ 𝒰 by Thm 9.6 ⇒ N_G(P) ⊆ M. So α(M) ⊆ σ(M) and M(α) ⊆ M(σ) = Hall σ(M)-subgroup of G.

**Step 2**: For any p ∈ σ(M), P = Sylow p-subgroup of M. Then N_G(P) ⊆ M ⇒ P = Sylow p-subgroup of G. By Focal Subgroup Theorem (Thm 1.17):

```
P = ⟨x^{-1}y : x, y ∈ P and x ~_G y⟩
P ∩ M' = ⟨x^{-1}y : x, y ∈ P and x ~_M y⟩
```

**Step 3**: If x ∈ P, g ∈ G, x^g ∈ P, then by Thm 10.1(X = ⟨x⟩), x^g = x^m for some m ∈ M. So every G-conjugacy is M-conjugacy ⇒ P ⊆ P ∩ M' ⊆ M'.

**Step 4**: M(α) ⊆ M(σ) ⊆ M'. Now F(M/M_α) is an α(M)'-group with rank ≤ 2 (by def of α). M_α ⊆ M(α) and M(σ)/M_α ⊆ M'/M_α = (M/M_α)' ⊆ F(M/M_α). Since F(M/M_α) is α(M)'-group, M(σ)/M_α is Hall in F(M/M_α) and normal in M/M_α. So M(σ) ⊲ M, hence M(σ) = M_σ (uniqueness of Hall subgroup).

**Step 5**: r(M/M_α) ≤ 2 follows from definition of α(M). M'/M_α ⊆ F(M/M_α) is nilpotent.

**Step 6** (M_σ ≠ 1): Assume M_α = 1. Then r(M) ≤ 2. Let q = largest prime dividing |M|. Then O_q(M) is Sylow q-subgroup, N_G(O_q(M)) = M (by maximality), so q ∈ σ(M) ⇒ M_σ ≠ 1.

### マイルストーン

Thm 10.2 は **BG の主定理群の最初の大型結果**. M_σ が Hall かつ M' に含まれるという事実から，後の Thm 10.6 (p-length 1) や Lemma 10.8 (β-radical), Corollary 10.9 (action controlling) へ次々と応用が波及. さらに Thm 15.2 (M_σ/F(M_σ) abelian) など §15 の major results も引用依存.

---

## Theorem 10.6: p-length 1 （構造定理）

### 主張（L2779-2779）

H = proper subgroup of G に対して，H は すべての素数 p に対して **p-length 1** を持つ.

**p-length の定義**: H has p-length one ⟺ H/O_{p',p}(H) is p'-group.

### 証明（L2781-2783）

**Step 1**: M ∈ ℳ(H) を選ぶ. M が p-length 1 を示せば十分 (M の tower が H に制御).

**Step 2**: r_p(M) ≤ 2 の場合，Theorem 4.18 (rank ≤ 2 p-group の p-length 定理) で直ちに M は p-length 1.

**Step 3**: r_p(M) ≥ 3 と仮定. M_α の定義から p ∉ α(M), i.e., p ∉ π(M) or r_p(M) ≤ 2. ここで r_p(M) ≥ 3 と矛盾せず，p ∈ π(M) なら r_p(M) ≤ 2... **矛盾回避の再読が必要** （手書きノート：実際は r_p(M) ≥ 3 なら p ∈ α(M), M_α と its complement K を考える）.

**Step 4**: K = complement to M_α in M とする. Thm 10.2 から M_α ⊆ M'. Lemma 6.3(a) により，M_α = [M_α, K]. q ∈ π(K/K') とし，Q = Sylow q-subgroup of K とする.

**Step 5**: Lemma 10.4 より，∃x ∈ Q, order q, C_{M_α}(x) = Z-group. Theorem 3.6 により，[M_α, K] has p-length 1. Since M_α = [M_α, K], done.

### Lean progress (2026-06-06)

`maximal_hasPLengthOne_of_not_mem_alpha` を追加し、Thm 10.6 の maximal subgroup base branch を完成。
`p∈π(M)` なら `p∉α(M)` から `pRank M p≤2` として Thm 4.18(e) を適用し、`p∉π(M)` なら
`|M/O_{p',p}(M)| ∣ |M|` から直接 `hasPLengthOne`。さらに `p∈α(M)` hard branch support として
`sylow_le_Malpha_of_mem_alpha_of_isHall` と
`not_dvd_card_quotient_Malpha_of_mem_alpha_of_isHall` を追加し、α-Sylow が `M_α` に吸収されることと
`M/M_α` が α-prime を含まないことを public 化した。S10 leaf build green、axioms は標準3公理のみ。
残り frontier は issue `0062-bg-thm106-p-length-one.md`: maximal reduction/subgroup-closure と、
`p∈α(M)` hard branch の Lemma 6.3(a) + Lemma 10.4 fragment + BG Thm 3.6 接続。

### 役割

**Theorem 10.6 は本セクション唯一の「フリースタンディング」structural result であり，同時に全 §11-§13 へ汎用的に使われる**. 特に:
- §11 (Exceptional): Hypothesis 11.1 下での maximal 分析で p-length 1 仮定が引き継がれ，Lemma 6.5, 6.6 適用基盤.
- §12 (E subgroup): E と maximal の interaction 下で部分群の derived/upper series 計算で.
- §13 (Prime Action): p-length 1 下での derived series acting.

---

## Corollary 10.7: Sylow p-group の深い性質

### 主張（L2787-2792）

P = Sylow p-subgroup of G に対して:

**(a)** V = complement to P in N_G(P) ⇒ P = [P, V] ⊆ N_G(P)'.

**(b)** r(P) ≤ 2 ⇒ P is abelian OR P is central product of nonabelian P_1 (order p³, exp p) and cyclic P_2 with Ω_1(P_2) = Z(P_1).

**(c)** Q ⊆ P, x ∈ G, Q^x ⊆ P ⇒ Q^x = Q^y for some y ∈ N_G(P).

**(d)** For every subgroup Q of P, N_P(Q) is Sylow p-subgroup of N_G(Q).

**(e)** R = p-subgroup, Q ⊆ P ∩ R, Q ⊲ N_G(P) ⇒ Q ⊲ N_G(R).

### 証明スケッチ（L2795-2805）

**前提**: M ∈ ℳ(N_G(P)) を選ぶ. p ∈ σ(M) より，Thm 10.6 から P ⊆ O_{p',p}(M). Lemma 6.6 を適用.

**(a) 証明**: Thm 10.2 から P ⊆ M_σ ⊆ M'. Lemma 6.6(b) により，**P ⊆ (N_M(P))' = (N_G(P))'**. Lemma 6.3(a) では K complement なら [P, V] = P.

**引用**: **L2797 では Lem 6.6 を "we know that P ⊆ (N_M(P))' ..."** と使用.

**(c) 証明**: Thm 10.1 により ∃u ∈ M s.t. Q^u = Q^x. **Lemma 6.6(c)** により ∃y ∈ N_M(P) s.t. Q^y = Q^u.

**引用**: **L2801 では "By Lemma 6.6(c), there exists y ∈ N_M(P) such that Q^y = Q^u."** Thm 10.1 + Lem 6.6(c) の連携が visible.

**(d), (e) 証明**: (c) を用いたSylow transfer argument.

### Lem 6.5, 6.6 の具体的役割

| 引用先 | mmd 行 | Lem番号 | 内容 | 必要理由 |
|--------|--------|--------|------|---------|
| Cor 10.7(a) 証明 | 2797 | **Lem 6.6(b)** | P ⊆ G', p-length 1 ⇒ P ⊆ (N_G(S))' | M_σ ⊆ M' と coprime action での derived 制御 |
| Cor 10.7(c) 証明 | 2801 | **Lem 6.6(c)** | Y ⊆ S, Y^x ⊆ S ⇒ x = cg (c ∈ C_G(Y), g ∈ N_G(S)) | Sylow conjugacy の 局所化 (Thm 10.1 → N_G(P) へ) |

### 役割

Corollary 10.7 は §10 の中では最も「応用色」が濃い. 5 部 (a)-(e) すべてが §12-§13 で多用される（特に (d) の Sylow transfer structure, (e) の normalization spread は Lemma 12.3 など major lemmas での backbone）.

---

## Lemma 10.8 と Corollary 10.9: β-radical と nilpotent Hall

### Lemma 10.8（L2809-2823）

M ∈ ℳ に対して:

**(a)** M_β is Hall β(M)-subgroup of M and of G.

**(b)** M' and M_σ have nilpotent Hall β(M)'-subgroups.

**(c)** For each p ∈ π(M) - β(M), both M' and M_σ have normal p-complements, and p is largest prime divisor of |M/O_{p'}(M)|.

### 証明梗概（L2815-2823）

**Step 1**: p ∉ β(M) なら r_p(M) ≤ 2. P = Sylow p of M は narrow. Thm 10.6 から M has p-length 1. Thm 5.6 (narrow p-group 定理) により，M' has normal p-complement.

**Step 2**: normal p-complements (for all p ∈ π(M) - β(M)) の交集合 = normal β(M)-subgroup of M' containing M(β) (the Hall β(M)-subgroup). Thus M(β) = O_{β(M)}(M').

**Step 3**: Since each p-complement is normal, M' is abelian mod O_p for all relevant p ⇒ M'/M_β is nilpotent.

### Corollary 10.9（L2825-2842）

**(a)** p, q ∈ β(M)' distinct, X = q-subgroup, X ⊆ M' or p < q ⇒
   1. X centralizes Sylow p-subgroup of M_σ.
   2. if p ∈ α(M), then C_M(X) ∈ 𝒰.
   3. X = Sylow q-subgroup of M' ⇒ N_M(X)' contains Sylow p-subgroup of M'.

**(b)** H ∈ ℳ - {M}, N_G(S) ⊆ H ∩ M for Sylow S ⇒ M = (H ∩ M)M_β and α(M) = β(M).

**Lean surface**:
- `beta_complement_centralizes`: Cor 10.9(a)(1)(2).
- `beta_complement_normalizer_derived_contains_sylow`: Cor 10.9(a)(3).
- `beta_factorization_of_sylow_normalizer_in_intersection`: Cor 10.9(b).

### 引用：Lem 6.5（L2840）

Corollary 10.9(a)(3) 証明:

```
W = Hall {p,q}-subgroup of XM' containing X
  ⊆ Hall β(M)'-subgroup W* of XM'.
So W ∩ M' is nilpotent.
...
M = M_β U where U = N_M(X).
O_p(W) is Sylow in M' ∩ U, (|O_p(W)|, |M_β|) = 1.
By Lemma 6.5(b), O_p(W) ⊆ U'.
```

**L2840 で "By Lemma 6.5, ..." と plaintext は省略されてるが，引用は明白**. Lem 6.5(b) の coprime action factorization N_G(H) = C_K(H)N_U(H) が，M = M_β U, (|O_p(W)|, |M_β|) = 1 という設定で直結.

---

## Proposition 10.10 - 10.14（補助結果群）

### Proposition 10.10（L2844-2854）

A ∈ ℰ_p² ∩ ℰ_p*, Q ∈ H_G*(A;q), q ∈ π(C_G(A)) ⇒ ∃ Sylow p-subgroup P ⊇ A such that:

1. N_G(P) = O_{p'}(C_G(P))(N_G(P) ∩ N_G(Q)).
2. P ⊆ N_G(Q)'.
3. If Q cyclic or ℰ²(Q) ∩ ℰ*(Q) ≠ ∅, then P centralizes Q.

**引用**: Lem 6.5(b) at L2852 in proof of (b).

### Proposition 10.11（L2856-2883）

M ∈ ℳ, K = σ(M)'-subgroup of M ⇒
1. K ∉ 𝒰.
2. r(C_K(M_σ)) ≤ 1.
3. C_K(M_σ) ∩ M' is cyclic normal subgroup of M.
4. (条件付) [K, P] centralizes M_σ and is cyclic normal in M.

**Lean surface**:
- `sigma_complement_rank_le_one`: Prop 10.11(a)(b)(c).
- `sigma_complement_commutator_cyclic_normal`: Prop 10.11(d).

### Proposition 10.12（未掲示, mmd L2885-???）

M, H ∈ ℳ, H not conjugate to M ⇒
1. M_α ∩ H_σ = 1 and α(M) ∩ σ(H) = ∅.
2. (if M_σ nilpotent) M_σ ∩ H_σ = 1 and σ(M) ∩ σ(H) = ∅.

### Proposition 10.14（L2894-2911）

p ∈ β(G), P = Sylow p-subgroup of G ⇒
1. ℰ²(P) ∩ ℰ*(P) and ℰ_p²(G) ∩ ℰ*(G) are empty.
2. Every p-subgroup R with r(R) ≥ 2 lies in 𝒰.
3. For subgroup X ⊆ P, N_P(X) ∈ 𝒰.
4. For nonidentity β(M)-subgroup Y of M, N_G(Y) ⊆ M.

**Lean surface**:
- `beta_global_structure`: Prop 10.14(a)(b)(c).
- `normalizer_le_of_nontrivial_beta_subgroup`: Prop 10.14(d), the direct §13 gate.

---

## §9 Uniqueness からの継承：𝒰 集合と σ, α

### Uniqueness Theorem (Thm 9.6) の復習

```
r(K) ≥ 2, [r(K) ≥ 3 or r(C_G(K)) ≥ 3]
  ⇒ K ∈ 𝒰
```

ここで **𝒰 = {K ⊆ G : |{M ∈ ℳ : K ⊆ M}| = 1}** = maximal に一意的に含まれる部分群の族.

### §10 での α(M), σ(M) の定義の意図

§10 は §9 の逆: **「K ∈ 𝒰 の判定基準を M 内からどう見るか」** という視点転換.

- **α(M)**: M 内で「大きい」（rank ≥ 3）p-group がいる素数の集合. Thm 9.6 により，M の α(M)-部分に含まれる rank ≥ 3 p-group は自動的に 𝒰 に属する.
  
- **σ(M)**: より**geometric**: N_G(P) ⊆ M という M-normalization condition. これは「Sylow p-subgroup がどの maximal に「belong」するか」を局所的に特性化. §9 の Uniqueness は「rank 視点」，§10 の σ は「normalization 視点」.

### Lemma 9.5 の echo

§9 Lemma 9.5 は「A ∈ SCN_3(p) ⇒ A ∈ 𝒰」を示した. §10 の Theorem 10.1-10.2 はこれを「A が σ(M) や α(M) に含まれていれば，そのSylow の normalization が确定される」という形で再利用.

---

## §11-§13 への橋渡し

### §11 Exceptional Maximal Subgroups

Hypothesis 11.1 冒頭:
```
M ∈ ℳ, p ∈ σ(M)', A_0 ∈ ℰ_p¹(M), N_G(A_0) ⊆ M.
```

- **σ(M)' = π(M) - σ(M)** つまり σ-exceptional な素数.
- By **Lemma 10.5** (§10 内の補助), r_p(M) = 2 and A_0 ⊆ A for A ∈ ℰ_p²(M).
- Since p ∉ σ(M), N_G(P) ⊈ M (P = Sylow p of M).

**使用**: M_α, M_σ の rank 制限; Thm 10.6 下の p-length 1; α, σ の定義そのもの.

### §12 The Subgroup E

E = "exceptional" structure の詳細解析. Thm 10.2 (r(M/M_α) ≤ 2) と Lemma 10.8 (β-radical の nilpotent Hall structure) から，M の derived/Fitting structure が厳密に制御され，E との共役性が決定される.

### §13 Prime Action

M の derived structure (M' の p-length, Sylow actions) on E. Corollary 10.7 (p-length 1 下での [P, V] = P 等) の応用.

---

## Peterfalvi §10 (Structure of Minimal Non-abelian Simple Group) との関係

BG §10 は Feit-Thompson 局所部の最小反例 G **inside maximal subgroups** に特化.

Peterfalvi §10 (04.10_*.mmd) は **minimal non-abelian simple group の structure** を（Peterfalvi の entire theory 下で）classify. 両者は異なる「non-structure」を扱う（FT G は solvable, Peterfalvi S は simple non-abelian）が，**M_σ, M_α の family parametrization と局所的な Hall/Sylow理論**（p-length, rank ≤ 2）は conceptually parallel.

---

## mathlib カバレッジ

| 概念 | mathlib 存在 | 新規実装要 | 注記 |
|------|-------------|----------|------|
| Fitting subgroup F(G) | low | Yes | Phase 1 で実装予定. Maximal subgroups の Fitting 構造の記述は BG §8 (Thm 8.1) で初. |
| p-rank r_p(P) | mid | Partial | basic rank def は OK. 「ideal prime」の判定 (ℰ²(P) ∩ ℰ*(P) = ∅) は Thm 5.3 実装後. |
| p-radical O_π(G) | high | No | mathlib has Subgroup.pRadical. |
| Hall subgroup | mid | Yes | basic Hall (non-unique solvable) あり，A-invariant Hall (unique under action) は Isaacs Ch.3 完成で新規. |
| p-length 1 | low | Yes | Definition and Thm 4.18 (rank ≤ 2 下) = Phase 1 Ch.4 で. Thm 10.6 全般は新規. |
| Sylow normalization / σ(M) | low | Yes | σ(M) の定義自体が BG 独自，maximal subgroups の normalization graph として新規. |
| Transfer / Focal / Burnside | high | No | existing Mathlib/GroupTheory/{Transfer,Focal,BurnsidePComplement} |
| Lemma 6.5, 6.6 (solvable + p-length 1) | low | Yes | **Phase 1 Ch.3 or Ch.4 で実装予定. p-length 1 が鍵的前提.**|

### 形式化の依存順序

```
Phase 1 完了
  ↓
§1 Elementary Solvable (A-invariant Hall 含)
  ↓
§4 p-Groups Small Rank + Thm 4.18 (p-length 1 下 structure)
  ↓
§6 Additional Results (Lem 6.5, 6.6 実装, Thm 6.2 normal-J)
  ↓
§7-§9 Uniqueness (𝒰 集合, Thm 9.6)
  ↓
★ §10 M_α, M_σ
    - Thm 10.1 (Conjugacy/Transfer with σ(M))
    - Thm 10.2 (Hall 性)
    - Thm 10.6 (p-length 1 for proper subgroups)
    - Cor 10.7 (Sylow structure + Lem 6.5, 6.6 連携)
    - Lem 10.8, Cor 10.9 (β-radical)
```

---

## Phase 2a 形式化着手順

### 準備段階（Phase 1 完成直後）

1. **§1 (Elementary)** と並行して **§4 (Small Rank)** 実装.
2. **Theorem 4.18** (rank ≤ 2 p-group の p-length 1 定理) が Thm 10.6 の「base case」になるので必須.

### Phase 2a 第 4 波（§9 完成直後）

1. **Lemma 6.5, 6.6** を含む **§6 (Additional)** の形式化を確認. （これは Phase 1 Ch.3/7 (Frobenius/p-stability) の完成と同期）.

2. **§10 着手**:
   - Thm 10.1 (Conjugacy/Transfer): Thm 10.1(b)-(e) が Thm 10.2, Cor 10.7 の前提.
   - Thm 10.2 (Hall 性): 手厚くカバー（Focal Subgroup Theorem 1.17 を多用）.
   - Thm 10.6 (p-length 1): Thm 4.18 + Thm 3.6 の連携が鍵.
   - Cor 10.7, Lem 10.8, Cor 10.9: Lem 6.6 の 3 部適用を正確に.

3. **Proposition 10.10-10.14**: 補助的だが §11-§12 の前提なので，軽めに.

### §10 ノート内での「micro-roadmap」

```
Thm 10.1
  ├─ (a)-(e): Conjugacy control via Thm 9.6 + Thm 4.18 + Frattini.
  └─ role: Transfer basis for Thm 10.2, Cor 10.7.

Thm 10.2 (Hall 性)
  ├─ (a)-(b): Hall subgroup structure.
  ├─ (c): M_α, M_σ ⊆ M' (Focal Group Theorem)
  ├─ (d): rank/nilpotent constraints
  ├─ (e): nonidentity M_σ (Burnside-style for largest prime)
  └─ role: core result for all of §10-§13.

Thm 10.6 (p-length 1)
  ├─ Thm 4.18 (rank ≤ 2 base case)
  ├─ Thm 3.6 (commutator control)
  └─ role: freestanding + every §11-§13 lemma.

Cor 10.7 (Sylow properties)
  ├─ (a): P = [P,V] ⊆ N_G(P)' [Lem 6.6(b) key]
  ├─ (b)-(e): Sylow structure / normalization spread
  └─ role: backbone for §12-§13 Sylow actions.

Lem 10.8, Cor 10.9 (β-radical)
  └─ role: supplements Thm 10.2 with "thin" maximal subgroups (small α).
```

---

## 未解決 / TODO

### 形式化時の注意

1. **mmd L2765 MISSING_PAGE_FAIL:87**: Prop 10.10 の直前ページが PDF では欠落. PDF p.87 を直接参照して補完.

2. **Lemma 10.4** (§10 内, 未抽出): Corollary 10.7, Thm 10.6, Corollary 10.9 の証明で引用される「X ⊆ P なら，∃x ∈ Q s.t. C_{M_α}(x) is Z-group」という statement. exact line number を確認後，補助 Lemma として.

3. **Lem 6.3 との違い**: Corollary 10.7(a) と Corollary 10.9(a)(3) で「Lemma 6.3」と「Lemma 6.5」が混在. Lem 6.3 の exact content (mmd line) を確認（coprime commutator factorization vs. coprime action factorization）.

4. **Proposition 10.10-10.14 の統合ポイント**: §11-§13 着手時に，どの propositions を§10 本文に，どれを§11-§13 prep lemmas に分割するか再精査.

### 形式化に向けた細項

- Lemma 10.1 (補助, L2643 around): "ideal prime" の判定(Theorem 5.3 連携).
- Lemma 10.3 (補助): Corollary 10.7(b) の「rank 2 Sylow 構造」の前置定理. exact definition確認.
- Lemma 10.4 (補助): Corollary 10.7 (Thm 10.6), Corollary 10.9 で使用の「rank 1 element action」.
- Lemma 10.5 (補助, 下部で): Hypothesis 11.1 (§11) でも引用. exact statement 抽出.

---

## 参考文献（本セクション内）

- **Theorem 5.3** (Narrow p-group 定理, §5): ideal prime の定義基盤.
- **Theorem 6.2** (normal-J, §6): §8-§9 での crucial, ここでは直接引用なし.
- **Lemma 6.3, 6.5, 6.6** (solvable + coprime action): Corollary 10.7, Corollary 10.9 で多用.
- **Theorem 9.1, 9.5, 9.6** (Uniqueness, §9): α(M), σ(M) の conceptual basis.
- **Theorem 1.17** (Focal Subgroup Theorem): Thm 10.2 (c) で P ⊆ M' 証明.
- **Theorem 3.6** (Commutator control): Thm 10.6 証明.
- **Theorem 4.16, 4.18, 4.20** (p-group rank ≤ 2): Thm 10.2 (d), Thm 10.6 base case.

---

## 完成予想時期

- **形式化開始**: Phase 2a 第 4 波（§9 完了から 2-3 週間後）
- **完成目安**: §10 単独で 1-2 週間（Lemma 6.5, 6.6 実装と synchronize）
- **§11-§12 への transition**: §10 完成直後に Hypothesis 11.1 と σ(M)' の意味を明確化

---

*作成: 2026-05-22. 出典: `references/bg/local-analysis.mmd` L2637-2912 (6 主要結果).*
*§9 Uniqueness (s09_uniqueness.md) からの直接の継承. Lem 6.5, 6.6 引用関係を可視化.*
*形式化詳細は Phase 2a 第 4 波着手時に per-lemma investigation へ.*
