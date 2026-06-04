# BG §9: The Uniqueness Theorem — mini-roadmap (FT critical)

**スコープ**: BG §9 (pp.64-68 in PDF), mmd L2486-2630. 6 結果を扱う.
**形式化先 (予定)**: `OddOrder/BG/Ch2_Uniqueness/S09_Uniqueness.lean`
**ROADMAP 上の位置**: Phase 2a 第 3 波（§8 完成必須）
**役割**: **maximal subgroup の一意性** (𝒰 集合の特性化), BG Ch.III/IV （§10-§13）の前提。Uniqueness Theorem は Peterfalvi §10（Structure of Minimal Non-abelian Simple Group）への橋渡し。

---

## TL;DR — Phase 2a 中盤の山場

§9 は BG のクリティカルパスの**第 3 段階**（§7 Transitivity → §8 Fitting of Max → **§9 Uniqueness**）の最終仕上げ。最小反例 G に対して、**rank ≥ 2 の部分群 K は（一定条件下で）maximal subgroup のいずれかに含まれる** ことを示す（Theorem 9.6）。これは Ch.3 (§10-§13) で maximal subgroup の構造を詳しく分析するための **基礎的な整理定理** として機能する。

中核は **Theorem 9.1** (非巡回 p-element Sylow p-subgroup の一意性) と **Lemma 9.5** (SCN₃(p) の元が 𝒰 に属すること) で、両者が **Theorem 9.6** (Uniqueness Theorem: r(K) ≥ 2 なら K ∈ 𝒰) の証明の要となる。

---

## §9 全 6 結果（表）

| # | 名前 | mmd 行 | 形式 | 簡述 | FT 役割 |
|---|------|--------|------|------|--------|
| 9.1 | Theorem 9.1 | 2492-2539 | Theorem (16 行証明) | B∉𝒰 ⇒ contradiction (非巡回 p-element via Thm 6.2) | **main** |
| 9.2 | Corollary 9.2 | 2541-2543 | Corollary (3 行証明) | L∈𝒰, K⊆C_G(L), r(K)≥2 ⇒ K∈𝒰 | **core** |
| 9.3 | Corollary 9.3 | 2545-2553 | Corollary (9 行証明) | A∈𝒰 abelian, m(A)≥3, r_p(C_G(B))≥3 ⇒ B∈𝒰 | **cascading** |
| 9.4 | Lemma 9.4 | 2555-2557 | Lemma (3 行証明) | r_p(F(M))≥3 ⇒ (abelian p-group rank ≥3) ⊆ 𝒰 | **supporting** |
| 9.5 | Lemma 9.5 | 2559-2625 | Lemma (67 行証明) | A∈SCN_3(p) ⇒ A∈𝒰 (contra. on r(F(M))) | **pivotal** |
| 9.6 | Theorem 9.6 | 2627-2629 | Theorem (3 行証明，**§9 の結論**) | r(K)≥2, r(K)≥3 or r(C_G(K))≥3 ⇒ K∈𝒰 | **MAIN RESULT** |

**結果数確認**: grep で 6 個 (Theorem 9.1, Corollary 9.2, Corollary 9.3, Lemma 9.4, Lemma 9.5, Theorem 9.6).

---

## Uniqueness Theorem 本体（Theorem 9.6）

### 主張
```
Theorem 9.6 (The Uniqueness Theorem)
Suppose K ⊆ G, r(K) ≥ 2. Assume r(K) ≥ 3 or r(C_G(K)) ≥ 3.
Then K ∈ 𝒰.

In particular, if A ∈ ℰ²(G) - ℰ*(G), then A ∈ 𝒰.
```

### 解説

**𝒰 の定義** (§8, Theorem 8.1 の仕様): G の部分群 K に対して、M(K) = {K に含まれる M ∈ ℳ} が唯一つであるとき K ∈ 𝒰. ℳ は最小反例 G の **maximal subgroup 全体**.

**意味**: 「rank ≥ 2 で（かつ rank ≥ 3 か centralizer が rank ≥ 3）である任意の部分群 K は、G の maximal subgroup の族 ℳ の中で**一意的に確定される**」。すなわち、K を含む maximal subgroup が必ず存在し、その個数は 1 つに決まる。

**特殊例**: A が 𝒰 の補集合 ℰ*(G) に属さない要素 elementary abelian 2-group なら A ∈ 𝒰 （＝ rank 2 要素も多くの場合 𝒰 に属する）。

### 証明スケッチ

```
証明: Thm 9.6
  ┌─ Step 1: Corollary 9.2 で r(K) ≥ 3 の場合に帰着
  │         (r(K) = 2 and r(C_G(K)) ≥ 3 のケースを処理)
  │
  └─ Step 2: r_p(K) ≥ 3 なる素数 p で B ∈ ℰ_p³(K) を取る
       ↓
       Lemma 5.1 → ∃A ∈ SCN₃(p) ⊆ N_G(P)  [P = Sylow p-subgroup ⊇ K]
       ↓
       Lemma 9.5 → A ∈ 𝒰
       ↓
       Corollary 9.3 → B ∈ 𝒰
       ↓
       K ∈ 𝒰  (K は B-orbit で characterize)
```

---

## Thm 6.2（normal-J）の引用箇所

### BG Theorem 6.2 の主張（§6 から recall）
```
Theorem 6.2:
G = solvable odd order, p ∈ π(G), S = Sylow p-subgroup.
⟹ Z(J(S))·O_{p'}(G) ⊴ G.
```

### §9 での引用（2 箇所）

#### 1. **Theorem 9.1 証明, L2511**
```
(line 2507-2512 in mmd)
By Theorem 6.2, O_{p'}(M)Z(J(P)) ⊴ M.
Therefore, by the Frattini argument,
  M = O_p'(M)Z(J(P))N_M(Z(J(P)) = O_p'(M)N_M(Z(J(P)).
```
**役割**: Fitting of M の構造から N_G(P) ⊆ M を導く（Eq. 9.3）。Thm 6.2 は M 内に normal structure を与える道具として使用。

#### 2. **Theorem 9.1 証明, L2515**
```
(line 2515 in mmd)
It follows that if O_{p'}(M) = 1, then
  N_G(P) ⊆ N_G(Z(J(P))) = M.
On the other hand, if O_{p'}(M) ≠ 1, then, by (9.1),
  N_G(P) normalizes O_{p'}(M) and hence
  N_G(P) ⊆ N_G(O_{p'}(M)) = M.
Thus, in both cases,  N_G(P) ⊆ M  ... (9.3).
```
**役割**: Thm 6.2 から得られた normalizer 情報を使って、2 つのケース（p' complement あり/なし）を統一的に処理。

### 文脈の重要性

§9 全体の戦略は以下の通り:

1. **Non-contradiction 仮定**: B ∉ 𝒰 と仮定して contradiction を導く.
2. **Thm 6.2 適用**: maximal subgroup M ∋ B に対して Thm 6.2 を使い M の normal structure を把握.
3. **Normalizer 計算**: Z(J(P)) や O_{p'}(M) の normalizer が M に含まれることを示す.
4. **Sylow p-subgroup 性**: これにより P が G の Sylow p-subgroup であることが確定.
5. **矛盾導出**: Frattini argument と Fitting subgroup の rank 制限により contradiction.

§9 では Thm 6.2 がなければ Step 2-3 が実行不可能なため、**§9 のコアは Thm 6.2 への依存**.

---

## central structure 概念

### 定義の implicit な出現箇所

§9 の証明全体で「central element」と「Sylow p-subgroup」の関係が繰り返し登場:

- **Z(J(P))**: Thompson J(P) の center. Thm 6.2 の "central structure" を表す.
- **O_{p'}(M)**: maximal p'-normal subgroup of M. p-length 1 条件と組み合わせて、M の solvable structure を決定.

### 𝒰 の characterization と central element

Thm 9.1-9.6 の chain では:

1. **central element による stabilization**: K ∈ 𝒰 ⟺「K を含む maximal subgroup M は K の中心元の作用で stabilize される」（暗黙）.
2. **rank 制限**: r(K) ≥ 2 および r(C_G(K)) ≥ 3 という**rank 条件**が、K を含む M が一意的に定まることを保証.
3. **SCN_3(p) の role**: abelian p-subgroup A ∈ SCN_3(p) は「p-length 1 をもつ任意 maximal subgroup で characterize」される（Lemma 9.5 の core）.

### "central structure" の形式化への示唆

Lean での実装では:

```lean
-- Pseudo-code
structure CentralJ (S : Sylow p G) where
  j_subgroup : S → Subgroup G
  z_center : S → Subgroup G  -- Z(J(S))
  normal_O_p' : ∀ M, M ∈ ℳ → O_p'(M) ⊴ M

theorem uniqueness_via_centralJ {K : Subgroup G} (hK : r K ≥ 2) 
    (hC : r K ≥ 3 ∨ r (centralizer K) ≥ 3) : K ∈ 𝒰 := ...
```

---

## §10-§16, App.C での被引用

### 直接引用

| 下流 | 引用場所 | 内容 |
|------|--------|------|
| §10 Thm 10.1, L2721 | Uniqueness Thm 9.6 | M_α の characterization: P ∈ 𝒰 ⇒ N(P) ⊆ M |
| §10 Lemma 10.4, L2697 | Thm 9.6 | r(P) ≥ 3 ⇒ P ∈ 𝒰 ⇒ maximal unique |
| §12 Lemma 12.17, L4182 | Corollary 9.2 | P ∈ 𝒰, r(O_{p'}(H)) ≥ 2 ⇒ O_{p'}(H) ∈ 𝒰 |
| §15 Thm 15.2, L4204 | Thm 9.6, Corollary 9.2 | q ∉ β(G) ⇒ M* of type 𝒫₁ |
| App.C, L5014 | Thm 9.6 (via 6.2) | Z(J(P)) の normalizer via Thm 6.2 |

### 構造的役割

**§9 → §10 gateway**:

- §9 で「任意 K with r(K) ≥ 2 が maximal 一個に contained」を確立.
- §10 で「maximal subgroup M に対して M_α (= Hall complement) + M_σ (= Frobenius kernel) を定義・分析」を開始.
- M_α, M_σ の existence/uniqueness が Thm 9.6 の「maximal の一意性」に基づいている（暗黙的）.

---

## Peterfalvi §10 への橋渡し

### Peterfalvi 本体での役割

Peterfalvi _Three Primes Divide the Orders of the Real Centralizers of 3-Central Elements_ (1986, updated 1984) §10 "Structure of Minimal Non-abelian Simple Group" では:

- **Hypothesis**: G = minimal non-abelian simple group of odd order.
- **Goal**: G の structure を制限し、最終矛盾に導く.
- **前提 (BG): Uniqueness Theorem** — rank ≥ 2 部分群が maximal subgroup 族の中で一意的に確定される事実.

BG App.C と Peterfalvi §10 は本質的に**同じ矛盾証明** (FT 1963 原論文 Ch.VI を両者が再構成)。

### クロスリファレンス

**BG における標記**: App.C (L4759-5005) では「Theorem C」として、**「𝓕 が Frobenius 族 {F_{p^q} : p ∈ π(𝓕)} の形ならば p ≤ q」** を述べる.

**Peterfalvi における対応**: 同様に、maximal subgroup の "generalized Frobenius" structure から、素数 p, q の大小関係を contradicting.

**Phase 2a での扱い**: Peterfalvi §9 （本来は Phase 2b） と並行で実装。ただし Uniqueness Theorem **必須** — Peterfalvi §10 はこれなしに着手不可.

---

## mathlib カバレッジ

| 概念 | mathlib 状況 | BG 実装 | 形式化優先順 |
|------|-------------|--------|------------|
| Sylow p-subgroup, Z(J(P)) | low | J(P) は Phase 1 Ch.7 で実装 | §6-§9 parallel with Ch.7 |
| SCN₃(p) (abelian p-group class) | **new** | BG 定義 (§5 Lemma 5.1) | 新規 API |
| 𝒰 (unique maximal set) | **new** | BG 定義 (§8 Thm 8.1) | 新規 typeclass or def |
| O_{p'}(G), O_{p,p'}(G) | **mid** | mathlib に O_p はあるが、p' notation は新規 | wrapper needed |
| Frattini argument | high | mathlib `Subgroup.frattiniSubgroup` | existing |
| Fitting subgroup F(G) | **mid** | Phase 1 Ch.2 で実装 | §8-§9 までに完了 |
| elementary abelian p-group | high | mathlib ℰ_p(G) | existing |
| Rank, m(A) (min gens) | **mid** | basic あり、BG 専用 rank functions 新規 | §4-§5 で実装 |
| p-length, narrow p-groups | **low** | Phase 1 Ch.7 で実装 | §5 完了必須 |

### 主な新規実装

1. **Uniqueness set 𝒰**:
```lean
def IsInUnicitySet (K : Subgroup G) : Prop :=
  ∃! M : Subgroup G, M ∈ maximalSubgroups G ∧ K ≤ M
```

2. **SCN₃ class**:
```lean
def IsSCN₃Subgroup (p : Nat) (A : Subgroup G) : Prop :=
  IsAbelian A ∧ (∀ p'-group, ...) ∧ (rank-related condition)
```

3. **central structure helper**:
```lean
def CentralJHelper (M : Subgroup G) : Subgroup G :=
  (O_p' M) ⊔ (Z (J (Sylow p M)))
```

---

## Phase 2a 形式化着手順

### 推奨 dependency 順

1. **§6 Theorem 6.2** (normal-J theorem) — **前提**. mmd L1969-2128.
2. **§7 Hypothesis 7.1 + Theorem 7.1-7.6** (Transitivity) — 参照的 use (Lemma 9.5 で Thm 7.4, 7.6 引用).
3. **§8 Theorem 8.1** (Fitting of maximal) — 𝒰 の定義源.
4. **§9 Theorem 9.1 → Corollary 9.2 → 9.3 → Lemma 9.4 → 9.5 → Theorem 9.6** — 線形チェーン.

### 証明負荷の評価

| 結果 | 行数 | 複雑度 | 見積 |
|------|------|--------|------|
| Thm 9.1 | 47 | **high** (Frattini x2, normalizer) | 2-3 days |
| Cor 9.2 | 3 | low | 2-3 hours |
| Cor 9.3 | 9 | **mid** (induction chain) | 3-4 hours |
| Lem 9.4 | 3 | low | 2-3 hours |
| Lem 9.5 | 67 | **very high** (contradiction x3, rank args) | 4-5 days |
| Thm 9.6 | 3 | low (corollary style) | 2-3 hours |

**Total**: 約 **7-10 days** (parallelizable with §8 後進).

### 着手準備チェックリスト

- [ ] **§6 Theorem 6.2** Lean form 確認 (normal-J).
- [ ] **§8 Theorem 8.1** 完成 (Fitting structure, 𝒰 定義).
- [ ] **Lemma 5.1** (SCN₃ existence) available.
- [ ] **Theorem 4.20** (p-group Fitting rank) available.
- [ ] **Corollary 4.19** (chief factor action) available.
- [ ] **Frattini argument** tactic/lemma in mathlib or BG.
- [ ] **Centralizer/Normalizer API** (Z(J(P)), N_G(Z(J(P)))) solid.

---

## 未解決 / TODO

### mmd/PDF 欠落

- **§6-§7 の境界** (L2128-2131): MISSING_PAGE_EMPTY:67. PDF p.67 を直接参照要.

### 概念的不明瞭

1. **SCN₃(p) の正確な定義**:
   - mmd L1821-1828 (§5 Lemma 5.1) では「S-conjugate-normal of rank 3」の記述.
   - Lean での characterization: abelian p-subgroup A が「あらゆる Sylow p-subgroup S に normal」かつ「m(A) = 3」か?

2. **ℰ*(G) の正確な補集合**:
   - Theorem 9.6 末尾「if A ∈ ℰ²(G) - ℰ*(G), then A ∈ 𝒰」.
   - ℰ*(G) の定義が mmd のどこに? (§8 Thm 8.1 前後を要確認).

3. **"central structure" の Lean encoding**:
   - Z(J(P))·O_{p'}(G) は multiplicative か normal product か?
   - BG では normal product ⊔ か canonical product なのか確認要.

### Peterfalvi との対応

- **App.C "Theorem C"** の statement と **Peterfalvi §10** の main result の exact correspondence を Phase 2b 着手時に確定.
- 両者の prime divisor argument が同じパターンなのか異なるのか.

### キャッシング・optimization 機会

- Lemma 9.5 の proof は 67 行の長い contradiction. sub-lemma で層別化できないか (reusable module).
- Corollary 9.2-9.3 の cascading logic を tactic framework で parametrize できるか.

---

## 参照 & リンク

- **概要**: `notes/bg/_overview.md` (§9 = Phase 2a 中盤, Thm 6.2 で多引用).
- **§8 ノート**: `notes/bg/s08_fitting.md` (§8 完了後に §9 着手).
- **§7 ノート**: `notes/bg/s07_transitivity.md` (Hypothesis 7.1, Thm 7.4-7.6 の参考).
- **§10 ノート**: `notes/bg/s10_m_alpha_sigma.md` (§9 後流, Thm 9.6 を引用).
- **Phase 2 cross-refs**: `notes/meta/phase2_cross_refs.md`.
- **Peterfalvi overview**: `notes/peterfalvi/_overview.md` (§10 via App.C).

---

**作成**: 2026-05-22.  
**出典**: `references/bg/local-analysis.mmd` (L2486-2630, 6 結果).  
**形式化予定**: Phase 2a 第 3 波（§8 完成後）.  
**本ノート確度**: ★★★★☆ (mmd full read, overview cross-check, §8-§10 context confirm).

---

## Lean API status (2026-06-02 lane B6)

Current Lean spine lives in `OddOrder/BG/Ch2_Uniqueness/S09_Uniqueness.lean`.

- §9 intentionally introduces no new local definitions: it consumes the shared `IsUniquelyMaximal`/`hInvariant` API, §7 `scn3Global`, and §8 `fittingInG`.
- Shared uniqueness API landed in `OddOrder/GroupTheory/MaximalSubgroup.lean`: `IsUniquelyMaximal.uniqueMaximalSubgroup`, its membership/coatom/le accessors, equality of maximal overgroups, and `maximalSubgroupsContaining_eq_singleton`.
- Shared `hInvariant`/`hInvariantStar` destructors landed in `OddOrder/GroupTheory/AInvariantPiSubgroups.lean`, so §9 proofs can project ambient containment, normalizer containment, pi-subgroup status, and star maximality without unfolding definitions by hand.
- Current remaining §9 theorem-body `sorry`s are exactly Theorem 9.1, Corollary 9.3, Lemma 9.4, and Lemma 9.5. Corollary 9.2, Theorem 9.6, and the `E^2 - E*` particular case are now Lean-proved from their upstream stated theorems. The remaining hard proofs still depend on the §7/§8 chain, BG §6 Theorem 6.2, BG §4 rank/centralizer inputs, and the Lemma 9.5 SCN₃-to-𝒰 argument. No Blackburn/narrow classification or theorem-conclusion hypothesis was hoisted.


## Lean API status (2026-06-04)

S08 completion after `d1ecd4e` unlocked the §9 frontier. The first sorry-free §9 support
API is now in place:

- `IsUniquelyMaximal.of_le_of_lt_top` in `OddOrder/GroupTheory/MaximalSubgroup.lean`: if
  `H ∈ 𝒰`, `H ≤ K`, and `K < ⊤`, then `K ∈ 𝒰`. This is the general monotonicity step used
  after proving an elementary abelian subgroup of `K` belongs to `𝒰`.
- S09 local bridge `centralizer_singleton_le_uniqueMaximalSubgroup_of_mem_centralizer`: in a
  minimal simple odd group, if `x ≠ 1` centralizes `L ∈ 𝒰`, then `C_G(x)` lies in the unique
  maximal subgroup containing `L`. This is the Lean form of the Corollary 9.2 line
  `C_G(b) ⊇ L`, hence `C_G(b) ⊆ H`.

The PRank refinement is now landed: `rank` is indexed over `{p // p.Prime}`, and
`exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank` extracts a prime-indexed
noncyclic elementary abelian subgroup of `K` from `2 ≤ rank ↥K`, mapped back to the ambient
group. With this witness, Corollary 9.2 is now proved in Lean from Theorem 9.1: for
`A ≤ K ≤ C_G(L)`, every nontrivial `a ∈ A` has `C_G(a)` inside the unique maximal subgroup
containing `L`, so Theorem 9.1 gives `A ∈ 𝒰`, and `IsUniquelyMaximal.of_le_of_lt_top` lifts
from `A` to `K`.

Theorem 9.6 is now proved in Lean from the stated upstream §9 gates. The proof has three
local bridges:

- `scn3Global_of_scn3_sylow`: maps a local `SCN₃(P)` subgroup of a Sylow `p`-subgroup to
  `S07.scn3Global p G`.
- `centralizer_lt_top_of_two_le_rank`: proves `C_G(K) < ⊤` from `2 ≤ rank K` in a minimal
  simple odd group.
- `isUniquelyMaximal_of_three_le_rank_of_lt_top`: extracts a rank-three elementary abelian
  `B ≤ K`, uses BG Lemma 5.1 to choose `A ∈ SCN₃(P)`, applies Lemma 9.5 to put `A ∈ 𝒰`,
  then Corollary 9.3 and `IsUniquelyMaximal.of_le_of_lt_top` to lift from `B` to `K`.

Lean's `uniquenessTheorem` carries `K < ⊤` explicitly, because `IsUniquelyMaximal K` includes
properness. BG writes `K ⊆ G`; downstream uses of the theorem occur for proper local subgroups
or must supply that properness separately.

The `E^2 - E*` particular case is now proved in Lean from Theorem 9.6. The local bridge
`three_le_rank_centralizer_of_mem_e2_not_maximal` extracts a larger elementary abelian
`p`-subgroup from `¬ IsMaximalElementaryAbelian p A`, puts it inside `C_G(A)`, and converts
its strict cardinal growth over `|A| = p^2` into `3 ≤ rank C_G(A)`. Thus an `A ∈ E_p^2(G)`
that is not in `E*` satisfies the second rank alternative of Theorem 9.6.

Remaining §9 `sorry`s are now exactly Theorem 9.1, Corollary 9.3, Lemma 9.4, and Lemma 9.5.
Corollary 9.2 still depends on the stated Theorem 9.1 proof being completed. Theorem 9.6 and
the particular case now have no theorem-body `sorry`, but they still depend on the stated
Corollary 9.3 and Lemma 9.5 gates.
