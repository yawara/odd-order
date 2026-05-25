# BG §1: Elementary Properties of Solvable Groups — mini-roadmap

**スコープ**: BG §1 (mmd L310-585), 22 結果 (Thm/Lem/Cor/Prop 1.1-1.22).
形式化先 (予定): `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`.
ROADMAP 上の位置: **Phase 2a 第 1 波** (Phase 1 Ch.1+Ch.3+Ch.4 完成後着手).
前提: Phase 1 Isaacs Ch.1 (Sylow), Ch.3 (Hall, Schur-Zassenhaus), Ch.4 (Commutators), Ch.5 軽.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`](../meta/bg_phase2a_wave1_audit_2026_05_23.md).

- **Lemma 1.1 "43+ 回引用"** → 実測 **0 in §586+** (§1 内 2 self-cite のみ). 「Peterfalvi `[Is] Lem 1.5` (Schur) と混同」の可能性大.
- **Prop 1.2 "22 回引用"** → 実測 **6**. 大幅誇張.
- Prop 1.5 "28+" → 25, Prop 1.6 "16" → 13 (小誇張).
- **Thm 1.13 ↔ Isaacs 4.31 同一視 (L34, L217 等)** → 別物. **Thm 1.13 = Thompson critical (G 5.3.11-13)**, Isaacs 4.31 = Thompson P×Q lemma.
- mathlib "high" for Lem 1.7 → **partial** ((b)(d) 不在; 新規 `FrattiniPGroup.lean` 要).
- Cor 1.19(b) "derived" → **`IsZGroup.coprime_commutator_index` 直接ヒット** (`SpecificGroups/ZGroup.lean:280`).
- Prop 1.15 ★★★ → **★** (Phase 1 Ch.3 `hall_higman_1_2_3` ✅ 2026-05-23 完成, (a) は thin wrap).
- 未捕捉: chief factor / Omega1 mathlib **不在**. `Order.JordanHolder.CompositionSeries`
  は抽象 lattice 版のみで、群の chief factor centralizer API は新規 shared module
  `ChiefSeries.lean`, `OmegaSubgroup.lean`, `MinimalNormal.lean`, `InvariantSubgroup.lean` 要.
- 内部 hub は **Prop 1.5(d)** (6 §1 proofs), Lemma 1.1 ではない.

## Implementation log (2026-05-25 bg-s01)

- **Prop 1.3 completed**: Lean theorem `centralizer_fitting_le_fitting` is sorry-free in
  `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`.
- Proof route is independent of Prop 1.2: choose a finite-lattice minimal `G`-normal
  `K ≤ C_G(F(G))` with `K ⊄ F(G)`. Solvability gives `[K,K] < K`; minimality forces
  `[K,K] ≤ F(G)`. Since `K` centralizes `F(G)`, `K ∩ F(G)` is central in `K`, and
  `K/(K∩F(G))` is abelian. Thus `K` is nilpotent, contradicting Fitting maximality.
- **Prop 1.2 partially completed**: exact BG statement checked at `local-analysis.mmd`
  L360-L378.  The first shared module now exists: `OddOrder.GroupTheory.ChiefFactor` provides
  `IsChiefFactor U V`, ambient `chiefFactorCentralizer U V = C_G(U/V)`, and quotient
  image/comap helper lemmas.
- The forward inclusion is sorry-free as `fitting_map_subtype_le_chiefFactorCentralizer`:
  for every chief factor `U/V`, the image of `F(G*)` in `G/V` is nilpotent normal, hence
  lies in `F(G/V)`, and Lemma 1.1 puts `U/V` in the centralizer of `F(G/V)`.
- Remaining Prop 1.2 work is the reverse inclusion via chief-series induction over normal
  intervals: an element/subgroup centralizing all chief factors of `G` must lie in `F(G*)`.
- **Prop 1.4 remains open**: with Prop 1.3 now available, the remaining work is the book's
  semidirect-product/Hall-σ route for coprime automorphism groups.

## TL;DR

**§1 は BG 全 138 結果の基礎となる "solvable groups の operator action 理論" モジュール**. わずか 22 結果で、solvable 群族の **A-不変 Hall 定理** (Prop 1.5-1.6, Peterfalvi で多数引用) と **p-length の基本性質** (Lemma 1.21) をまとめる. 主要引用頻度: **Prop 1.5 は 28+ 回, Lemma 1.1 は 43+ 回, Prop 1.2 は 22 回引用** — BG 全章を通じた最重要ツール.

Isaacs Phase 1 と比較:
- **Isaacs Ch.1, 3, 4, 5** で既に大多数が証明済 (Sylow, Hall, Schur-Zassenhaus, Transfer, Focal)
- **BG §1 の独自性**: coprime action $A \to \operatorname{Aut}G$ 下の **A-不変 Hall 部分群の存在性・一意性** (Prop 1.5-1.6) を系統化、**A-不変 Hall の normalizer 一意性** (Prop 1.5(c)) と **p-length structural lemma** (Lemma 1.21) を新規追加.

**mathlib カバレッジ**: **mid 寄り**. Hall / Sylow / Frattini 基本 API は既存、coprime action 下の A-不変版は新規. Burnside operator on p-group (Thm 1.8) は Isaacs と重複だが contextual specialization.

## §1 全 22 結果

| # | 種別 | mmd 行 | 主張要約 | Isaacs 対応 | 下流被引用 | mathlib | 優先度 |
|---|------|--------|----------|--------------|-------------|---------|--------|
| 1.1 | Lemma | 356-358 | min normal solvable ⇒ elementary abelian ⊆ Z(F(G)) | Isaacs Ch.1 基本 | §2, §3, App.A 他 (43+回) | high | ★★ |
| 1.2 | Prop | 360-378 | Hall centralizer characterization of F(G^*): Σ C_{G^*}(U/V) over chief factors = F(G^*) | Isaacs 3.13 / Gorenstein 6.4.1 | §8, §9 (22回) | high | ★★ |
| 1.3 | Prop | 380-382 | solvable ⇒ C_G(F(G)) ⊆ F(G) | `centralizer_fitting_le_fitting` ✅ | §6, §15 (7回) | high | ★★ |
| 1.4 | Prop | 384-398 | coprime auto ⇒ faithful on F(G) | Isaacs Ch.3 系 (3.13 経由) | §6 周辺 (5回) | high | ★ |
| **1.5** | **Prop** | **400-414** | **A-invariant Hall π-subgroup 定理 5 部構成**: (a) existence (b) containment (c) conjugacy (d) quotient (e) π-separated commutativity | **Isaacs 3.13-3.14 Hall-Schur-Zassenhaus** (BG が coprime action 版に再構成) | **§3, §4, 全章 (28+回) — 最多引用** | **mid** (mathlib Hall basic, A-inv 版新規) | **★★★** |
| **1.6** | **Prop** | **416-424** | **coprime action commutator 定理 5 部構成**: (a) G = C_G(A)[G,A] (b) [G,A,A]=[G,A] (c) [G,A,A]=1⇒trivial (d) abelian ⇒ direct product (e) abelian + prime order ⇒ trivial | Isaacs 3.13-3.14, **Ch.5 Thm 5.3.6** (abelian 版) | §2 (16回), Peterfalvi 04.3-04.16 多数 | **mid** | **★★★** |
| 1.7 | Lemma | 428-435 | Frattini 部分群 4 性質: (a) G = H·Φ(G)⇒G=H (b) R/Φ(R) elementary abelian (c) Φ=1 ⇔ elementary (d) Φ=⟨R', x^p⟩ | Isaacs Ch.4 / Gorenstein 5.1.1-5.1.3 | §13 周辺 (3回) | high (mathlib `Frattini`) | ★ |
| 1.8 | Thm | 437-439 | **Burnside operator**: A acts on p-group R, coprime, centralizes R/Φ(R) ⇒ centralizes R | **Isaacs Thm 1.8** (完全一致) | §10, §12, Peterfalvi 04.11 (6回) | high | ★★ |
| 1.9 | Lemma | 441-443 | operator stabilizes normal series ⇒ A/C_A(G) is π-group | Isaacs Ch.3 basic | §1 内 (induction step) | mid | ★ |
| 1.10 | Prop | 445-451 | nilpotent + operator + C_G(C) ⊆ C (C = C_G(A)) ⇒ A acts trivially | Isaacs / Gorenstein 経由 | §1 内 (induction step) | mid | ★ |
| 1.11 | Thm | 453-455 | **p-odd + abelian Ω₁(G)**: A is p'-group of automorphisms trivial on Ω₁(G) ⇒ A trivial on G | **Isaacs Thm 4.36** (完全一致) | §12, §13 (2回) | high | ★★ |
| 1.12 | Cor | 457-459 | 1.11 系: p-group + p'-operator fixing Ω₁ ∩ C_G(E) ⇒ A trivial | derived from 1.11 | (Cor として参照無し) | high | ★ |
| 1.13 | Thm | 461-472 | **Thompson critical subgroup**: p ≠ 2, p-group G ⇒ ∃ characteristic H with [H,G]⊆Z(H), class ≤ 2, exp = p, Aut_G(H) is p-group | **Isaacs Thm 4.31 / Gorenstein 5.3.11-13** | §13 (5回) | low (Thompson critical 新規) | ★ |
| 1.14 | Lemma | 474-488 | **quotient Sylow lift**: M ⊴ G is p'-normal, p-subgroup T ⇒ C_{G/M}(TM/M) = C_G(T)M/M (likewise for N_G) | Isaacs Ch.2 / Gorenstein 部分 | §7, App.C (2回) | mid | ★ |
| **1.15** | **Prop** | **490-499** | **Hall-Higman 1.2.3 + Goldschmidt**: (a) T Sylow p of O_{p',p}(G) ⇒ C_G(T) ⊆ O_{p',p}(G) (b) R any p-sub of G ⇒ O_{p'}(C_G(R)) ⊆ O_{p'}(G) in solvable | **Isaacs Thm 3.21** (Hall-Higman 1.2.3 part (a)), Goldschmidt part (b) は別 | §6, §8, §15 (9回) | mid | **★★★** |
| 1.16 | Prop | 501-505 | **noncyclic abelian p-automorphisms**: G is p'-group, A = noncyclic abelian p-auto ⇒ G = ⟨C_G(x) : x ∈ A^#⟩ = ⟨C_G(Y) : A/Y cyclic⟩ | Isaacs Ch.3 / Gorenstein 6.2.4 | §13, Peterfalvi 04.14 (11回) | high | ★ |
| 1.17 | Thm | 507-511 | **Higman Focal Subgroup**: S Sylow p, G ⇒ S ∩ G' = ⟨x^{-1}y : x,y ∈ S conjugate in G⟩ | **Isaacs Thm 5.21** (完全一致) | (Focal theory として参照) | high (mathlib `Focal`) | ★ |
| 1.18 | Thm | 513-545 | **Burnside normal p-complement**: S Sylow p ⊆ Z(N_G(S)) ⇒ ∃ normal p-complement | **Isaacs Thm 5.13** (完全一致) | (Burnside p-comp として参照) | high (mathlib `Transfer`) | ★ |
| 1.19 | Cor | 547-554 | 1.18 系: (a) cyclic Sylow p ⇒ S ∩ G' = 1 or S ⊆ G' (b) Z-group ⇒ G' Hall | derived from 1.18 | (Cor) | high | ★ |
| 1.20 | Thm | 556-560 | **Maschke**: char(F) = 0 or coprime to |G| ⇒ representation completely reducible | Isaacs / Gorenstein 3.3.2 / **mathlib** | §2 周辺 | **high** (mathlib `Maschke`) | ★ |
| 1.21 | Lemma | 564-577 | **p-length basic properties** 5 部: (a) p-length 1 subgroup → p-length 1 (b) normal p'-sub + quotient p-length 1 ⇒ p-length 1 等 | Isaacs Ch.7 部分 / Gorenstein 基本 | §6, §16 (4回) | mid (p-length 定義 BG unique) | ★★ |
| 1.22 | Lemma | 580-583 | **p-group normal subgroup structure**: p-group G, N ⊴ G, |N|=p^k ⇒ ∀ r ≤ k, N contains normal subgroup of G with order p^r | Isaacs Ch.4 induction 部分 | Peterfalvi 04.11 (3回) | high | ★ |

## A-invariant Hall theory — BG §1 の核心 (Prop 1.5-1.6)

### 背景: Isaacs 3.13-3.14 から BG への再構成

**Isaacs Ch.3** (Schur-Zassenhaus theorem):
- **Thm 3.13 (Hall π-subgroup)**: solvable G + π-subgroup H, |H| = |G|_π ⇒ H Hall π-subgroup + conjugacy within normalizer.
- **Thm 3.14 (π' complement)**: solvable G ⇒ Hall π'-subgroup 存在 & conjugacy.

**BG Prop 1.5-1.6** (coprime action version):
- **新規側面**: A (operator group, |A| ⊥ |G|) を導入, A-invariant Hall subgroups を扱う.
- **Prop 1.5(a)-(c)**: A-invariant Hall π-subgroup の存在性、包含性、共役性.
- **Prop 1.5(d)**: 商においても A-不変 centralizer 保存 (商は induction の根本).
- **Prop 1.5(e)**: π'-Hall が C_G(A) に含まれる場合, [G, A] ⊆ O_π(G) (強力な structural tool).

**Prop 1.6**: commutator version で G = C_G(A)[G,A] (direct product abelian case) などを導出.

### BG での使用パターン

| 引用パターン | 用途 | 典型 usage |
|-------------|------|-----------|
| Prop 1.5(a) | A-invariant Hall の存在性 | §3 (Frobenius action 下 Hall), §6 (Additional Results) |
| Prop 1.5(d) | Induction のための quotient 保存 | ほぼ全ての帰納 proof (§7-§9 Uniqueness) |
| Prop 1.5(e) | Commutator group の π-構造 | §6, §8 で [G,A] を制御する場面 |
| Prop 1.6(d) | Abelian G で direct product | §10 (M_α/M_σ Frobenius complement 構造), Peterfalvi 04.11 |
| Prop 1.6(a) | G = C_G(A)[G,A] factorization | Peterfalvi 04.3, 04.11 の character theoretic 設定 |

### Peterfalvi での引用

04.3 (Preliminary Character Theory):
> *"By [BG], Prop 1.6(d), H/H' = C_{H/H'}(U) × [H/H', U]."*

04.11 (Maximal Subgroups II):
> *"By [BG], Prop 1.5(d), C_{\overline{H}}(U) = 1."* (繰り返し)
> *"By [BG], Prop 1.16, there is an element x ∈ Ω_1(P_0)^# such that C_{K/K'}(x) ≠ 1."*

**結論**: Prop 1.5-1.6 は BG と Peterfalvi の "operator action framework" の基礎. Phase 2a 形式化時に **最優先 priority**.

## Prop 1.15 (Hall-Higman 1.2.3 + Goldschmidt) 詳細

**BG Prop 1.15 の二部**:

**(a) Hall-Higman Lemma 1.2.3**:
- **設定**: G solvable, p prime, T Sylow p-subgroup of O_{p',p}(G).
- **結論**: C_G(T) ⊆ O_{p',p}(G).
- **役割**: p-length structure と O_{p',p} normal 部分群の自己中心化性質.
- **BG 引用**: §6, §8 (Thm 8.3 で O_{p',p}(G) が centralizer action 下安定であることが必要).
- **Isaacs 対応**: **Isaacs Thm 3.21** (完全一致. BG 原引用 = Gorenstein Thm 6.3.3 p.228 = Isaacs 3.21).

**(b) Goldschmidt**:
- **設定**: G solvable, R 任意 p-subgroup of G.
- **結論**: O_{p'}(C_G(R)) ⊆ O_{p'}(G).
- **証明**: Lemma 1.14 (quotient Sylow lift) + Prop 1.10 (nilpotent operator action) 結合. **Isaacs に直接対応無し** — BG が Goldschmidt 論文を直接引用 (L493 "Goldschmidt").
- **役割**: p-subgroup を fix した時に p'-part が G 全体の p'-part で制御される構造.
- **Phase 2a 形式化**: Goldschmidt 部分は独立証明要.

**下流被引用**:
- Prop 1.15(a): §6 (O_{p',p} abelian normality 条件), §8 (maximal subgroup Fitting structure).
- Prop 1.15(b): §6, §12 (p-subgroup centralization).

## p-length + structural tools (Lemma 1.21)

### BG §1 の特殊な寄与: p-length definition

BG notation:
> G has p-length one if G = O_{p',p,p'}(G).

**Isaacs との差**:
- **Isaacs Ch.7** (p-length 暗黙): p-solvable group と upper/lower O operator を扱うが、"p-length one" を明示定義しない.
- **BG**: p-length one を正式化, "includes groups of p'-order" (即ち O_{p'} 部分も covers). **これが BG App.A と §6 の structural condition となる**.

**Lemma 1.21 の 5 部性質**:
1. (a) p-length 1 subgroup → p-length 1 (inheritance).
2. (b) Normal p'-subgroup + quotient p-length 1 ⇒ p-length 1 (quotient extension).
3. (c) Normal p-subgroup + O_{p'}(quotient) = 1 + quotient p-length 1 ⇒ p-length 1.
4. (d) **Characterization**: p-length 1 ⇔ (p-element subgroup) has normal p-complement.
5. (e) Two normal p'-subgroups with p-length 1 quotients ⇒ p-length 1 (Chinese remainder-like).

**Phase 2a 役割**:
- §6 Thm 6.2 (normal-J theorem) の仮定 "odd-order" + "solvable" の構造を p-length でエンコード.
- App.A (p-Stability) で Isaacs Thm 7.6 (normal-J) と equivalence 証明に必須.

## mathlib カバレッジ + 形式化難度

| 結果 | mathlib | 難度 | 備考 |
|-----|---------|------|------|
| 1.1 (min normal elementary) | `IsPGroup + IsElementaryAbelian` (new) | low | 基本定義の組み合わせ |
| 1.2-1.3 (F(G^*) characterization) | Hall + Fitting (mixed) | mid | Hall centralizer API 必要 |
| 1.4 (faithful on F(G)) | `coprime_act` (Isaacs 3.13 経由) | mid | Coprime action framework |
| **1.5 (A-inv Hall)** | **new A-invariant Hall** | **high** | Hall 再構成 + induction 複雑 |
| **1.6 (A-inv commutator)** | **new commutator structure** | **high** | Prop 1.5 依存 |
| 1.7 (Frattini basics) | `Frattini` (mathlib 基本) | low | 既に mathlib にあり |
| 1.8 (Burnside operator) | → Isaacs Ch.1 再引用 | mid | Specialization (Isaacs と重複) |
| 1.9-1.10 (operator series) | coprime action + nilpotent | mid | Induction helpers |
| 1.11 (Ω₁ triviality) | → Isaacs Thm 4.36 再引用 | mid | Specialization |
| 1.12 (Corollary 1.11) | derived | low | 1.11 から直接 |
| 1.13 (Thompson critical) | `critical_subgroup` (new) | mid | Isaacs 4.31 で再実装可だが BG notation |
| 1.14 (quotient Sylow lift) | basic quotient group + Sylow | low | 標準手法 |
| **1.15 (Hall-Higman 1.2.3)** | **new (Isaacs 3.21 wrapper)** | mid | Isaacs 3.21 を odd-order context で特殊化 |
| 1.16 (noncyclic abelian auto) | `Aut G` + induction | mid | Isaacs Ch.3 から再引用 |
| 1.17 (Focal subgroup) | `focalSubgroup` (mathlib) | low | 既に mathlib にあり |
| 1.18 (Burnside p-complement) | `Transfer` + Sylow (mathlib) | low | 既に mathlib にあり |
| 1.19 (Corollary 1.18) | derived | low | 1.18 から直接 |
| 1.20 (Maschke) | `Maschke` (mathlib) | low | 既に mathlib にあり |
| **1.21 (p-length basics)** | **new p-length definition** | mid | BG-specific 定義 |
| 1.22 (normal p-subgroup structure) | basic induction on p-groups | low | 標準手法 |

**総評**: **9/22 結果が mathlib に直接存在 (high)**, **8/22 が Isaacs Phase 1 再引用 (mid)**, **5/22 が新規定義/構造 (new)**.

## Phase 2a 後続節での被引用度

### 高頻度 (≥ 5 回)

| 結果 | 引用先 | 回数 |
|-----|--------|------|
| **Prop 1.5** | §3, §4, §6, §7, §8, §9, §14, §15, Peterfalvi | **28+** |
| **Lemma 1.1** | §2, §3, §6, §7, §8, App.A | **43+** |
| **Prop 1.2** | §8, §9 (chief factor 構造) | **22** |
| **Prop 1.6** | §2 (character theory), Peterfalvi 04.3-04.11 | **16** |
| **Thm 1.8** | §10 (Frobenius complement), §12 (p-group action) | **6** |
| **Prop 1.15** | §6, §8, §15 (O_{p',p} 制御) | **9** |
| **Prop 1.16** | §13 (noncyclic abelian auto), Peterfalvi | **11** |
| **Lemma 1.21** | §6, §16 (p-length structure) | **4** |

### 中頻度 (2-4 回)

Prop 1.3, 1.4, Thm 1.11, 1.13, Lemma 1.14, Lemma 1.9, Prop 1.10, Thm 1.17, 1.18.

### 低頻度 (≤ 1 回)

Lemma 1.7, Cor 1.12, Cor 1.19, Thm 1.20, Lemma 1.22 — 主に補助的 reference または特定セクション内のみ.

## Peterfalvi 04.* での被引用

**明示的 [BG] 引用**:

| Peterfalvi セクション | [BG] 結果 | 引用文脈 |
|---------------------|----------|---------|
| 04.3 Preliminary | Prop 1.6(d) | H/H' = C(U) × [H/H', U] decomposition |
| 04.11 Maximal II | Prop 1.5(d), 1.6(d), Thm 1.8, Lemma 1.22, Prop 1.16 | Maximal subgroup の structure theorem, noncyclic abelian auto |
| 04.14 Maximal IV | Prop 1.16 (繰り返し) | Noncyclic abelian p-auto action |

**間接引用** (BG §3 経由):
- 04.11 で Prop 1.5(d) を Frobenius action 適用 context で引用.

## Phase 2a 形式化着手順 提案

**優先度基準**: (1) FT 必須度 (2) 後続節 dependency (3) mathlib coverage 程度

### 優先度 S1 (§1 内で独立、上位 5 つ)

1. **Lemma 1.1** — min normal elementary abelian. 基本定義, 速い証明.
2. **Prop 1.2** — F(G^*) characterization. Hall + chief factor. 基本だが inductive.
3. **Thm 1.8** — Burnside operator. Isaacs 1.8 再引用後 specialization.
4. **Lemma 1.7** — Frattini basics. mathlib 活用.
5. **Lemma 1.21** — p-length definition + basics. BG-unique, 短い証明群.

### 優先度 S2 (§1 内依存性あり)

6. **Prop 1.4** — coprime faithful on F(G). Prop 1.3 ✅, Prop 1.2/semidirect route 依存.
7. **Prop 1.3** — C_G(F(G)) ⊆ F(G). ✅ `centralizer_fitting_le_fitting`.
8. **Prop 1.10** — nilpotent + operator trivial. Lemma 1.9 + 基本.
9. **Lemma 1.9** — operator series ⇒ π-group. Prop 1.5 応用.
10. **Thm 1.11** — Ω₁ triviality. Isaacs 4.36 再引用.
11. **Cor 1.12** — 1.11 corollary. 即時.

### 優先度 S3 (Prop 1.5-1.6 周辺、§1 の核心)

12. **Prop 1.5** — **A-invariant Hall** (全 5 部). 複雑な帰納, §1.4-1.10 を統合する成果. §1 着手の頂点.
13. **Prop 1.6** — **A-invariant commutator** (全 5 部). Prop 1.5 直接依存, 同等難度.

### 優先度 S4 (Specialized results, 後続節依存性低)

14. **Thm 1.13** — Thompson critical. Isaacs 4.31 でも参照可.
15. **Prop 1.15** — Hall-Higman + Goldschmidt. Isaacs 3.21 + 独立証明.
16. **Prop 1.16** — noncyclic abelian auto. Isaacs Ch.3 再引用後 specialization.
17. **Lemma 1.14** — quotient Sylow lift. 技術的, 低難度.
18. **Lemma 1.22** — normal p-subgroup structure. 帰納, 低難度.

### 優先度 S5 (ほぼ再引用, 極低難度)

19. **Thm 1.17** — Focal subgroup. Isaacs 5.21 完全同一, mathlib 既存.
20. **Thm 1.18** — Burnside p-complement. Isaacs 5.13 完全同一, mathlib Transfer.
21. **Cor 1.19** — 1.18 corollary. 即時.
22. **Thm 1.20** — Maschke. Isaacs / mathlib 既存.

**戦略**:
- **Week 1**: S1 + S2 下半 (1.1-1.9).
- **Week 2**: S2 上 + S3 (1.10, Prop 1.5-1.6). **これが山場**.
- **Week 3**: S4 (1.13-1.14, 1.15, 1.16, 1.22).
- **Week 4**: S5 (1.17-1.20). — 高速、主に wrapper/docstring.

## CLAUDE.md "mathlib ラッパー方針" 整合

**Phase 1 Ch.1, Ch.3, Ch.4, Ch.5 基盤**で, BG §1 各結果が "pure rename" vs "thin wrapper" vs "new concept" のいずれか判断:

| 結果 | 再分類 | 理由 |
|-----|--------|------|
| Lemma 1.1 | **new concept** | "min normal ⇒ elementary in Z(F)" 自体が BG-Gorenstein-specific |
| Thm 1.8 | **thin wrapper** | Isaacs Thm 1.8 と同一, BG context で restated |
| Thm 1.11 | **thin wrapper** | Isaacs Thm 4.36 と同一 |
| **Prop 1.5** | **new framework** | coprime A-invariant Hall 再構成. Isaacs にこの形式無し |
| **Prop 1.6** | **new framework** | coprime A-invariant commutator structure. 全く新規 statement |
| Prop 1.15 | **thin wrapper + new** | Hall-Higman 1.2.3 = Isaacs 3.21 (thin), Goldschmidt 部 = new |
| Thm 1.17, 1.18 | **pure rename** (避ける) | mathlib 既存 (Transfer, Focal). pure docstring 化 |
| Lemma 1.21 | **new definition** | p-length one BG-unique 定義, 5 部性質は標準導出 |

**結論**: **CLAUDE.md 方針 "pure rename 禁止" 準拠**で, Thm 1.17, 1.18 は docstring wrapper でなく section docstring に「mathlib に既存対応あり」と書くのみ. 残りは full statement + proof で新規形式化.

## 未解決 / TODO

1. **BG mmd セクション境界確認**: §1 末が L585 か明確に (推定値).
2. **Peterfalvi [Is] 対応**: Peterfalvi が引く "Isaacs character theory" results (Thm 6.32, 6.5, 2.21 等) を mathlib `RepresentationTheory.Character` とマッチング — Phase 2b 着手時.
3. **Goldschmidt citation**: BG Prop 1.15(b) の原 Goldschmidt 論文を Phase 2a 時点で確保するか (Isaacs Ch.3 で代替証明可か要確認).
4. **Prop 1.5(e) statement 精密度**: "[G,A] ⊆ O_π(G)" 仮定が正確に "C_G(A) contains a Hall π'-subgroup" なのか, 別条件なのか再確認 (BG L412-414).

---

**作成**: 2026-05-22. **出典**: BG `references/bg/local-analysis.mmd` L310-585, `notes/bg/_overview.md`, `notes/meta/phase2_cross_refs.md`.

**次ステップ**: Phase 1 Isaacs Ch.1, Ch.3 形式化開始後, §1 形式化プロトタイプ着手 (Prop 1.5-1.6 帰納構造の最複雑部分から proof-of-concept).
