# Peterfalvi §10–§16 — scaffold feasibility 調査・統合 (2026-06-01)

**目的**: Peterfalvi 後半 §10–§16 (= FT 指標理論の apex、最終矛盾まで) の Lean 雛形化 (= 定義は filled-in な real def、定理は faithful な statement + `sorry`、**true-stub 不可**) の実現可能性を per-section で評価。
**方法**: §10–§12 と §13–§16 の 2 並列調査エージェント出力を統合。各 agent は mmd 全文 (`04.10`–`04.16`)、既存 notes、house style (`S09_NonexistenceCertain.lean`)、既存 Lean infra (BG `IsMinimalSimpleOdd`/`fittingInG`、GroupTheory foundation、Peterfalvi `S03`/`S04`/`S07`/`S08` Dade/coherence 層) を実測。
**統合元**: 2 survey reports + BG plan `notes/bg/scaffold_feasibility_2026_06_01.md` + 実 repo 監査 (本 session)。

---

## 核心発見 — 「各 section 独立に雛形化」は faithful には不可。foundation-first 必須

Peterfalvi §10 は本書後半全体で固定する **「奇数位数の極小単純群 G」** を fix する。これは **`OddOrder.BG.IsMinimalSimpleOdd G` と同一の G** (BG `Ch2_Uniqueness/Setup.lean` で確認)。§11–§16 はこの G の **極大部分群の Type 分類塔** の上に建つ:

```
§10 : M_F (nilpotent normal Hall) + type 𝓕/I/𝓟/II/III/IV/V + Ms + A₁/A/A₀ + 「supports」/Ã
       + 構造定理 (8.8 dichotomy)/(8.11)/(8.12)/(8.13)
§11 : Hyp 9.2/9.5 + 𝒮(Y)/𝒳(Y) char-set 族 + Wielandt fixed-point (9.1)
§12 : Hyp 10.1/10.4 + α_{ij}  → (10.7)[S,S]Frobenius / (10.8)𝒮 not coherent / (10.10) Type V 排除
§13 : Hyp 11.2 + 𝒮(X)        → (11.6)/(11.7) H elem-ab + (11.8)/(11.9) 指標直交
§14 : Hyp 12.1/12.8          → (12.7) Type I は Frobenius (headline) + (12.17) → (8.8) case (b)
§15 : Hyp 13.1 (S,T setup, 最大structure ~25 fields) + ω/η/μ/ν 指標族 → (13.12) c=1 / (13.16)/(13.17)
§16 : Hyp 14.1/14.3/14.10/14.13 + G₀  → (14.2) 有限体構造 → 最終矛盾 (BG App.C で閉じる)
```

このうち faithful な scaffold を阻む **3 つの global gate** が全 Tier 分類を支配する:

### Global gate #1 — §10 Type 分類塔 (**最重要・唯一の今すぐ高価値ファイル**)
`PeterfalviType` (= `IsTypeF`/`IsTypeI`/`IsTypeP`/`IsTypeII/III/IV/V`) は §11–§16 の全 hypothesis structure が "M of Type III/IV"、"S Type II"、"L Type I" として参照する。**Lean に一切存在しない**。これが #1 gate。**ただし §10 自身の定義塔は今すぐ Tier B で書ける** (後述 foundation 節) — これが §10–§16 で唯一「意味のある今すぐ書けるファイル」。§11–§16 を §10 完成前に書くと型仮定を opaque `Prop` placeholder にせざるを得ず、faithful でない。

### Global gate #2 — `M_F` (nilpotent normal Hall) — BG §15 と Pf §10 が共有する唯一の foundation gap
`M_F` = M の極大 nilpotent normal Hall 部分群。§10 冒頭で定義、§10–§16 の全結果が `H = M_F` を使う。**repo に存在しない**。`fittingInG` (BG `Ch2/S08`) は G への plain Fitting 埋込であり **`M_F` ではない** (両 report 一致確認)。**今すぐ encodable** (nilpotent+normal+Hall 部分群の `sSup`; existence/uniqueness は BG §15 Thm 15.2 = `sorry`-backed lemma)。BG plan note も §15 を「`MFitting` def のみ今書ける」と分類しており、**両書の同一対象** → 共有 module 化すべき。

### Global gate #3 — 指標 index 族 `ω_{ij}`/`η_{ij}`/`μ_{ij}`/`ν_{ij}` + `σ`/`τ₁`/`ρ`
Peterfalvi (3.2)/(3.3) の `ω_{ij}`、`η_{ij}=ω_{ij}^τ`、(4.3) の `μ_{ij}`/`ν_{ij}`、補助写像 `σ`/`τ₁`/`ρ` は §13/§15/§16 が総和を取る doubly-indexed grid。**`S03`/`S04` に named object として未材料化** (S03 は `characterTableEntry`・`σ: Equiv.Perm`・`IrreducibleCharacter` 型はあるが indexed `(i,j) ↦ ω_{ij}` grid は無い)。statement が `ω/η/μ/ν` を含む結果は全てこれが存在するまで Tier C。norm-cascade 系 ((13.5)–(13.10),(13.18), (14.11.x), §13 (11.8)) がこれに当たる。

### Global gate #4 (BG dependency) — BG Theorem A–E + App.C が **未 scaffold**
§10 (8.8)/(8.11)/(8.12)/(8.13) は **BG Thm A/B/I/II + Prop 16.1** を引く。これらは repo に無い (BG Ch3 は `S10`/`S11`/`S12` のみ、`Ch4_*` 不在 = 本 session 監査確認)。BG plan note も BG §16 を **Tier C apex (§10–§15 待ち)** と分類。さらに **§16 の最終 G-非存在は BG App.C Theorem C** (`(14.2)(a)(b) ⇒ p≤q`、`q<p` と矛盾) を明示的に引くが、**App.C は Lean ファイルが全く無い**。

**faithful な道筋 = foundation-first**: (1) `M_F` + §10 Type 分類塔を共有 module + S10 ファイルに埋める → (2) §11–§16 の hypothesis structure と standalone 算術補題のみ書く → (3) BG Thm A–E / App.C と §3–§8 指標族が整うまで §11–§16 の定理本体は `-- TODO` で保留。memory `scaffold-sorry-free-not-done` の anti-pattern (hard content を自由変数仮説に hoist) を避ける。

---

## per-section feasibility 一覧

Tier: **A** = 今すぐ faithful に書ける (参照対象が既存、群構造不要の算術 or 既存 infra のみ) / **B** = その section 自身の新 def (= §10 type塔/`M_F`) を埋めれば書ける / **C** = 他の未構築対象 (BG Thm A–E/App.C・§10 type塔・指標族 `ω/μ`・Dade/coherence numerics) に依存。

| § | 題 | 結果数 | Tier 内訳 | 今すぐ section file? | 主ブロッカー |
|---|---|---|---|---|---|
| **10** | Structure of Minimal Simple G | **15** (8.1–8.18; 8.14–8.17 は mmd 欠落) | **B~12, C~5** | **YES (最高価値)** | def 塔 (type 𝓕/I/𝓟/II–V + Ms + A₁/A/A₀) は今書ける。構造定理 (8.8)/(8.11)/(8.12)/(8.13) statement は writable, proof は **BG Thm A–E** 待ち |
| **11** | Maximal II/III/IV | **11** (9.1–9.11) | A~1, B~3, C~7 | 部分 (§10 後に充実) | **(9.1) Wielandt は今すぐ Tier A**。Hyp 9.2/9.5 + 𝒮(Y) 族は §10 後 Tier B。(9.3)–(9.11) は §10 type + 指標族 + Clifford/coherence |
| **12** | Maximal III/IV/V | **11** (10.1–10.11) | A~0, B~3, C~8 | 不可 (最 downstream of 三者) | Hyp 10.1/10.4/α_{ij} は §10+§4 Dade 後 Tier B。全定理 (10.2)–(10.11) は BG A–E + §11/§9 char numerics。**(10.8) は (7.5)/(7.8.b) が既存** で最も provable に近い |
| **13** | Maximal III/IV | **9** (11.1–11.9 + 11.8.x) | **A~1**, B~3, C~5 | 部分 | **(11.1) `p^q>4q²+1` は今すぐ Tier A (証明も可)**。Hyp 11.2 + (11.5)/(11.6)/(11.7) は §10 後 Tier B (群論のみ)。指標直交 (11.3)/(11.4)/(11.8)/(11.9) は `𝒮/ω/μ`+§10/§12 |
| **14** | Maximal I | **17** (12.1–12.17) | A~0–1, B~3, C~13 | 部分 | headline **(12.7) Type I は Frobenius** の statement は §10 後 writable。(12.6)/(12.9) も。(12.17)→既存 `S09` (7.11) に配線可。残は Dade cascade + BG Thm 2.6(a)/Prop 1.16 |
| **15** | Subgroups S and T | **19** (13.1–13.19) | **A~1**, B~3, C~14 | 部分 (最大・最深) | **(13.14) cyclotomic 数論は今すぐ Tier A (証明も可)**。最大 `Hypothesis131` structure (~25 fields, ω/η/μ/ν を field 化) + (13.2.b/c)/(13.12)/(13.16) statement は §10+`M_F` 後。残は norm cascade + BG Lem 3.2/Prop 3.9 |
| **16** | Non-existence of G (apex) | **11** (14.1–14.17, nested) | A~1, B~4, C~15 | 不可 (FT 完成点) | **(14.8.a) `q^{p+1}>p^{q+1}` は今すぐ Tier A (証明も可)**。Hyp 14.1/14.3/14.10/14.13 + `G₀` def + (14.2.b) statement は §15 後。**最終矛盾は BG App.C Thm C 待ち (Lean 無)** |

**全体**: 約 **60 numbered results 中 ~47 が Tier C** (apex 指標算術 + type 分類 + 最終矛盾)。残 ~13 の Tier A/B (数論補題・Frobenius/coherence statement・hypothesis bundle・構造的結論) が各ファイルを「filled def + faithful sorry-statement」の real scaffold にする。

---

## 今すぐ埋められる foundation 定義 (encodable now、open problem 無し)

### (1) 新規共有 module (BG §15/§16 と Peterfalvi §10 横断で再利用)

| 定義 | 内容 | 提案 Lean signature | 置き場所 | 備考 |
|---|---|---|---|---|
| **`maxNilpotentNormalHall` (`M_F`)** | M の極大 nilpotent normal Hall | `def maxNilpotentNormalHall (M : Subgroup G) : Subgroup G := sSup {N | N ≤ M ∧ (N.subgroupOf M).Normal ∧ Subgroup.IsNilpotent (N.subgroupOf M) ∧ IsHallSubgroup (Nat.card N).primeFactors (N.subgroupOf M)}` | **new** `OddOrder/GroupTheory/MaxNilpotentNormalHall.lean` | **keystone gap**。BG §15 と Pf §10–§16 が共有。existence/uniqueness (= sSup が自身 nilpotent-normal-Hall) は BG §15 Thm 15.2 = `sorry`-backed lemma。`fittingInG` は別物 |
| **`MaximalSubgroupType` 塔** | `IsTypeF`/`IsTypeI`/`IsTypeP`/`IsTypeII/III/IV/V` (下記§10詳細) + `Ms` + `A₁`/`A`/`A₀` + `PeterfalviType` inductive + `typeOf` discriminator | `structure IsTypeF (M : Subgroup G) : Prop where …` 他 (§10 表参照) | **new** `OddOrder/GroupTheory/MaximalSubgroupType.lean` (**BG §16 Type I–V と共有**) | BG↔Pf 同一分類 (下記)。Pf の plain-derived-series 形を base にし、BG が σ/κ を上に接続 |

### (2) 既存で直接再利用 (新規不要、両 report 一致確認)

- **固定 G**: `OddOrder.BG.IsMinimalSimpleOdd G` — Pf §10「奇数位数極小単純群」と同一。`(hG : IsMinimalSimpleOdd G)` を BG §10–§12 と同様に thread する。**再定義しない**。
- **type 𝓟 の `V`-normalizer 条件は既存 `Peterfalvi.S05.TICyclicHypothesis` と同型** (`W=W₁×W₂` cyclic + `IsTISubset V W` を既に bundle) → この設計を reuse。
- **群論 infra**: `Isaacs.Ch06.IsFrobeniusGroup N A` / `Isaacs.Ch03.IsHallSubgroup π H` / `Subgroup.IsComplement'` + `SemidirectProduct ⋊[φ]` / `GroupTheory.TISubset.IsTISubset` / `GroupTheory.ChiefFactor.IsChiefFactor` / `GroupTheory.ZGroup.IsZGroup` / `GroupTheory.MaximalSubgroup.{maximalSubgroups, IsUniquelyMaximal, maximalSubgroupsContaining}` / `GroupTheory.PRank.{pRank, rank}` / `GroupTheory.ElementaryAbelian(Family)` / `GroupTheory.ConjClassSet.conjClassSet` / `GroupTheory.IsExtraspecial` / `GroupTheory.OmegaSubgroup` / `Monoid.exponent` / BG `Ch2.S07.opiCoreInG` (= `O_π` in G, `Msigma`/`Malpha` で実績) / `AInvariantPiSubgroups`。
- **指標・Dade/coherence 層** (`S03`/`S04`/`S06`/`S07`/`S08` は §7 まで sorry-free): `RepresentationTheory.ClassFunction` (+`.inner`/`.innerSum`/`.induce`/`.IsReal`) / `ZIrr` (+`mem_ZIrr`/`ZIrrFourier`) / `InducedCharacter` / `Inertia.inertia θ` (= 慣性群 `I(θ)`) / `Clifford` / `IsReal` / `Peterfalvi.S04.{Hypothesis, DadeMap, IsDadeMap, IsDadeIsometry, SupportedClassFunctions, dadeSupport, sharp, centralizerIn}` / `Peterfalvi.S06.Hypothesis (4.6)` / `Peterfalvi.S07.{IsCoherent, IntegralCharacterMap}` + `S08` coherence 定理。
- **§14→§16 の実在 hook**: `Peterfalvi.S09.Hypothesis71` (= Hyp 7.1、`ρ` map) と `S09` の (7.5)/(7.8)/(7.11) は **既に statement 化済 (一部 sorry-free)**。(12.17)/(10.8)/(14.x) はこれに配線する。
- **有限体**: `§16 (14.2)` の `𝔽_{p^q}` は mathlib `GaloisField` で構成可。

### (3) 今すぐ書ける standalone 算術補題 (群構造不要、Tier A、証明も今できる)

これらは §10 type 塔・指標族・BG いずれにも依存せず、**FILL (証明まで) できる高価値の独立補題**:

| Pf# | 名前 | statement | 置き場所 |
|---|---|---|---|
| (11.1) | `pow_gt_four_sq_add_one_of_odd_primes` | p,q 奇素数, p≠q ⇒ `p^q > 4q²+1` | §13 ファイル (純 `Nat` 帰納) |
| (13.14) | `geom_sum_div_facts` | `(p^q−1)/(p−1)` odd; `p≡1 (q) ⇒ q∣…`; else `p−1` と coprime + 約数 `≡1 (q)` | §15 ファイル (純数論, `Nat.ModEq`/幾何和) |
| (14.8.a) | `q_pow_gt_p_pow` | p,q 奇素数 q<p ⇒ `q^{p+1} > p^{q+1}` | §16 ファイル (`Real.log x/(x+1)` 単調減少) |
| (9.1) | `wielandt_frobenius_fixedpoint` | `U⋊E` Frobenius が solvable H に coprime 作用 ⇒ `|C_H(UE)|^{|E|}|H|=|C_H(E)|^{|E|}|C_H(U)|` | **`OddOrder/GroupTheory/CoprimeAction.lean`** に昇格 (証明は Wielandt = `[HB]XI.12.4`、mathlib 欠 ⇒ statement のみ今、`sorry`) |

(9.1) は群論だが §10/BG/Dade 非依存で **FT 全体で再利用価値** → `CoprimeAction.lean` 共有を推奨。(11.1)/(13.14)/(14.8.a) は純算術で **証明まで今できる** — 各 section ファイルに「本当に proved な 1 補題」を置けるので scaffold が true-stub でない証拠になる。

---

## BG ↔ Peterfalvi 依存 (どの BG 結果が Pf を feed するか)

### Pf §10–§16 が消費する BG 結果 (= **全て未 scaffold**, BG Ch4/App.C 不在)

| Pf 結果 | 引く BG | 状態 |
|---|---|---|
| (8.8) dichotomy | BG **Thm I / Prop 16.1 / Thm B / Thm C(3)** | BG §16 未 (Tier C apex) |
| (8.11) | BG **Prop 16.1 + Thm A(1)** (M_σ-as-Hall) | 未 |
| (8.12) | BG **Thm B** | 未 |
| (8.13) | BG **Thm II + Thm B(5) + Thm D(4)** | 未 |
| §14 (12.12) | BG **Thm 2.6(a)** (complement cyclic, `e∣p±1`) | BG §2 = `Ch1/S02_Representations.lean` は skeleton; statement 化要 |
| §14 (12.9) / §16 (14.6) | BG **Prop 1.16 + Lem 1.14** | BG §1 (`Ch1_Preliminary`) — 要在庫確認 |
| §15 (13.16) | BG **Lem 3.2** | BG §3 (`Ch1/S03_FrobeniusActions.lean`) — 要在庫確認 |
| §15 (13.17) | BG **Prop 3.9** | 同上 (`S03_FrobeniusActions` に存在見込) |
| **§16 最終矛盾** | BG **Appendix C Theorem C** (`(14.2)(a)(b) ⇒ p≤q`) | **Lean ファイル皆無 = keystone 欠** |

### Types I–V を BG/Pf 共有 module にできるか → **YES (両書同一分類)**

第 1 report (§13–§16 担当) が BG `local-analysis.mmd` L4330–4350 と Pf 04.10 (8.1)–(8.7) を突合し、**同一分類**と確定:

| Pf §10 | BG §16 | 同一? | encoding note |
|---|---|---|---|
| type 𝓕 (8.1) | Type I 内の Frobenius 条件 Ii–Iv | yes (Pf が名前付き block に factor out, BG は inline) | Pf 形が clean → `IsTypeF` を一度定義し両方で reuse |
| Type I (8.3) | Type I (L4330) | **identical** (TI / rank-2 / cyclic `O_{p'}` の trichotomy) | BG: "our defs a little more explicit than FT"; Pf §10 = FT-IV 形 |
| type 𝓟 (8.4) | `ℳ_𝒫` membership | same derived-series data (M′,M″,W₁,W₂,V) | Pf は plain M′/M″; BG は σ/κ/`M_σ` を Prop 16.1 で追加接続 |
| Type II/III/IV (8.6) | Type II/III/IV | same (U abelian? / `N_G(U)⊆M`?) | — |
| Type V (8.7) | Type V | same (U=1 + TI/`p−1`/`p³` trichotomy) | — |

**結論**: 共有 module `OddOrder/GroupTheory/MaximalSubgroupType.lean` を **Pf の plain-derived-series 形で build** する (Pf §10 は `M_σ` 不要)。BG §16 は自身の `M_σ`/`ℳ_𝒫ᵢ` を Prop 16.1 経由でこれに接続 (deferred)。これで未構築の BG σ/κ 塔を Pf scaffold に強制せずに済む。**naming は BG §16 scaffold 担当と調整必須**。

---

## §10 詳細 — 定義塔 (今すぐ書ける高価値ファイル)

### A. 定義 (全て Tier B = `M_F` が入れば今 compile、共有 module へ)

| name | math 意味 | encodable now? |
|---|---|---|
| `IsTypeF` (8.1) | M=H⋊U solvable, H=M_F≠1≠U complement; ∃ abelian U₁◁U, `C_U(x)≤U₁ ∀x∈H#`; ∃U₀≤U, `exp U₀=exp U`, HU₀ Frobenius kernel H | **B**: `IsComplement'`/`IsFrobeniusGroup`/`Monoid.exponent`/centralizer 全在。`M_F` 依存。HU₀ 部分群 glue は fragile なら docstring defer |
| `IsTypeP` (8.4) | cyclic Hall W₁, M=M′⋊W₁; nilpotent U◁M′, M′=H⋊U; H non-cyclic, `M″⊆HC_M(H)=F(M)⊂M′`; cyclic W₂≤H∩M″, `C_{M′}(x)=W₂ ∀x∈W₁#`; V=W−(W₁∪W₂), `N_G(X)=W ∀∅≠X⊆V` | **B**: `commutator`/`derivedSeries`/`IsZGroup`/`normalizer(·:Set G)` 在。**`V`-normalizer 条件は `S05.TICyclicHypothesis` 設計を reuse** |
| `IsTypeI` (8.3) | `IsTypeF M ∧ (IsTI(M_F) ∨ (IsCommutative ∧ rank=2) ∨ (∀p∣\|H\|, exp U∣p−1) ∧ (∃p, O_{p'}(M) cyclic))` | **B**: `IsTISubset`/`rank`/`opiCoreInG` 在。**caveat**: Pf "rank 2" = cyclic 直積因子数; 該当 abelian 群では `rank`/`pRank`-sum と一致 — docstring に注記 |
| `IsTypeII/III/IV` (8.6) | `IsTypeP M ∧ U≠1 ∧ \|W₁\| prime ∧ F(M)# TI ∧` (II: U abelian, `N_G(U)⊄M`, M′ type𝓕; III: U abelian, `N_G(U)⊆M`; IV: U non-abelian, `N_G(U)⊆M`) | **B** (IsTypeP 後) |
| `IsTypeV` (8.7) | `IsTypeP M ∧ U=⊥ ∧ (H# TI ∨ (\|W₁\|∣p−1, O_{p'}(H) cyclic) ∨ (\|O_p(H)\|=p³, \|W₁\|∣p+1, O_{p'}(H) cyclic))` | **B** |
| `PeterfalviType` + `typeOf` | type discriminator (inductive + classifier) | **B** (Classical) |
| `Ms` (8.10) | H if I/II/V else M′ | **B** (`if typeOf ∈ {III,IV} then commutator M else M_F`) |
| `A₁`/`A`/`A₀` (8.10) | `A₁=Ms#`; `A=⋃_{x∈H#}C_M(x)#` (I) / `⋃_{x∈M#}C_{M′}(x)#` (𝓟); `A₀=A∪V^M` | **B**: `Set.iUnion` + centralizer-set。`S04.dadeSupport` と同 pattern |
| `supports`/`Ã(M)` (8.18) | conjugacy-saturation + "T supports S" | **B** (新 def) |

### B. 定理 (Tier C — statement は今 writable, proof は BG Thm A–E 待ち)

(8.2)/(8.5) は自己完結 Tier B props (一部 provable)。**(8.8) dichotomy / (8.11) / (8.12) / (8.13) centralizer-decomposition** は statement が type 塔 + `IsMinimalSimpleOdd` のみ参照 → §10 ファイル内で **今 compile**、proof は `sorry` + docstring に BG Thm A–E blocker 明記。**(8.14)–(8.17) は mmd `[MISSING_PAGE_EMPTY:15]`** (Nougat 欠落) → PDF p.15 から statement 回収まで `-- TODO`。

---

## §11–§16 詳細 (downstream、§10 後 Tier B / 残 Tier C)

- **§11**: (9.1) Wielandt = **唯一の Tier A、即着手** (→ `CoprimeAction.lean`)。Hyp 9.2/9.5 + 𝒮(Y)/𝒳(Y) 族は §10 後 Tier B。(9.3)–(9.11) は §10 type + 指標族 + Clifford/coherence numerics で Tier C。**(9.11) 8-part coherence** が最大 obligation (private sub-lemma 群)。`Hypothesis95` の quotient `H/H₀`/`U/C` (rank/nilpotent sub-clause) は **Normal-instance fragility** → docstring defer。
- **§12**: 最 downstream。Hyp 10.1/10.4/α_{ij} は §10+§4 Dade 後 Tier B。全定理 Tier C。**(10.8) `𝒮` not coherent は (7.5)/(7.8.b) が repo 既存 (sorry-free)** ので最も provable に近い (残 blocker = BG A–E size facts + (10.6)/(10.7))。(10.10.1)–(10.10.4) は `IsExtraspecial` (p³ 構造) で private sub-lemma 化。
- **§13**: **(11.1) 数論 = Tier A、証明まで今**。Hyp 11.2 + (11.5) `M″=HC` / (11.6) H p-group / (11.7) `H elem-ab order p^q, H₀=⊥` は statement が `commutator`/`IsPGroup`/`ElementaryAbelian`/card のみ → §10 後 Tier B (proof `sorry`)。(11.3)/(11.4)/(11.8)/(11.9.a) は `𝒮/ω/μ/τ` 族要 → `-- TODO` (fake statement 不可)。
- **§14**: headline **(12.7) Type I は Frobenius kernel M_F** — statement (`IsTypeI M → ∃ U, IsFrobeniusGroup M (M_F) U`) は §10 後 writable, proof `sorry`。(12.6)/(12.9) も Tier B 形。**(12.17) は既存 `S09.(7.11)` に配線可能**。残 (12.2)–(12.5)/(12.10)–(12.16) は `R(χ)/ω/τ₁/ψ` 族 + BG Thm 2.6(a)/Prop 1.16 で Tier C。
- **§15**: 最大・最深 (19 結果)。**(13.14) cyclotomic = Tier A、証明まで今**。`Hypothesis131` は本書最大 structure (~25 fields): S,T semidirect 構造 + char-set 𝒮/𝒯 + Dade τ + **ω/η/μ/ν を `Fin q → Fin p → ClassFunction G ℂ` FIELD として carry** (S03/S04 欠の principled workaround、S09 certificate-field 様式)。(13.2.b/c)/(13.12) `c=1`/(13.16) `N_G(W₁)=QW₂` statement は §10+`M_F` 後 Tier B。norm cascade (13.3)–(13.10)/(13.17)–(13.19) は Tier C。**4-section 構成 (Setup/Norm/Order/External) で 1 ファイル**、物理分割は成長後 (空 subdir 先行作成しない)。
- **§16 (apex)**: **(14.8.a) `q^{p+1}>p^{q+1}` = Tier A、証明まで今 (`Real.log` 単調)**。Hyp 14.1/14.3/14.10/14.13 (§15 bundle 拡張) + `def G0` (= `ConjClassSet` + set ops) は Tier B。(14.2.b) `Q elem-ab + W₂ normalizes` statement は writable。(14.13) conjugacy trivial。**最終 G-非存在 conclusion は `-- TODO (Phase 4): BG App.C Theorem C 待ち`**、または条件付き capstone `theorem … (bgThmC : (14.2).a ∧ (14.2).b → p ≤ q) : False` で依存を明示し build-green。

---

## データ品質の補正 (per-section notes へ backfill 要)

- **§10 (8.14)–(8.17)** は `04.10_*.mmd` で `[MISSING_PAGE_EMPTY:15]` (Nougat 欠落) → scaffold 前に `references/peterfalvi/pdf/` p.15 から statement 回収。回収まで `-- TODO`、fake statement 不可。
- **指標 index 族の未材料化**: `ω_{ij}`/`η_{ij}`/`μ_{ij}`/`ν_{ij}`/`σ`/`τ₁`/`ρ` は §13/§15/§16 が pervasive に参照するが S03/S04 に named object 不在 (S03 は `characterTableEntry`/`σ: Equiv.Perm` のみ、indexed grid 無)。**この事実を §10–§16 notes に明記**。第 1 report (§13–§16) と第 2 report (§10–§12) が独立に同一指摘 → 確度高。
- **BG Thm A–E / App.C の不在**: BG Ch3 は `S10`/`S11`/`S12` のみ (本 session 監査確認)、`Ch4_*`・`AppC_*` 皆無。§10 (8.8/8.11/8.12/8.13) と §16 最終矛盾の blocker。BG plan note と整合 (BG §16 = Tier C apex)。
- **(9.1) Wielandt の出典**: `[HB]XI.12.4` (mathlib 欠) → statement のみ今、proof `sorry`。
- **§14 BG hook の在庫確認要**: BG Thm 2.6(a) は `Ch1/S02_Representations.lean` が skeleton (statement 化要)。Prop 1.16/Lem 1.14 (§14 (12.9)/§16 (14.6)) と Lem 3.2/Prop 3.9 (§15 (13.16)/(13.17)) は `Ch1_Preliminary` 在庫を実装前に確認 (Prop 3.9 は `S03_FrobeniusActions` に存在見込)。

---

## 推奨実行計画 (phased, foundation-first)

- **Phase 0 (今すぐ・完全独立、群塔/BG 非依存)**: standalone 算術補題を **証明まで** FILL — (11.1) `pow_gt_four_sq_add_one_of_odd_primes`、(13.14) `geom_sum_div_facts`、(14.8.a) `q_pow_gt_p_pow`。各 section ファイルに「本当に proved な 1 補題」を置き、scaffold が true-stub でない錨にする。+ (9.1) Wielandt statement を `CoprimeAction.lean` に。+ notes のデータ品質補正。
- **Phase 1 (foundation = keystone)**: `OddOrder/GroupTheory/MaxNilpotentNormalHall.lean` (`M_F`, existence/uniqueness は `sorry`-backed) + `OddOrder/GroupTheory/MaximalSubgroupType.lean` (type 𝓕/I/𝓟/II–V + Ms + A₁/A/A₀ + PeterfalviType/typeOf + supports/Ã)。**BG §16 scaffold 担当と naming 共設計**。これで §10 が unlock。
- **Phase 2 (§10 = 最高価値ファイル)**: `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` — ~12 Tier-B def/props を FILL + 5 Tier-C 構造定理 (8.8/8.11/8.12/8.13) statement を `sorry` + BG Thm A–E blocker docstring。全て `IsMinimalSimpleOdd` + 新 type predicate 上で compile。(8.14)–(8.17) は `-- TODO` (PDF 回収後)。
- **Phase 3 (§11–§14 の hypothesis 層)**: §10 完成後、各 section の Hypothesis structure (9.2/9.5, 10.1/10.4, 11.2, 12.1/12.8) を Tier B で FILL + headline statement ((9.3),(10.7)/(10.10),(11.5)–(11.7),**(12.7)**) を `sorry`。(12.17)→`S09.(7.11)` 配線。指標族 `ω/μ` 要の定理は `-- TODO`。
- **Phase 4 (§15→§16 apex)**: §15 `Hypothesis131` (ω/η/μ/ν を field 化) → (13.2.b/c)/(13.12)/(13.16) statement。§16 Hyp 14.x + `G0` + (14.2.b)/(14.8) statement + 条件付き capstone。**BG Thm A–E + App.C 完成と同期**。最終 `feitThompson` bridge は `-- TODO Phase 5`。
- **並行調整**: §11–§16 を §10/BG 完成前に独立ファイル化しない (`M_σ`/Dade を自由変数 axiom 化する anti-pattern を回避)。`MaximalSubgroupType` は BG §16 と共有 module ゆえ naming 衝突に注意 (`notes/meta/forward_dep_policy.md`)。issue 採番は Peterfalvi=1000 固定レンジ。

各 phase は build-green 維持 (`lake build OddOrder` + AxiomsCheck)。深い未構築依存は **`-- TODO (Pf N.N): <blocker>`** で traceability 保持 (true-stub も hoist もしない)。

---

## Lean encoding tips (BG scaffold tips 準拠)

- **固定 G**: `(hG : OddOrder.BG.IsMinimalSimpleOdd G)` を全 hypothesis structure に thread。Pf §10「奇数位数極小単純群」= この G。**再定義禁止**。
- **共役**: `M^g = MulAut.conj g • M` (`open scoped Pointwise`)。set-normalizer は `Subgroup.normalizer (·:Set G)`。Hall は終始 `Isaacs.Ch03.IsHallSubgroup`。
- **Normal-instance fragility**: quotient objects `H/H₀`・`U/C` (§11 Hyp 9.5, §11 (9.4) chief factor) は rank/nilpotent sub-clause を **docstring 注付きで defer** (BG scaffold tips の既知の罠)。
- **指標族の workaround**: `ω/η/μ/ν` を S03/S04 に back-port するか、interim で §15 `Hypothesis131` の `Fin q → Fin p → ClassFunction G ℂ` **field** として carry (S09 `Hypothesis76.chiRho_decomp` の certificate-field 様式)。ただし定理 RHS の総和は §3/§4 family semantics 無しでは under-constrained ゆえ、field で carry しても **定理本体は `-- TODO` が安全** (fake statement より honest)。
- **type "rank 2"**: Pf (8.3.b) の "abelian of rank 2" = `IsCommutative ↥H ∧ rank ↥H = 2`。Pf rank = cyclic 直積因子数だが該当 abelian 群で `rank`/`pRank`-sum と一致 — docstring に定義的注記。
- **structure 様式** (S09 準拠): `structure HypothesisNN (G) [Group G] [Fintype G] where hG : IsMinimalSimpleOdd G; …` で全仮定 bundle。指標恒等式は証明不要時 certificate field 化。純群論/数値 statement は素直に `sorry`。数論補題 ((11.1),(13.14),(14.8.a)) は standalone で **証明まで**。
- **物理分割**: §15 は 4-section (Setup/Norm/Order/External) で 1 ファイル開始、空 subdir 先行作成しない (固定 5s/ファイル コスト)。active frontier を leaf に残し凍結 subsection を上流へ押し出す (CLAUDE.md ファイル粒度方針)。
- **capstone の明示依存**: §16 最終矛盾は条件付き `theorem typeTwoConfig_contradiction (… : Hypothesis141 …) (bgThmC : (14.2).a ∧ (14.2).b → p ≤ q) : False` で BG App.C 依存を型に出し build-green を保ちつつ traceable に。

---

*作成: 2026-06-01。2 並列調査エージェント (Pf §10–§12 / §13–§16) 出力 + BG plan note + 実 repo 監査の統合。詳細 per-result inventory は各 agent 出力 (本 session transcript) 参照。関連: `notes/bg/scaffold_feasibility_2026_06_01.md`, `notes/peterfalvi/s10_structure_minimal_simple.md`, `references/peterfalvi/04.{10–16}_*.mmd`, `references/bg/local-analysis.mmd` L4330–4446 (BG Types I–V)。*
