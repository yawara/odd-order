# Pf §16 — non-existence (`S16_NonExistenceG.lean`) gate map — lane-c (2026-06-22)

## ⭐ 2026-07-10 CURRENT — issue 3004 conditional (14.10)/(14.11) architecture

2026-07-08 の「`exists_MHypothesis.betaGrid` gate」という分類は **superseded**。
原文 (14.10) には `e=pq` / signs / grid expansion は無く、これらを無条件 fieldにした旧
`MHypothesis` は (14.11.1–2) 自身を循環させていた。Hub ruling
(`issues/3004-mhypothesis-conditional-grid.md`) に従い次へ修正:

```text
(14.10) MHypothesis
  e = actual |M:K|
       │
       ├─ b: (13.17.c)-dual  e=p ∨ e=pq ──▶ e≤pq
       │                                      │
       └─ K≠V ──▶ (14.11.1) strict gaps ─────┤
                                              ├─ b: faithful (13.19.c) alternatives
                                              │          │
                                              │          ▼ bound branches excluded
                                              └─▶ c: betaM_expansion_data
                                                    e=pq + ±1 + Y=0 + χ classification
                                                    + signed expansion
```

実装済み:

- `MHypothesis` の `complement_card_eq_pq` / `betaSigns` / `betaSigns_pm` /
  `betaGrid` を削除。`exists_MHypothesis` は actual indexで sorry-free構成。
- `main_size_bounds_structural`: `K≠V + e≤pq` から
  `k>2pv` と **strict** `(k−1)/e>(v−1)/p` を実証明。
- `BetaMGridParityAlternatives`: actual `betaM` に対する (13.19.c) の二つの
  bound-or-parity disjunction。b の corrected conjunction API から射影し、
  `betaM_axis_odd_of_main_size_bounds` は両 bound枝を実証明で排除。
- 無条件 norm/card API は `e` 一般形、`e=pq` は conditional norm cascade内でのみ使用。

残 frontier:

| owner | named boundary | 内容 |
|---|---|---|
| b | `complement_inf_P_structure_dichotomy` | faithful (13.17.c)-dual theorem body |
| b | `typeIOrthogonalityGridData_of_typeISetup` | faithful (13.19) deep producer |
| c/b interface | `exists_betaMGridData` | b の chosen Dade image と `Mdata.h78.beta` の同期 |
| c | `betaM_expansion_data` | projection + tightness + `Y=0` + χ classification |
| c | `complementIndex_eq_pq_of_K_eq_V` | K=V 後の small branch 排除 |

`ComparingLM` の L-side `grid_mem` を入力 fieldにしている旧 engineも、同じ generic
tightness engineへ将来再配線する。旧 over-strong `betaL_eta_independent` は citeしない。

---

## ⭐ 2026-07-08 CURRENT — definitive gate map (lane-c /loop, 全数検証)

**C cluster の全 13 live sorry (S16_NonExistenceG 10 + S15_HonestTypeP2A0 pin 3) は 2 つの
cross-lane gate に完全帰着。C の ungated deep math は完了 (prime-TI infra + `hyp46S` = sorry-free)。**

| sorry | 場所 | gate class | issue |
|---|---|---|---|
| `T_typeIII_ratio_le` (S-side βₛ) | S16:1750 | **lane-b** βₛ bridge (S15_SAndT) | 0098/3003 |
| `hVcomm` (V abelian) | S16:1896 | **lane-a** typeP_Galois σ-theory | 9000 |
| `T_isTypeP2` (key_ineq fwd) | S16:1963 | **lane-a** v-value (rests on) | 9013 |
| `tSide_caseB_v_gated_inputs` | S16:2063 | **lane-a** v-value σ-theory | 9013/9000 |
| `s/t_side_frobenius_kernel` | S16:4515/4528 | **lane-a** FieldNormalizer/TFieldModel σ | 9000 |
| `lSideGridCoeffData` m_row/m_col/grid_mem | S16:7215/7218/7236 | **lane-b** η-grid parity (β_S) | 3002 |
| `exists_MHypothesis` betaGrid | S16:8238 | **lane-b** η-grid (13.1.d) expansion | 3002 |
| pin `mu_row0_ne`/`diff_support`/`vanish_on_V` | S15_HonestTypeP2A0 | **lane-b** μ-grounding (`hyp.mu=residueS.mu2`) | 9076 |

- **lane-a σ-theory (9000/9013)**: 5 sorry。**lane-b η-grid/grounding/βₛ (3002/9076)**: 8 sorry。
- **C ungated 完了**: prime-TI (`PrimeTIResidue`/`residueS` sorry-free) + `hyp46S` (type-P2 Hyp46-for-S,
  commit 6945ba5f) + pin scoping (mu_row0_ne isolation, pin-2 j=0 over-claim 発見)。
- **⚠ pin 2 over-claim (要 b 協調)**: `tauS_mu_row0_diff_support` は `∀ j` だが j=0 で偽、`j≠0` 追加要
  (consumer は `_hj` 保持、cross-lane 2-step、issue 9076)。
- **結論**: C の独立 frontier は枯渇。残 close は全て lane-a σ-theory or lane-b η-grid/grounding 待ち。
  reactivation = a の typeP_Galois or b の grid/grounding landing。

---

> ⚠ **HISTORICAL (2026-06-22 レーン構造; 2026-07-02 追記)**: 現行は 3 レーン再編
> ([`ft_lane_reallocation_2026_06_28.md`](../meta/ft_lane_reallocation_2026_06_28.md))。
> `S15_SAndT*` は **lane c 所有** (下記の「S15_SAndT.lean is lane-h (cite only)」記述は無効)。
> issue 1004 は **closed** (producer landed、S-side vestigial)。`T_typeII` は**消費あり**
> (S15_SAndT.lean の (14.9)-gated 群; 下記「現 consumer 0」は無効)。
> live = [`s16_w4_char_cascade.md`](s16_w4_char_cascade.md) + issues 9001/9002/4001。

> Lane-c owns `OddOrder/Peterfalvi/S16_NonExistenceG.lean` (editable tail) +
> POLE-2 `field_normalizer_structure`. `S16_NonExistenceGCore.lean` is frozen (cite only),
> `S15_SAndT.lean` is lane-h (cite only). This note maps every remaining `sorry` in the
> editable tail to the *precise* upstream signature it bottoms out on, so the cross-lane
> dependency on Lane B (Pf §13 char/Dade) and Lane F (BG §14-16 carrier) is explicit.
> 正本 issue = 2009 (POLE-2). 関連 = 1004 (section16CharacterData, Lane B).

## 2026-06-22 (lane-c 再開): 基盤 char-infra へのピボット (ユーザー裁可)

再開時の全数 audit + Explore 監査で確認: **S16 の 13 sorry はすべて上流 char theory に gated** —
char core (14.11.2/.3/.4, 14.14, 14.16) は **η-grid が S15 free field** + (7.5)/(7.8)/(3.7)/(3.9) が
**repo に ABSENT**、構造 cyclic/typeII は §9/§11/§13 (Lane B)。ungated 3 本は kickoff (ff2338a5) で
消化済、直近 2 commit は carrier de-opacify (honest 化) 済。lane-b は main から 0 commits 先行、
`section16CharacterData` 未着手 ⟹ S16 内に ungated な証明仕事は無い。

→ **方針転換 (ユーザー選択「基盤 char インフラ構築」)**: §16 sorry を待つのでなく、§14-16 endgame
全体を gate している **foundational char infra を lane-c が構築**する。η free-field に依存しない
ungated な arithmetic backbone を先に積み、η carrier honest 化 (lane-h) 後に consume する
(signature 先行整備、[[feedback-gated-endpoint-skeleton-pattern]])。

### 構築済 foundational cores (sorry-free + axiom-clean)

| lemma | 役割 | commit |
|---|---|---|
| `one_le_norm_signed_paired_sum` | **(3.9)/(14.11.3) parity core**: 整数値 grid が共役 involution でペア・唯一固定点で値 1 ⟹ ±1 符号和は奇整数 ⟹ ‖·‖≥1。`generic_character_bound` (14.11.3) + dual (14.16) が cite | `2d517956` |
| `all_pm_one_and_card_of_odd_sq_sum_le` | **(14.11.2) sum-of-squares core**: 奇係数 grid・Σa²≤e−1・e≤\|grid\|+1 ⟹ e=\|grid\|+1 かつ全 a=±1。`betaM_expansion` (14.11.2) が cite | `9f17b010` |

両者 generic (`Fintype ι`)、`#print axioms` = [propext, Classical.choice, Quot.sound]。

### 適用に要る η-carrier 強化 = lane-h への ask (S15)

上記 core を `betaM_expansion`/`generic_character_bound`/(14.16) に wire するには、**S15 の η-grid
(`Hypothesis.eta : Fin q → Fin p → ClassFunction G ℂ`、現 free field + `eta_eq_tau_omega` のみ) を
honest 化**し、(3.9) の値性質を record/export する必要がある (lane-h 所有、lane-c は cite):

- **(3.9.c)** 生成元 `g ∈ G_0` (位数 pq 素) で `η_ij(g) ∈ ℤ` (整数値)。parity core の `n i` を供給。
- **(3.9.a)** 共役ペア `η_{(-i,-j)}(g) = conj(η_ij(g))`、整数値ゆえ実 = `η_ij(g)`。parity core の involution `ρ` + `hpair` を供給。`η₀₀(g) = 1` (唯一固定点 `i₀ = (0,0)`)。
- **η-grid 直交正規性** (5.x/3.9): 係数 `a_ij = ⟨β_M^τ, η_ij⟩` を射影として取り出し、展開
  `β_M^τ = Σ a_ij η_ij − χ` を出す。sum-of-squares core の `a` + `Σa²≤e−1` を供給。
- **(13.19.c)** 系の odd parity: `⟨β_M^τ, η_ij⟩` が奇。S15 に `OddIntegerInner` 既存 (betaL 側
  `caseC2_eta0j_odd` 等) — betaM 側の analog を export。

これらが揃えば lane-c が betaM/generic engine を core 経由で sorry-free に組める。
**∴ §16 char endgame の真の long pole = S15 η-grid carrier の honest 化 (lane-h)**。

## 更新 (2026-06-22, resume session — 上流 2 sorry 着地 + 精密 gate 特定)

ユーザー指示「上流から、文書上で早いものから、FT 限定」で再開。教科書 (14.4)/(14.6) 原文 +
上流 (S15) export を精読し、**文書順で lane-c 自身が忠実に閉じられる 2 本**を着地 (commit `aff0bc2a`、
full build + AxiomsCheck 緑 3881 jobs)。S16 実 sorry **13 → 11**、`bin/count-sorry` **131 → 129**。

- **`caseB_for_S` (14.6, 旧 211)** ✅ — `caseB_for_T` と同じ opaque-`Prop` scaffold で close:
  qualitative (9.7.b) 命題は `True` 担持 (consumer 不読)、数値 `u`-order は `S15.caseB_order_u_data`
  (13.15, faithful sorried §13 obligation) を cite して (14.8)/(14.11) cascade へ wire
  ([[feedback-cite-sorried-lemmas-if-signature-correct]])。(14.6) の rank-2 Sylow 群論本体は §13/§9 上流。
- **`K_eq_V_index_pq` の index 半 (`e=p*q`, 14.11, 旧 2012)** ✅ — `MHypothesis` を
  `complement_card_eq_pq` field で enrich (`LHypothesis.typeI_complement_card_eq_pq` の V-side dual)。
  唯一の constructor `exists_MHypothesis` (既 sorry) が供給ゆえ index 半は直接帰結化。

### 更新 (2026-07-15, C-1 — (14.6) compatibility bridge 撤去)

上の 2026-06-22 scaffold は撤去済み。`caseB_for_S` は chief factor に対する Clifford dichotomy
を実行し、case (9.7.a) を完成済みの type-I-over-normalizer contradiction で排除、残る
`CliffordCaseBData` を `caseB_order_u` に直接渡す。`CaseBForSData.caseB_formula` はもはや
`True` でなく、その実 certificate の `Nonempty`。`CaseBOrderUData` / `caseB_order_u_data`
は宣言ごと削除された。`T_isTypeP2` が必要とする S-side 上界は、循環を避けて独立な
`Hypothesis.u_le_cyclotomicQuotient` (AxiomsCheck 済み) から供給する。

### ⚠ 精密 gate 特定 (lane-h ask、新規): `exists_MHypothesis` (14.10) の V-side 構造構築

`exists_LHypothesis` は **sorry-free** だが、その dual `exists_MHypothesis` (旧 3324) は構造部すら
組めない。理由: `S15.typeII_overNormalizer_frobenius` が **S/U-side ハードコード**
(`(hSTypeII : IsTypeII hyp.S) → ∃ data, … ∧ (hyp.U ≤ data.H)`、S15:1712)。V-side 構築には
**T/V-side dual** が必要:

> **lane-h ask**: `typeII_overNormalizer_frobenius` の **T/V-side 版**を S15 に export —
> `(hTTypeII : IsTypeII hyp.T) → ∃ data : TypeIOverNormalizerData(V-side), … ∧ (hyp.V ≤ data.H)`
> (+ `complement_card_eq_pq` 相当)。これが在れば `exists_MHypothesis` は `exists_LHypothesis` の
> 機械的 dual として構造部を sorry-free 化でき、`MHypothesis.complement_card_eq_pq` も供給される。

同様に **`T_side_caseB_facts` (14.4, 136)** は S15 が S-side `caseA_parameters`(13.13)/`caseB_order_u`(13.15)
のみ持ち **T-side dual を欠く** (`lambda_forces_T_caseB` は discharge 不能な `lambda_induced_from_PC_linear`
仮説付き) ゆえ閉じられない。lane-h ask = T-side `caseA_parameters_T` (`caseA_for_T → p=3`) + (9.7)-for-T
dichotomy + T-side `D=⊥`/`v=full`。

⟹ **lane-c §16 の残 11 sorry は全て lane-h の §13/§14 char/構造理論に gated** (issue 4002 の再確認;
本セッションで原文・signature レベルまで独立検証済)。詳細 = 下記 gate 分類 + issue 4003 (η-carrier)。

## 現状 (2026-06-22, kickoff session)

`field_normalizer_structure` (POLE-2) の **dispatch tree は sorry-free** (lane-h の成果):
`exists_LHypothesis`✅ / `field_normalizer_of_U_characteristic`✅ / `field_normalizer_of_L_conj_M`✅ /
`H_eq_U`✅ を組み合わせる。`nonexistence_of_G` (BG App.C 仮説付き) も sorry-free。
残 `sorry` はすべて dispatch が cite する **named obligation** に押し込まれている。

`bin/count-sorry` = 135 (本セッション 136→135)。S16 ファイルの実 sorry = **13 本**。

### 本セッション (lane-c kickoff) の landing

- **`exists_LHypothesis` を §16 冒頭へ移動** — 中盤の数値補題が `LHypothesis` を構成して
  `caseB_for_S` を呼べるようにする (それまで file 末尾 3130 にあり forward-ref 不能だった)。
- **`key_inequality` (14.8)** = 実証明 (`key_inequality_of_caseB_outputs`, PROVEN) — free→proof。
- **`main_size_bounds` (14.11.1)** = conjunct 3 `(v-1)/p > (u-1)/q` 実証明、構造 2 本を
  `main_size_bounds_structural` に named-isolate。
- **`MHypothesis_kernel_cyclic`** = 実 assembly (`K=V` from `K_eq_V_index_pq` (14.11 cascade) +
  `V_cyclic` (新 13.2.a-for-T obligation))。**(14.11) norm-cascade を load-bearing 化**。

## 残 13 sorry の gate 分類

凡例: **[B]** = Lane B (Pf §13 char/Dade、producer 不在 or sorried-cite)、
**[F]** = Lane F (BG §14-16 carrier)、**[C]** = lane-c 内で更に進められる余地あり。

### A. (14.11) norm-cascade 系 (mostly arithmetic、char 入力に gate) — 今 load-bearing
| sorry | 行 | 内容 | gate |
|---|---|---|---|
| `main_size_bounds_structural` | 1784 | `k>2pv ∧ (k-1)/e ≥ (v-1)/p` | **[B]** M の type-I 構造 (k=|M_F|, e=index) + 次数/Dade データ。`betaM_expansion` の `e=pq` と同源 |
| `betaM_expansion` | 1813 | `e=pq ∧ betaM_expansion_formula` (後者 opaque) | **[B]** (14.11.2) β_M の η_ij 展開。issue 1004 |
| `generic_character_bound` | 1821 | `|ψ^τ₁| ≥ 1 on G_0` (opaque `generic_bound_formula`) | **[B]** (14.11.3) Dade generic set。issue 1004 |
| `normCascadeBound_of_charData` | 1838 | `normCascadeBound hyp k` | **[B]** (14.11.4) = (14.11.2)+(14.11.3)+(7.5) Frobenius 内積。これが唯一の真の char 入力 (下流の算術 cascade は `norm_cascade_contradiction` で sorry-free) |
| `K_eq_V_index_pq` (e=pq 枝) | 1875 | `Mdata.e = p*q` | **[F/C]** MHypothesis を `complement_card_eq_pq` field で enrich すれば close (LHypothesis に対応 field 既存)。exists_MHypothesis 側 (sorry) が供給 |

> **opaque Prop 注意**: `MHypothesis` の `betaM_formula` / `betaM_expansion_formula` /
> `generic_bound_formula` / `final_norm_contradiction` / `e_eq_index` は opaque `Prop` field。
> これらを concrete な character 述語に **materialize (de-opacify)** するのは Lane B の §14 Dade
> 仕事 (lane-b が §10-12 grid でやった de-opaque と同型)。lane-c は consumer ゆえ手を出さない。

### B. POLE-2 dispatch が cite する §13 char obligations
| sorry | 行 | 内容 | gate |
|---|---|---|---|
| `caseB_for_S` (14.6) | 211 | `∃ CaseBForSData, caseB_formula` | **[B]** S-side case-(9.7.b) 判定 = `character_degree_analysis` (S15:295, sorried) の出力で「どの枝か」。S-side 版 `lambda_forces_*` が未 stated。`caseB_order_u` (S15:693, sorried) は cite 可 |
| `U_cyclic_and_Q_elemAbelian` (13.2.a/b) | 2207 | `IsCyclic U ∧ IsElementaryAbelian q Q` | **[B]** §9/§11。`basic_structure.UW1_frobenius`/`U_commutative` (S15, sorried) は在るが U-cyclic は別 (kernel が cyclic とは限らない、c=1/(9.7.b) 経由)。Q elem ab は (13.2.b for T) |
| `V_cyclic` (13.2.a for T) | 2287 | `IsCyclic V` | **[B]** U-cyclic の dual。kernel_cyclic が cite |
| `MHypothesis_kernel_cyclic` 上流 | — | (上 A の `K_eq_V_index_pq`/`V_cyclic` 経由) | **[B]** |

### C. (14.13)–(14.16) 例外ケース char endpoint
| sorry | 行 | 内容 | gate |
|---|---|---|---|
| `orthogonality_switch` (14.14) | 3111 | `∃ data, caseA ∨ caseB` | **[B]** β_M-φ / β_L-ψ 直交 dichotomy 構成 = 実 char theory ((13.19.c) 出力 + caseB→(q,p)=(3,5))。`typeI_orthogonality_dichotomy` (S15:1833, sorried-faithful) を cite するが OrthogonalitySwitchData の caseA/caseB 述語と bound を構成する本体が深い |
| `caseB_character_contradiction_of_gap_inequalities` (14.16) | 3079 | `False` | **[B]** (13.19.c) を S/T 両側 + β_L^τ の η_ij 展開 (14.11.2 型) が non-zero pairing と矛盾。η-expansion 形が未 stated。`exists_typeI_eta_axes_odd_of_caseB_gap` (PROVEN) は odd-pairing を供給済 |

### D. V-side carrier 構成 (symmetric to exists_LHypothesis)
| sorry | 行 | 内容 | gate |
|---|---|---|---|
| `exists_MHypothesis` (14.10) | 3187 | `Nonempty (MHypothesis hyp)` | **[B]** 構造部 (M, K, normalizer_V_le_M) は `T_typeII` + `typeII_overNormalizer_frobenius` の T/V 適用で exists_LHypothesis と対称に組めるが、Dade fields (Mset/tau/psi/betaM/G0/…) は §13 Dade producer (issue 1004) 待ち。opaque Prop fields を埋める必要 |

### E. 単独・要調査
| sorry | 行 | 内容 | 状況 |
|---|---|---|---|
| `T_typeII` (14.9) | 1554 | `IsTypeII hyp.base.T` | **[B]** 教科書 (14.9) は真と主張するが、`one_typeII : IsTypeII S ∨ IsTypeII T` からは出ない (S type II で disjunction 充足ゆえ T は別証明要)。(14.9) の char 論法が要る。現 consumer 0 (exists_MHypothesis が bare sorry のため)。exists_MHypothesis を組むとき cite |

## lane-c が今後できること (gate 解禁を待たずに)

1. **`K_eq_V_index_pq` e=pq** — `MHypothesis` を `complement_card_eq_pq` field で enrich
   (lane-c 所有 carrier、exists_MHypothesis が sorry なので追加コスト 0)。LHypothesis の
   `typeI_complement_card_eq_pq` と対称。**[C] 着手可**。
2. **`exists_MHypothesis` の構造 skeleton** — `T_typeII` + `typeII_overNormalizer_frobenius`
   を T/V 側に適用し、構造 fields を埋め、Dade fields を named obligation に isolate
   (gated-endpoint skeleton)。ただし T_typeII (14.9) と Dade producer に gate。**[C/B]**。
3. それ以外 (A の char cascade, B の §13 cyclic, C の dichotomy) は **Lane B の §13 Dade
   producer (issue 1004 section16CharacterData) 着地待ち** = cite 先がそこで生まれる。

## cross-lane ask (Lane B / hub 宛)

lane-c の §16 unconditional 化は **Lane B の Pf §13 Dade 指標論 (issue 1004) に bottom-out**。
B が `section16CharacterData` producer を landing する際、以下を **faithful signature** として
export してくれれば lane-c が cite で §16 を実証明で積める (signature-first、正しければ sorried 可):

- S-side case-(9.7.b) 判定 (`caseB_for_S` 用) — `character_degree_analysis` の dichotomy 出力
- `U_cyclic` / `Q_elementaryAbelian` / `V_cyclic` (13.2.a/b、§9/§11)
- (14.11.2)/(14.11.3) の β_M η-expansion + generic bound、(14.11.4) norm 不等式 (Frobenius (7.5))
- (14.14) 直交 dichotomy、(14.16) β_L^τ η-expansion contradiction
- `T_typeII` (14.9)

## 2026-07-09 lane-c 精査: (14.9) `T_typeIII_ratio_le` hcount de-bundle は **BLOCKED** (v=|V| が gated)

`T_typeIII_ratio_le` (S16_NonExistenceG:1647) の唯一 sorry (:1750) は **bundle**:
`∃ Γ x, hcount ∧ hxcoe ∧ hx ∧ hnorm` (`T_typeIII_ratio_le_of_sSide_gap` :1519 の 4 入力)。
`hcount : (calT1.card:ℚ) = (v−1)/p` の close を試みたが **2 重に blocked、de-bundle しても sorry は減らない**:

- ⚠ **`v = |V|` は ungated でない**: `hVcard` (:4080-4085) は `V_inf_centralizer_Q_eq_bot`
  (**S15_SAndT:1891 = bare sorry**、T-side d=1、docstring「(14.9) T_typeII structure に gated」) を **cite**。
  ∴ v=|V| は T-side d=1 sorry に gated (私の初回「ungated」判断は誤り、`grep -c sorry` の 1 hit を見落とし)。
- ⚠ **forward-ref**: v=|V| は `IsTypeII hyp.base.T` を要すが `T_typeII` (:1973) は `T_typeIII_ratio_le`
  (:1647) より**後方**。`hIII : IsTypeIII` からは IsTypeII を得られない (II/III 排他)。
- ∴ hcount を close するには sorried v=|V| を cite する forward-ref-broken path しか無く、**bundle は honest as-is**。

**再利用可の発見 (別 endpoint 用)**: (a) exact 乗法カウント `card_image_induce_mul_index_eq`
(`OrbitOnIrr.lean:56`, `(𝒯.image Ind).card * H.index = 𝒯.card`) — floor 版 `calT1_image_induce_card_eq`
より強く、`p ∣ (|V|−1)` を要する任意の exact ℚ cast に使える。(b) `T_typeIII_calT1_family` (:677) の
5th conjunct (count) 内に `hinertia`(:811)/`hconj`(G-conj, :821)/`hcard`(:845) が local に proven。
⟹ v=|V| が ungate される (= `V_inf_centralizer_Q_eq_bot` が実証明化 = 別レーン/9072 T-side d=1) まで 14.9 は保留。


## 2026-07-09 lane-c (再開): pin 2/3 の close engine 構築完了 — pins は「grounding のみ待ち」に精密化

RULING #2 (9077) の「landing 発火で一気に close (infra 完備)」の前提を実査 → **pin 2/3 の
「grounding 仮説 → S06 定理で close」engine が未構築**だったため構築 (c-buildable / non-dup):

- `426c3ae1` **Engine A `Hypothesis.residueS_mu2_diff_support`** (S15_HonestTypeP2A0): Coq
  `prDade_sub_TIirr_on` (PFsection4.v:838) の S-side instance。**Coq 原典と同一の仮定形**
  (`(j:ℕ)≠0` / `(k:ℕ)≠0` / 度数一致 — Coq 自身が度数一致を明示仮定に取る) で、
  `μ2_{ij} − μ2_{ik}` の support ⊆ `A₀(S)` を `certainType_diff_supp_subset_A0` の hyp46S
  instantiation で実証明。付随 refactor: `residueS` (S13_PrimeTIResidueBridge) の data instance
  を scoped `FiniteInduce` 供給に統一 (instance 項不一致 → columnFamily-level defeq 破壊
  → whnf timeout、の根治。教訓: instance-dependent な def の cross-form cite は
  **両側を同一 scoped 定数に統一**するのが正解、letI 再現より強い)。
- `4cff46ce` **Engine C `Hypothesis.residueS_mu2_diff_dade_apply_of_mem_V`**: regular set
  `V_S = W∖(W₁∪W₂)` 上の `τ_S(μ2-diff)(v) = δ·(ω^σ-diff)(v)` (Coq prTIirr_id 系)。Dade 側は
  `dadeIntegralCharacterMap_apply_of_support` + Engine A の support で完全 discharge。

**pins の close 残 (b-side grounding landing 時)**: pin 1 = `mu2_orthonormal` transport 1 行 /
pin 2 = Engine A cite (+9076 の j≠0 signature fix、度数は §13 具体値) / pin 3 = Engine C +
**η/ω^σ-grid 同定** (`η_{ij} = δ·ω^σ_{ij}` on regular、(3.5)/(13.1.d) spine 対応 — grounding
package の一部として b/spine 側)。

**s_side_frobenius_kernel (SubgroupM:992) の追加調査**: `field_normalizer_structure` (14.2、
proven dispatch) の cite は**真の循環で不可** (s_side → (14.11.3) → exists_MHypothesis →
field_normalizer_structure)。honest 分解 = (14.6)-時点の §13 供給 (u-value = b の
`caseB_order_u` 等) で `field_normalizer_of_U_characteristic_of_inputs` (proven engine) を
直接呼ぶ形 — 構造 inputs (`W2_le_P`/`Q_elemAb`) は `S_field_model_structural_inputs` で
**既に proven**。t_side 型の精密 existential 化は次 iteration 候補 (hcyc/(14.5)-y の
(14.6)-context 供給可否の原文照合が要る)。

### 追記 (同日): s_side_frobenius_kernel 分解完了 (`aa9695f2`) + 次 iteration 候補

- **s_side_frobenius_kernel = crisp frobPU gate 化済**: 残 sorry は Coq `frobPU`
  (`IsFrobeniusGroup ↥S' (P.subgroupOf S') (U.subgroupOf S')`) そのもの。真の gate =
  typeP_Galois S (9000/lane-a、Coq `typeP_Galois_P` 経由) と code-level 確定。transport
  (Isaacs 6.4 `centralizer_kernel_le` の座標搬送) は実証明済。field-model 経由の旧 framing は
  真の循環 (field_normalizer_structure ← exists_MHypothesis ← (14.11.3) ← 本 lemma) で不可。
- **次 iteration 候補 (engine-prep 系の残り)**: `exists_MHypothesis` betaGrid (ComparingLM:~1368)
  の M-side grid-coefficient carrier mirror。L-side 機構 (`lSideGridCoeffData` +
  `lSide_delta_grid_expansion`、±1 rigidity assembly) の `hq3/hp5` binder は **body 未使用の
  vestigial** ゆえ一般 q,p で M に mirror 可能。ただし M-side は `TypeICoherent78Data` package
  でなく `exists_M_hypothesis78` の直接 h78 を持つ → **L-machinery の dataL → h78 一般化 or
  M-data の TypeICoherent78Data 再 packaging** の設計判断が要る (中規模)。gated 3-field
  (parity ×2 + Y=0 membership) は L-side と同一の b-layer。
