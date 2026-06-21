# Pf §16 — non-existence (`S16_NonExistenceG.lean`) gate map — lane-c (2026-06-22)

> Lane-c owns `OddOrder/Peterfalvi/S16_NonExistenceG.lean` (editable tail) +
> POLE-2 `field_normalizer_structure`. `S16_NonExistenceGCore.lean` is frozen (cite only),
> `S15_SAndT.lean` is lane-h (cite only). This note maps every remaining `sorry` in the
> editable tail to the *precise* upstream signature it bottoms out on, so the cross-lane
> dependency on Lane B (Pf §13 char/Dade) and Lane F (BG §14-16 carrier) is explicit.
> 正本 issue = 2009 (POLE-2). 関連 = 1004 (section16CharacterData, Lane B).

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
