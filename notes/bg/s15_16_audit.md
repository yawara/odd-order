# BG §15 / §16 — faithfulness + dependency + gate audit (Lane G, 2026-06-14, post-13.6)

Lane G を §13 → BG §15+§16 に再配置した直後の着工前監査。目的は LAUNCH の
「scaffold の faithful 化 + §14 非依存補題」を実行可能な形に落とすこと。
正本 mmd = `references/bg/local-analysis.mmd`、§15 = L4086–4255、§16 = L4256–4562。
対象ファイル = `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean`（9 sorry）/
`S16_MainResults.lean`（9 sorry）。

## 0. ゲート現実（重要）

**§15/§16 の 18 endpoint はすべて §14（Lane H）/ §13（Lane F）に gate されている。**
各 docstring が proof gate を列挙しており（下表）、mmd の "schematic proof" 依存表
（L4424–4449）とも一致する。⟹ **現時点で §14 非依存に証明できる §15/§16 の主結果は無い。**
唯一の ungated Lean ターゲットは `M_F` の基本 API（§3）。本格証明は F が §13、H が §14 を
landing させてから。

## 1. FT-critical spine（私の担当の中で最短経路に乗る部分）

```
Prop 16.1 (型辞書 S14↔shared)  ──┐
BG Theorem I  (8.8 へ)          ──┼─→ Peterfalvi S10_BGInterface (既に私の scaffold を cite)
BG Theorem II (8.12/8.13 へ)    ──┘        ↓
                                    Pf §10–16 character theory
                                            ↓
                          FeitThompson.sectionSixteenHypothesis_of_isMinimalSimpleOdd
                                  (= FeitThompson 層 唯一の実 sorry)
```

- `sectionSixteenHypothesis_of_isMinimalSimpleOdd`（[FeitThompson.lean:67]）は **Peterfalvi**
  の `S16.Hypothesis` を生成する。BG §16 の Theorem I/II はそこへ供給される指標論側の入力。
- `OddOrder/Peterfalvi/S10_BGInterface.lean` は既に私の §16 scaffold を cite している
  （`proposition_type_classification` / `theoremI_…` / `theoremII_…`）。⟹ **私が §16 scaffold を
  証明すると Peterfalvi interface の conditional 補題が自動 unconditional 化する。**
- よって優先順位 = **Prop 16.1 → Theorem I → Theorem II**（A–E はそれらの支持）。

## 2. 忠実性 verdict（endpoint 別）

### §16（mmd L4256–4562 を直接照合済）

| endpoint | mmd | verdict | 備考 |
|---|---|---|---|
| `proposition_type_classification` (Prop 16.1) | L4478 | ✅ **faithful** | 6 句 = mmd (a)–(f) 完全一致 |
| `theoremB_U_and_A_tame` (Thm B) | L4368 | ✅ **faithful** | 5 句 = B(1)–(5)。⚠ 句2 は `centralizerGeneratedBySigma M U = ⟨U∩M̂_σ⟩` の def 等式に依存（成立するが証明要） |
| `theoremA_maximal_structure` (Thm A) | L4274 | ⬜ 未照合 | gate: 10.2(b)/15.1(a)/14.2(abc)/15.2(a)/15.5/15.7 |
| `theoremC_paired_structure` (Thm C) | L4303 | ⚠ **lossy** | `∃! Mstar` 句が C(4)(6)(7)(8) を緩く束ね、**落ちている**: C(4)「K=C_{M*}(K*) かつ K* は κ(M*)-Hall」/ C(6)「M∩M*=K×K*」(scaffold は IsCyclic(K⊔K*) のみ) / C(7)「全 H∈M_P は M か M* に共役」/ C(8)「N_G(Ẑ)=Z」/ C(9)「C_M(Ẑ)=A_0−A」。また C(2)「M_F 非巡回」が Thm C に無い（Cor 15.6 にはある） |
| `theoremD_msigma_conjugacy_and_centralizers` (Thm D) | L4317 | ⬜ 未照合 | D(4) tail は復元済。gate: 15.3(b)/12.17/14.4(b)/A(8)/15.9 |
| `theoremE_sigma_partition_and_counting` (Thm E) | L4370 | ⬜ 未照合 | gate: 14.5(c)/13.9/14.9 |
| `aSets_support_slice` | L4368/4404 | ⬜ 未照合 | A/A_0 の TI + Supports スライス |
| `theoremI_…dichotomy` (Thm I) | **L4526** | ⚠ **両部あるが圧縮** | 句1 共役 = mmd Thm I 句1 ✓ / 句2 dichotomy は mmd の (1)–(5) を圧縮し **落ちている**: W の normalizer-V 性質、S=W₁S′/T=W₂T′/S∩T=W 構造、条件(5)「S,T とも II–V 型」。**docstring の mmd 行参照 L4402 は誤り → L4526 に修正要** |
| `theoremII_tame_embedding` (Thm II) | **L4548** | ⚠ **lossy** | (Ti)+D⊆A+一意性+型I/II は捕捉、**落ちている**: (Tii)(a)–(e) supporting-subgroup system、(Tiii)。Pf (8.12)/(8.13) が (Tii)/(Tiii) のどこまで要るか要確認。docstring 行参照 L4416 も要確認 |

### §15（docstring の gate 表のみ。mmd L4086–4255 の本文照合は次セッション）

| endpoint | gate（docstring 記載、mmd と要照合） |
|---|---|
| `typeP_auxiliary_structure` (Lemma 15.1) | 14.7(d)(h)/12.10(b)/10.2(c)/14.3/12.5(d)/12.12 |
| `mf_ne_msigma_typeP1_structure` (Thm 15.2) | 14.1/14.7(f)/14.2(a)/6.3(a)/3.8/1.5(a)(d)/3.7/3.10/5.5(a) |
| `mf_hall_centralizer_control` (Cor 15.3) | — |
| `nilpotent_hall_embeds_in_mf` (Cor 15.4) | — |
| `fitting_decomposition` (Cor 15.5) | — |
| `typeP_kstar_in_mf` (Cor 15.6) | — |
| `fitting_not_ti_cases` (Thm 15.7) | E_i/exponent/Ω₁(Z(P)) 句は §12/§10.13 encoding 完成まで deferred と docstring 明記 |
| `tau2_transfer_constraint` (Thm 15.8) | 14.12/15.2/12.6/Uniqueness/12.17/14.4 |
| `centralizer_escape_final_local` (Cor 15.9) | 同上 |

## 3. §14 非依存の provable core（現時点で唯一の Lean ターゲット）

`maxNilpotentNormalHall M = sSup {N | N≤M ∧ (N.subgroupOf M).Normal ∧ Nilpotent ∧ Hall}`。
def docstring は「この sSup が再び maximal nilpotent-normal-Hall 性を持つ（特に Hall）」を §15 へ
deferred としている。そのうち **containment と M-正規性は §14 非依存に証明可能**（Hall 性が本丸で残る）。

- ✅ **`maxNilpotentNormalHall_le` (`M_F ≤ M`)** — 本セッション landing（`sSup_le fun _ hN => hN.1`、S15_MF.lean）。
- ⬜ **`M ≤ normalizer (M_F)` / `(M_F.subgroupOf M).Normal`** — 次ターゲット。証明スケッチ:
  m∈M に対し各候補 N は (N.subgroupOf M).Normal ⟹ M≤N_G(N) ⟹ `conj m • N = N`
  (`conj_smul_eq_self_of_mem_normalizer` + `le_normalizer_of_normal_subgroupOf`)。よって
  conj m は候補集合 S を各点固定 ⟹ `conj m • sSup S = sSup S` ⟹ m∈normalizer。
  要 pin: 本 repo の set-引数 `Subgroup.normalizer (· : Set G)` の所在 + pointwise `smul_sSup`。
- Hall/nilpotent の well-definedness = 真の §15 内容（nilpotent は Fitting で join 可、**Hall が hard core**）。

## 4. 次セッション推奨

1. `M ≤ normalizer (M_F)`（§3 スケッチ）を landing — MF 基本 API を完成。
2. faithfulness 監査続行: Thm A/D/E + Lemma 15.1 を mmd 本文照合（§15 本文 L4086–4255 未読）。
3. lossy statement の修正（Thm C → Thm II → Thm I dichotomy の順）。**ただし**:
   - scaffold sorry の statement 強化は Peterfalvi citation を壊さない（結論が強くなるだけ）が、
     1 定理ずつ build 検証して進める。
   - 落ちた句のうち **downstream（Pf 8.x / final contradiction）が実際に要する分**を優先復元。
     不要に重い句を足して sorry を膨らませない。
4. 本格証明は §14（H）/§13（F）landing 後。それまでは 1–3 を回す。

## 5. §15-body 忠実性監査 (mmd L4166–4262, 2026-06-14 追加)

§15 endpoint 全 9 件は **external citation 0**（freely fixable）。⚠ **monitor の sorry-不増 gate**
ゆえ修正は「既存 sorry の強化/差替え」のみ可、**新 sorry'd theorem の追加は不可**（合流 abort）。

| endpoint | mmd | verdict |
|---|---|---|
| `mf_hall_centralizer_control` (Cor 15.3) | L4204 | **✅ FIXED 2026-06-14** — 旧 scaffold は無関係な centralizer-escape 主張 (`C_G(X)≤M ∨ …`) で docstring (「centralizer and conjugacy control」) と不一致だった。mmd 15.3(a) `C_M(H)=C_{M_σ}(H)·X` (X cyclic τ₂) + (b) `N_M(H)`-fusion に restated (uncited, sorry-neutral) |
| `typeP_kstar_in_mf` (Cor 15.6) | L4228 | ✅ **faithful**（K*≠1 cyclic ⊆ M_F∩M''、M_F 非巡回 — 5 句一致） |
| `typeP_auxiliary_structure` (Lemma 15.1) | L4166 | ⚠ **narrowed + lossy**: scaffold は `IsTypeP M` 仮説を追加（mmd は **全 M ∈ ℳ**）→ type-F 失う。また 15.1(c) の「X は cyclic τ₂(M)-subgroup」が脱落（M(C_G(X))={M} のみ保持） |
| `mf_ne_msigma_typeP1_structure` (Thm 15.2) | L4180 | ⚠ **organizational**: mmd 冒頭の一般鎖「1⊂M_F⊆M_σ⊆M'⊂M」が statement に無いが、その事実は **Theorem A に存在**（`MF≤Msigma`, `Msigma≤M'`）。M_F≠M_σ 分岐の 7 bullet は概ね faithful |
| `fitting_decomposition` (Cor 15.5) | L4219 | ⚠ **lossy + 要検証**: mmd F(M)=F(M_σ)×Y を scaffold は `MF(Msigma M)⊔Y` で表現（**MF(M_σ) vs F(M_σ)** の等式は非自明・要確認）。(a)τ₂/(c)「H⊆M', M'/H nilpotent」/(d)「K≠1→F(M)⊆M'」脱落 |
| `fitting_not_ti_cases` (Thm 15.7) | L4234 | ⚠ **known-deferred**（docstring 明記）: (d) E₃=1/E₂⊴E/E≅E₁、(e) 詳細 trichotomy（O_p/O_{p'}/exponent/Ω₁(Z(P))）が deferred。mmd の (a)(b)(c) + (e) 概形は捕捉 |
| `tau2_transfer_constraint` (Thm 15.8) | L4264 | ⚠ 要精査: mmd「q=|K|, q は τ₂(H) 唯一の素数, τ₂(M)=∅」を scaffold は `tau2 M=∅ ∧ ∃q, tau2 N={q}`（**N vs H**、「q=|K|」脱落） |
| `centralizer_escape_final_local` (Cor 15.9) | L4298 | ⬜ 未精査 |
| `nilpotent_hall_embeds_in_mf` (Cor 15.4) | L4215 | ⬜ 未精査（mmd: nilpotent Hall H → M を H⊆M_σ に取れる） |

**次の安全な fix（sorry-neutral 強化、優先順）**: Lemma 15.1(c) に「X cyclic ∧ τ₂」追加 / Cor 15.5 に
(c)(d) 追加 + MF(M_σ)=F(M_σ) を別途確認 / Lemma 15.1 の `IsTypeP` 仮説除去（要 type-F 整合確認）。
**Thm 15.2 一般鎖は新 theorem 不可（monitor gate）ゆえ Theorem A 経由で足りると判断、修正不要**。

## 6. 監査完了 — Thm A/D/E + Cor 15.4/15.9 (2026-06-14 追加)

§16 Thm A statement = mmd L4362、§15 Cor 15.9 = L4298 を照合し残り全 endpoint を監査完了。

- **Thm A** `theoremA_maximal_structure` — ⚠→**✅ A(3) バグ修正** (`33de10f2`): 旧 scaffold は
  `U⊔M_σ ≤ N(U⊔M_σ)`（任意部分群が自身を正規化する**自明命題**）を述べていた → mmd A(3)
  `UM_σ ⊴ M` すなわち `M ≤ N(U⊔M_σ)` に修正（Cor 15.3 / Thm II と同型の triviality バグ）。
  **残る脱落** (proof-time 復元): A(3) `U⊴UK` / A(5) directness `K⊓K*=1` (× を ⊔ で表現) /
  A(6) `1⊂M_F`・`M'⊂M`・`M'/M_F nilpotent` / A(7) `F(M)=C_M(M_F)M_F`・`K≠1→F(M)⊆M'`。
- **Thm D** `theoremD_msigma_conjugacy_and_centralizers` — ✅ **概ね faithful** (D(1)-(4) 捕捉;
  RData で D(3)(4) 構造化)。軽微脱落: D(2) の `M_σ∩M^g = M_σ∩M_σ^g` 等式（cyclic 性は保持）。
- **Thm E** `theoremE_sigma_partition_and_counting` — ✅ **概ね faithful** (E(1) 濃度 / E(2) σ
  disjoint / E(3) covering; `hR`/`hRreps` で RData pin 済ゆえ "arbitrary R" 落とし穴回避)。
- **Cor 15.4** `nilpotent_hall_embeds_in_mf` — ⚠→**✅ 修正** (`b58b5367`, → `_in_msigma`): Hall 仮説
  脱落 + 結論 `H≤M_F` 過剰主張 → Hall 仮説復元 + `H≤M_σ` 化（mmd は M_σ; H は M で正規とは限らず
  M_F は従わない）。
- **Cor 15.9** `centralizer_escape_final_local` — ⚠ **(a)(b) faithful, (c) lossy**: scaffold (c) は
  `x`/`N_G(⟨x⟩)≤E⊓N` だが mmd は `x_r`(r-part)/`N_E(⟨x_r⟩)⊆E∩N`、かつ `|E∩N|=|N/N'|` 脱落。
  proof-time に精密化（intricate ゆえ defer）。

⟹ **§15/§16 全 18 endpoint 監査完了**。検出した triviality/over-claim バグ 3 件 (Cor 15.3 /
Thm A(3) / Cor 15.4) は修正済、Thm II/C/I dichotomy + Cor 15.5/15.9(c) の intricate 脱落は
proof-time 復元。§14 非依存 API (M_F well-definedness + 通知 notation) は本セッションで完備。

## 7. 証明-readiness 調査 (2026-06-14 — endpoint 証明を阻む構造的要因)

§16 endpoint を sorried cite で証明する試みで判明: **scaffold は現状 proof-ready でない**。
sorried §14 だけでなく **scaffold 自身の構造**が clean citation を阻む:

- **bundled existential**: Thm 15.2 (`mf_ne_msigma_typeP1_structure`) は全内容を `hne: M_F≠M_σ`
  gate 下の `∃ K Kstar Q Q0 D p q, …` に束ねる。Cor 15.6 が要する `K*≤M_F` は (i) この existential
  の `Kstar` が Cor 15.6 の `Kstar` と別物、(ii) `K*≤M_F` が conjunct として露出していない (Q≤M_F +
  Kstar が q-group からの導出が要る)、(iii) `hne` が Cor 15.6 の仮説に無い、で **抽出不能**。
- **case-split**: Theorem A は一般 M だが Prop 14.2 (cite 先) は type-P 限定 → type-F 構造を別途要す。
- **σ-theory**: Cor 15.4 は `N_G(S)⊆M → p∈σ(M) → S⊆M_σ` の subtle な σ 補題を要す (clean cite 無し)。
- **§12 encoding**: Thm 15.7(d)(e) は E_i 構造、Cor 15.9(c) は x_r (r-part) を要す。

⟹ **endpoint 証明には scaffold の restructuring が前提** (bundled existential を de-bundle して
中間事実を accessible に、hne-gate を外す、σ/E_i 補題を整備)。これは coherent な focused effort
(multi-hour) 向きで、60s loop fragment 不適。**F/H が §14 を landing 後**が望ましい (sorried §14 への
fragile 依存回避 + §14 結果の最終形に合わせて cite)。schematic proof の cite→conjunct 対応自体は
mmd L4424-4449 に在る (B: 12.1d/12.5b→1, 15.1d/e/c→2/3/4/5 等) ので、restructuring 後は機械的。

## 8. endpoint 証明プラン (cite map; restructuring 後の実行用)

restructuring (Thm 15.2 parametrize 済, `43f42629`) で §15 は概ね citable。§14 は Lane H が
parametrize 済 (Prop 14.2 `typeP_structure` は K/Kstar/U 仮説 + Kstar≠⊥ 露出、Thm 14.7
`typeP_duality` は IsCyclic(K⊔Kstar) 露出)。endpoint 証明は focused session 向き(各 ~40-50 行)。

**Cor 15.6 (`typeP_kstar_in_mf`) cite map** (full scoping 済):
- `Kstar≠⊥` ← `typeP_structure hG hM hP hK hKstar hU` の conjunct 3。⚠ U が要る → Hall 存在で構成。
- `IsCyclic Kstar` ← `typeP_duality` の `IsCyclic(K⊔Kstar)` + `Kstar≤K⊔Kstar` + subgroup-of-cyclic。
- `Kstar≤MF M` ← case-split: `MF=M_σ` (Kstar=M_σ⊓C(K)≤M_σ=MF) ∨ `MF≠M_σ`
  (`mf_ne_msigma_typeP1_structure hG hM hne hK hKstar` → 露出済 `Kstar≤MF`)。
- `Kstar≤M''` ← Lemma 6.3(a) (`S06_Additional:300`) + M=KM' (Thm 14.7(h) — 要 source 確認)。
- `¬IsCyclic(MF M)` ← contradiction: MF cyclic → F(M) cyclic (Cor 15.5) → M'⊆C_M(F(M))⊆F(M)
  (`S08.centralizer_fittingInG_inf_le_fittingInG` + Aut(cyclic) abelian) → M''⊆F(M)'=1 →
  Kstar≤M''=1, contra Kstar≠⊥。

friction: U 構成 / M=KM' source / contradiction の Aut-abelian step。他 endpoint も同様の
cite map が mmd schematic (L4424-4449) から作れる。**実行は focused session が効率的**
(60s loop では各 endpoint multi-iteration uncommittable WIP)。

## 9. Aut-abelian core landed + Cor 15.6 friction の解消状況 (2026-06-14, `dd10d84d`)

§14 非依存の **Aut-abelian core を S15_MF に landing** (sorry-free, axiom-clean) — Cor 15.6
conjunct 5 (`¬IsCyclic MF`) のエンジン:

- `actionCommutator_conj_eq_commutator` (private): `actionCommutator (MulAut.conj) = commutator H`。
- `commutator_le_centralizer_of_normal_isCyclic` (一般・再利用可): N⊴H cyclic ⟹ H' ≤ C_H(N)。
  BG Thm 4.12 機構 `actionCommutator_le_centralizer_of_isCyclic_isAInvariant` (φ=MulAut.conj) 再利用。
- `fittingInAmbient_cyclic_imp_derivedDerived_eq_bot`: **F(M) cyclic ⟹ M''=⊥** (M'≤C_M(F(M))≤F(M),
  F(M) abelian)。`centralizer_fitting_le_fitting` (S01) + 上記 core。

**Cor 15.6 cite map の friction を全点精査して更新** (section 8 の「要 source 確認」を解決):

| conjunct | source | 状態 |
|---|---|---|
| `Kstar≠⊥` | `typeP_structure` conjunct 3 (U は `Ch03.hall_E_exists (G:=↥M)` + `map M.subtype` で構成、`exists_hallAlphaSubgroup_isHallInG` がパターン) | ✅ 露出済 (sorried §14, stable) |
| `IsCyclic Kstar` | `typeP_duality` の `IsCyclic(K⊔Kstar)` + `isCyclic_of_surjective`/subgroup-of-cyclic | ✅ 露出済 (sorried §14, stable) |
| `Kstar≤MF` | case-split: MF=Msigma (inf_le) ∨ MF≠Msigma (`mf_ne_msigma_typeP1_structure` 露出済 `Kstar≤MF`) | ✅ (sorried, mine) |
| `Kstar≤M''` | Lemma 6.3 第2結論 `centralizer_inf_le_derivedInG_of_isComplement'` (**proved**, S06_Additional:396) ＋ M=KM' | ⚠ **M=KM' が §14 Thm 14.7(h) に未露出** |
| `¬IsCyclic MF` | `fittingInAmbient_cyclic_imp_derivedDerived_eq_bot` (proved) ＋ 「MF cyclic⟹F(M) cyclic」(Cor 15.5、要露出) | ✅ engine proved; Cor 15.5 強化要 |

**🔑 ボトルネック更新**: section 8 は Lemma 6.3 を「要 source 確認」としたが **第2結論
`centralizer_inf_le_derivedInG_of_isComplement'` は proved**(`H⊴G normal Hall 補群 K, H≤G',
coprime ⟹ C_H(K)⊓H ≤ H'`)。真の唯一の欠落 = **M=KM'** (`IsComplement' (derivedInG M) K`):
- §14 `typeP_duality` (Thm 14.7) は (h)「M=KM', K∩M'=1」を **露出していない** (statement に無し)。
- **迂回路**: mmd Lemma 15.1(a)「UM_σ⊴M=KUM_σ」+ (b)「K≠1⟹M'=UM_σ」⟹ M=K·M'、|K| κ-数 /
  |M'|=|UM_σ| κ'-数 ⟹ K∩M'=1。**MY `typeP_auxiliary_structure` (Lemma 15.1) に
  `IsComplement' (derivedInG M) K` を sorry-neutral 強化すれば §14 非依存に M=KM' を供給可能**
  (Lemma 6.3 適用は ↥M 内: H=M'.subgroupOf M, coprime(|M'|,|K|) 要、subtype juggling)。

⟹ **Cor 15.6 は (i) Lemma 15.1 に IsComplement' 強化 + (ii) Cor 15.5 に「MF cyclic⟹F(M) cyclic」
強化 の 2 つの sorry-neutral 強化を済ませれば、全 conjunct が露出済 cite で証明可能**
(典型 fragile: typeP_structure/duality/15.2/15.1/15.5 = sorried だが 15.1/15.2/15.5 は mine、
14.2/14.7 は parametrize-stable)。Thm 14.7(h) 露出待ち (Lane H) は不要に。
**残 friction = conjunct 4 の Lemma 6.3 ↥M 適用 (subtype + coprime) のみ。** issue 8004 参照。

## 10. M_F 包含鎖 M_F ≤ M_σ ≤ M' ≤ M を §14 非依存に landing (2026-06-14, `b212b8d1`/`c64909c2`)

§14 非依存 API をさらに拡充 (section 3 の「Hall well-definedness が hard core」とは別軸):

- **`maxNilpotentNormalHall_le_Msigma` (M_F ≤ M_σ)** — mmd L4116「easy to see that M_F lies in M_σ」、
  **Theorem A の `MF≤Msigma` 節**。証明 = 候補 N の各素数 p で「N 冪零ゆえ Sylow_p char → M 正規 +
  N Hall ゆえ full Sylow → O_p(M)」、M 極大+G 単純で `normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot`
  により N_G(O_p(M))≤M ⟹ p∈σ(M) ⟹ `IsPiGroup.le_oPiCore` で N≤M_σ。
  道具: `sylowMap_eq_opiCoreInG_singleton_of_normal` / `opiCoreInG_singleton_ne_bot_of_sylowMap_eq` /
  `Sylow.ofCard` + `card_eq_multiplicity` + Hall coprime で factorization 一致。
- **`maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent` (M_F = M_σ ⟺ M_σ 冪零)** — 上記 (常に) +
  既存 `Msigma_le_maxNilpotentNormalHall_of_nilpotent` + M_F 常に冪零。**section 3 で「gated Theorem A
  の M_F≤M_σ と combine」としていたが、M_F≤M_σ が §14 非依存に取れたので iff も完全 §14 非依存に。**
- **`maxNilpotentNormalHall_le_derived` (M_F ≤ M')** — 上記 + `Msigma_le_derived`。Cor 15.5(c)「H⊆M'」。

⟹ M_F API は ≤M / ⊴ / 冪零 / ≤F(M) / ≤M_σ / ≤M' / iff まで §14 非依存に完備。
**残る §14 非依存余地は薄い** (M_F char in M は speculative; endpoint 配線は §14 gate ゆえ defer)。

## 11. Cor 15.6 conjunct-4 friction 解消 — §14非依存エンジン landing (2026-06-15, `2f7e0c5d`)

section 9 の「残 friction = conjunct 4 の Lemma 6.3 ↥M 適用 (subtype + coprime)」を解消。
mmd L4232 の Cor 15.6 証明は `K*⊆M''` に **Thm 14.7(h)** (M=KM', K∩M'=1) + **Lemma 6.3** を使う。
この節の **§14非依存コア**を抽出し sorry-free で landing:

- **`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'`** (S15_MF, sorry-free):
  仮説 = relative complement `IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)`
  (= M=KM' inside ↥M) + `coprime(|M'.subgroupOf M|, |K.subgroupOf M|)`。
  結論 = `M_σ ⊓ C_G(K) ≤ M''` (= K*⊆M'')。証明 = Lemma 6.3
  (`centralizer_inf_le_derivedInG_of_isComplement'`, proved) を ↥M 内で H=M'.subgroupOf M に適用
  → `C_{M'}(K)⊓M' ≤ M''`、K*=M_σ⊓C(K)≤M'⊓C(K) (∵ M_σ≤M')。**S12_E.Msigma_E_relations の
  Lemma 6.3 transport を M'↔M_σ・K↔E で流用** (`hid: (derivedInG M).subgroupOf M = commutator ↥M`,
  transport `(derivedInG H).map subtype = M''`, pointwise centralizer の Subtype.ext)。

- **Lemma 15.1 (`typeP_auxiliary_structure`) の K≠⊥ 節に上記エンジンの仮説 2 個を露出**
  (sorry-neutral、mmd 15.1(a)(b) に忠実): `IsComplement' (M'.subgroupOf M) (K.subgroupOf M)` +
  coprime。⟹ **Thm 14.7(h) 露出待ち (Lane H) は完全に不要**: Cor 15.6 conjunct 4 は
  Lemma 15.1 (mine, sorried) → エンジン (proved) の単一 cite に縮約。

**Cor 15.6 の残 friction 更新** (section 9 表の進捗):
| conjunct | 状態 (2026-06-15) |
|---|---|
| `Kstar≠⊥` | typeP_structure conjunct 2 (sorried §14, exposed) |
| `IsCyclic Kstar` | typeP_duality `IsCyclic(K⊔Kstar)` (sorried §14, exposed) |
| `Kstar≤MF` | case-split: MF=Msigma (inf_le) ∨ MF≠Msigma (15.2 exposed `Kstar≤MF`) — mine sorried |
| `Kstar≤M''` (4) | **✅ engine proved**; 仮説は Lemma 15.1 K≠⊥ 節 (mine sorried) から |
| `¬IsCyclic MF` (5) | engine `fittingInAmbient_cyclic_imp_derivedDerived_eq_bot` proved; **残 = 「MF cyclic⟹F(M) cyclic」** (Cor 15.5, 非自明: F(M)=F(M_σ)×Y 要、F(M_σ) vs M_F は等しくない ⟹ §15 構造依存・§14非依存抽出は不可) |

⟹ **Cor 15.6 の §14非依存に抽出可能な hard part (conjunct 4 の subtype juggling) は完了**。
残るは (i) §14 cite (typeP_structure/duality, parametrize-stable) の landing 待ち、
(ii) conjunct 5 の「MF cyclic⟹F(M) cyclic」= Cor 15.5 本体 (§15 構造、Thm 15.2 の type-P1 場合分け
要、§14 gate)。**conjunct 5 の §14非依存余地は無い** (F(M_σ)≠M_F ゆえ MF cyclic から F(M_σ) cyclic は
従わない; 真に Cor 15.5 b/Thm 15.2 g の decomposition が要る)。

## 参照

- mmd §16 schematic proof 依存表 = L4424–4449（Thm A–E の gate を 1 行で）。
- Prop 16.1 本文 + 証明 = L4478–4520（Thm A(8)/B(1-3)/C(2)(8)/15.7(c) 使用 → gated 確認）。
- Thm I = L4526、Thm II = L4548、tamely imbedded の定義 remark = L4560。
- Peterfalvi 消費側 = `OddOrder/Peterfalvi/S10_BGInterface.lean`（私の scaffold を既に cite）。
