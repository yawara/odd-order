# BG §15 / §16 — faithfulness + dependency + gate audit (Lane G, 2026-06-14, post-13.6)

> ## ❄ FROZEN/SUPERSEDED (2026-07-02)
> §15/§16 は凍結 (残 5 sorry = S15_MF 2 [15.8/15.9] + S16_MainResults 3、全て
> overstatement/deep-char の off-spine = memory [[ft-settled-findings]]; feitThompson spine は
> Prop 16.1 のみ消費で sorry-free)。**Thm A の proof-time 復元プラン (§7/§12) は撤回** —
> `theoremA_maximal_structure` は do-not-prove-as-is
> (faithful = `theoremA_maximal_structure_faithful` S16:~4844)。以下は履歴。
>
> **2026-07-15 更新**: bare `theoremA_maximal_structure` は全 consumer の faithful 版移行を
> 再確認して retire 済み。canonical API = `theoremA_maximal_structure_faithful`。以下の bare
> monolith 復元案は引き続き撤回済みの履歴として読む。

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
| `fitting_not_ti_cases` (Thm 15.7) | L4234 | ⚠ **issue 3022 で逐条精査 (2026-07-18)**: (a) faithful / (b) **準恒真**（`∃ X` が book の `X=F(M)∩F(M)^g` を束縛せず `M_F≠1` と同値）/ (c) `=`→`≤` は**正当**（MathComp 準拠）/ (d) `E₃=1` のみ別 theorem `E3_eq_bot_of_not_fittingIsTI` に landed（bundled 結論には未収録）、`E₂⊴E`・`E/E₂≅E₁`・cyclic は未形式化 / (e) **恒真**（(a) が第2枝を与え排中律に潰れる）。⚠ 旧記載「(a)(b)(c) は捕捉」は (b) について過大評価だった |
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

### Cor 15.6 §14非依存 assembly skeleton landing (2026-06-15, `a33d4b6c`)

`typeP_kstar_in_mf_of_inputs` (sorry-free): Cor 15.6 の 5 conjunct を **§14/§15 の事実を仮説に
取って** 組み立てる skeleton。fragile sorried cite を持たない (robust)。仮説 = hKne/hcyc/hKsubMF/
hcompl/hcop/hFcyc (各々 typeP_structure/typeP_duality/15.2/Lemma 15.1/Cor 15.5 由来)。非自明
step = conjunct 4 (conjunct-4 engine) + conjunct 5 矛盾 (M''=1 engine)。conjunct 2 =
`Subgroup.isCyclic_of_le`。**⟹ §14 着地後の Cor 15.6 (`typeP_kstar_in_mf`) は「各仮説を単一 cite
で供給 + skeleton 適用」の clean assembly に縮約** (fragile な §14 cite は cascade 時に限定)。

**Cor 15.6 cascade-readiness = MAX (§14非依存に可能な全 groundwork 完了)**:
engine (conjunct 4) + skeleton (assembly) + Lemma 15.1 露出 (hcompl/hcop 供給) + 既存
conjunct-5 engine。残る supply-side (U 構成, typeP_structure/duality destructure, 15.2 case-split,
Cor 15.5 hFcyc) は §14/§15 gated ゆえ cascade 時 (§14 landing 後)。**他の §15/§16 endpoint は
deeply gated で §14非依存 skeleton の限界効用低 (§16 は §15 経由で landing から遠い)。Lane G の
§14非依存余地はこれで実質尽きた** ⟹ 次の substantive 進捗は §14 (Lane H, 10 sorry) / §13 (Lane F)
landing 待ち。

## 12. FT-critical §16 faithful 精査 + 復元プラン (2026-06-15, `fdd8798a`)

FT-critical spine (Prop 16.1 → Thm I → Thm II → Peterfalvi interface → S16.Hypothesis → FT) の
§16 endpoint を mmd 直接照合。**docstring 行参照のみ修正** (statement 不変・consumer 非破壊)。
substantive な lossy 復元は **ユーザー裁可 (2026-06-15) で defer**(speculative encoding を避け、
Pf consumer 出現時に実需要に合わせる)。本 section が復元プランの正本。

### 12.1 §16 → Peterfalvi consumer マップ (干渉の所在)

| §16 endpoint | consumer (Pf, **私の編集対象外**, build closure 内) | 消費形状 (壊すと full build 赤・直せない) |
|---|---|---|
| `proposition_type_classification` (Prop 16.1) | `S10_BGInterface` (`a7278d39`) | `.1` (=(a)) / `.2.1` (=(b)) / `.2.2.2.2.2.mpr` (=(f)) |
| `theoremI_…dichotomy` (Thm I) | `S10_MinimalSimpleStructure` (8.8, `6de1edea`) | `.2` を `⟨S,T,_W1,_W2,_W, hS,hT,hST,_hW,_hWcyc, hSnonI,hTnonI,hII,hcov⟩` で rcases (5 binder + 9 conjunct; **W データ _W1/_W2/_W/_hW/_hWcyc は discard**, 使用は hS/hT/hST/hSnonI/hTnonI/hII/hcov) |
| `theoremII_tame_embedding` (Thm II) | **未 cite** (theoremA-E/C/aSets も未 cite) | — (自由に復元可) |

### 12.2 忠実性 verdict (mmd 直接照合)

- **Prop 16.1** (mmd L4478): ✅ **faithful** — 6句 (a)-(f) 完全一致。docstring 行参照を L4352→L4478 修正 + 句注記追加。**変更不要**。
- **Thm I** (mmd L4526): ⚠ lossy。落ちている = (1) `W=W₁×W₂` cyclic の **normalizer-V 性質**「N_G(W₀)=W ∀ nonempty W₀⊆W−W₁−W₂」+ `W_i≠1`、(2) `S=W₁S'`, `T=W₂T'`, `S'∩W₁=1`, `T'∩W₂=1`, `S∩T=W`。**条件(5)「S,T とも II-V型」= `IsTypeNonI` (=¬TypeI=II-V) で既に捕捉済 (audit の「(5)脱落」は誤り)**。docstring 行参照は既に L4526 (正)。
- **Thm II** (mmd L4548): ⚠ lossy。落ちている = **(Tii) supporting-subgroup system** (D≠∅ ⟹ ∃ M₁..Mₙ of Type I/II, H_i=M_{iF}⊆M_i', (a)-(e)) + **(Tiii)** (∃ M_i Type II ⟹ M Frobenius/cyclic complement, M_F not TI)。現状は (Ti)+`D⊆A(M)`+`|𝓜(C_G(x))|=1`(∃! N + TypeI/II) のみ。docstring 行参照を L4416→L4548 修正。

### 12.3 復元プラン (Pf consumer 出現時に実行)

**Thm I (W-tame-embedding 構造)** — トリガー: Pf が (8.8) 超えで W=W₁×W₂ を消費し始めるとき。
- mmd (1)(2) を復元。**clean 復元 (各句を別 conjunct) は (8.8) の tuple 形状 (5 binder+9 conjunct) を変え rcases を壊す** → (8.8) 同時更新が必須 (Pf レーン協調) か、shape-preserving folding (discard される `_hW`/`_hWcyc` slot に normalizer-V/W_i≠1/S=W₁S' を畳み込む — hacky だが (8.8) 不変)。
- (1) normalizer-V: `∀ W₀ : Set G, W₀ ⊆ (↑W \ ↑W₁ \ ↑W₂) → W₀.Nonempty → Subgroup.normalizer W₀ = ↑W` (W₀ は**集合**、部分群でない点に注意)。`W₁≠⊥ ∧ W₂≠⊥`。
- (2) S=W₁S': `∃ S' T', S=W₁⊔S' ∧ T=W₂⊔T' ∧ S'⊓W₁=⊥ ∧ T'⊓W₂=⊥ ∧ S⊓T=W` (新 binder S' T' は top-level に出すと (8.8) 破壊 → 既存 conjunct 内に nest)。

**Thm II ((Tii)/(Tiii))** — トリガー: Pf (8.12)/(8.13) が tame-embedding を消費し始めるとき (現在 gated・未形式化 ⟹ encoding を実需要に合わせる)。
- (Tii): `D.Nonempty → ∃ (n:ℕ) (Mfam Kfam : Fin n → Subgroup G), (∀i, Mfam i∈max ∧ (IsTypeI∨IsTypeII)) ∧ (∀i, MF(Mfam i)≤derivedInG(Mfam i)) ∧ (a)..(e)`。
  - (a) `∀ i j, i≠j → Nat.Coprime (card (MF(Mfam i))) (card (MF(Mfam j)))`
  - (b) `∀ i, IsComplement' ((MF(Mfam i)).subgroupOf (Mfam i)) ((M⊓Mfam i).subgroupOf (Mfam i)) ∧ M⊓MF(Mfam i)=⊥`
  - (c) `∀ i, ∀ x∈X, x≠1 → Nat.Coprime (card (MF(Mfam i))) (card (centralizer{x}⊓M))`
  - (d) `∀ i, (A0Set (Mfam i) (Kfam i) \ ↑(MF(Mfam i))).Nonempty ∧ IsTISubset (A0Set (Mfam i) (Kfam i) \ ↑(MF(Mfam i))) (Mfam i)` — **per-M_i K_i が要 (A0Set は K 依存)** → Kfam を family data に含める。
  - (e) `∀ x∈D, ∃ y∈D, (∃g, y=g*x*g⁻¹) ∧ ∃ i, centralizer{y} = (centralizer{y}⊓MF(Mfam i)) ⊔ (centralizer{y}⊓M) ∧ centralizer{y}≤Mfam i` — **「C_{H_i}(y)C_M(y)」の積を ⊔ で表すのは over-approx** (要 complement/product 条件; モデル化判断は Pf 消費形に合わせる)。
- (Tiii): `(∃ i, IsTypeII (Mfam i)) → ∃ comp, IsFrobeniusGroup ↥M ((Msigma M).subgroupOf M) comp ∧ IsCyclic comp ∧ ¬ IsTISubset (sharpSubgroup (MF M)) (Subgroup.normalizer ↑(MF M))` (Frobenius kernel = M_σ?/complement cyclic; モデル化要確認)。
- **monitor gate**: 全て既存 sorry (Thm I/II) の結論強化 = sorry-neutral (新 sorry'd theorem 追加でない) ゆえ可。各復元後 **full build (S10_BGInterface/S10_MinimalSimpleStructure 含む) で consumer 非破壊を検証**。

### 12.4 現状の sufficiency

現 lossy statement は **現 consumer ((8.8), S10_BGInterface) には十分** (落ちた W データ / (Tii)/(Tiii) は現 consumer が消費しない)。lossy-ness が block するのは **deeper Pf** (§10-13 character theory, 現在 BG §14-15 gate で停止中)。⟹ defer は安全 (現 spine を block しない)。**deferred 復元タスク = issue 8005** (トリガー条件 + 復元手順を記載)。

## 11. Cor 15.6 `typeP_kstar_in_mf` ✅ COMPLETE (2026-06-15, `34d44c28`, issue 8004 closed)

section 9 の計画(迂回路 = Lemma 15.1 に `IsComplement'` 強化して §14 非依存に M=KM' 供給)は
**不要になった**。main 同期で **§14 Thm 14.7(h) が `typeP_duality` に露出済**(Lane H `1243d4c6`、
結論冒頭 `IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧ Coprime …`)なので、
**直接経路**で配線:

- `hKne` (K*≠⊥) ← `typeP_structure` (Prop 14.2) conjunct 2。U-factor は本体内で
  `Ch03.hall_E_exists (G:=↥M) ((kappa∪sigma)ᶜ)` + `map M.subtype` + `comap_map_eq_self_of_injective`
  の subtype roundtrip で生成(`hKM : K ≤ M` を faithful 仮説として追加、caller 無しで安全)。
- `hcyc`/`hcompl`/`hcop` ← `typeP_duality` (Thm 14.7(d)(h)) を直接 destructure(∃! witness から
  `IsCyclic(K⊔Kstar)` 抽出、Mstar 非依存)。
- `hKsubMF` ← `by_cases MF M = Msigma M`(eq: `inf_le_left`、ne: `mf_ne_msigma_typeP1_structure`)。
- `hFcyc` ← `fitting_decomposition` (Cor 15.5) 末尾 conjunct(`08e7dc5c` で露出済)。
- 組立 = sorry-free engine `typeP_kstar_in_mf_of_inputs`(conjunct 4 = `Msigma_inf_centralizer_le_
  derivedDerived_of_isComplement'` で Lemma 6.3 を ↥M 内適用済、§14 非依存)。

⟹ `typeP_kstar_in_mf` の `sorry` 消滅(S15_MF decl-sorry 9→8)。full build green (3817 jobs)、
AxiomsCheck OK。cite 先(14.2/14.7/15.2/15.5)は sorried だが §14 proof landing で自動 unconditional 化。
**残 §15 sorry = Lemma 15.1 / Thm 15.2 / Cor 15.3 / Cor 15.4 / Cor 15.5 / Thm 15.7 / Thm 15.8 /
Cor 15.9(8件)— いずれも multi-hour hard theorem(§14 proof 待ち)。** 次の FT-spine 標的 =
**Thm I** (`theoremI_…`, Peterfalvi S10:112 が consume)。

## 12. §15 substantive 結果の依存マップ — すべて §14 proof に gate (2026-06-15, mmd 精読)

section 3 の dependency 表(`Cor 15.3 deps = —` 等)は **不正確**。Cor 15.3–15.5 の mmd 証明
(L4204–4226)を精読した確定結果:

| 結果 | mmd 証明が使う上流 | §14非依存? |
|---|---|---|
| **Cor 15.3(a)** `C_M(H)=C_{M_σ}(H)X` | Prop 14.2(b1)(e) [§14] + Lemma 15.1(c) [mine, §14-gated] | ❌ |
| **Cor 15.3(b)** G-conj→N_M(H)-conj | Thm 14.4 [§14] + Thm 15.2 の Q [mine, §14-gated] + Frattini | ❌ |
| **Cor 15.4** `H nilp Hall→H⊆M_σ` | Cor 15.3(a) + σ-helper(✅ landed `sylow_le_Msigma_of_normalizer_le`)+ 冪零分解 | ❌(15.3 経由) |
| **Cor 15.5** Fitting 分解 | Lemma 15.1(a) + Thm 15.2(g) + Cor 15.3(a) | ❌ |
| **Lemma 15.1 / Thm 15.2** | Prop 14.2 / Thm 14.7 / 12.x [§14/§12] | ❌ |

⟹ **§15 の substantive 結果は 1 つも §14 非依存に閉じない。** 真の上流ゲート = Lane H の §14 proof
(Prop 14.2 / Thm 14.4 / Thm 14.7 — 現在 sorry、Lane H が Prop 14.2 case-τ₃ を実装中)。Lane G が
§14非依存にできるのは (i) infrastructure helper(σ-helper / M_F API / 冪零分解 helper)と
(ii) gated-endpoint skeleton(仮説パラメータ化 assembly、Cor 15.6 が例; `_of_inputs` engine 化)のみ。
**§14 proof が main に landing したら sync して gated endpoint を unconditional 化するのが最短。**

**Cor 15.4 の §14非依存 assembly 計画**(skeleton 化): S=非自明 Sylow of H → N_G(S) proper(G 単純・
S≠⊥・S≠G)→ M∈ℳ(N_G(S)) → S⊆M_σ(σ-helper ✅)→ H 冪零ゆえ H=S×R, R≤C_G(S)≤N_G(S)≤M,
各 H_q は C_M(S) 内の M の Sylow → Cor 15.3(a)[仮説化]で ≤M_σ → 冪零分解 helper で H≤M_σ。
冪零分解 helper(`isNilpotent_iff_forall_sylow_normal` 経由「H 冪零 ∧ 全 Sylow≤K ⟹ H≤K」)が次の leaf。

**✅ UPDATE 2026-06-15 (`ee1c7d41`): Cor 15.4 COMPLETE.** section 12 の「§15 は 1 つも cite で閉じない」は **Cor 15.6(`34d44c28`)と Cor 15.4(`ee1c7d41`)で部分的に覆った** — 両者とも本体 sorry-free で、cite 先(Cor 15.4 → Cor 15.3a; Cor 15.6 → 14.2/14.7/15.2/15.5)の sorry に gated。Cor 15.4 の reconstruction gap(π(H)⊆σ(M))は ChatGPT Pro 拡張で解決(`s15_4_chatgpt_answer.md`、核心 = Cor 15.3a の X が τ₂ 群なので C_M(S)/C_{M_σ}(S) が τ₂ 群 ⟹ q∉σ Sylow は埋め込みで τ₂ 強制→rank-2 矛盾)。新 helper: `sylow_le_Msigma_of_normalizer_le` / `eq_top_of_forall_sylow_le` / `eq_top...` / `normalizer_eq_self_of_mem_maximalSubgroups` / `sylow_isHall_piSet_subgroupOf_Msigma` / `sylow_le_Msigma_of_le_centralizer_sylow`(KEY)。**✅ UPDATE 2026-06-15 (`ec348bc3`+`b46f2e29`): Cor 15.5 COMPLETE + M_F Hall landed.** Cor 15.5
`fitting_decomposition` 本体 sorry-free(cite 先 Lemma15.1/Thm15.2/Cor15.3 にのみ gated)。ChatGPT
Pro 拡張 reconstruction(`s15_5_chatgpt_answer.md`)+ 手検証の 2 Case-II fixes(FIX1: F(M)⊆M_σ で Y=1;
FIX2: ¬IsCyclic(MF M) で conjunct 7、循環 15.6 回避)。最後の gate だった conjunct 5 ⊆ は
**`maxNilpotentNormalHall_isHall`(一般有限群・axiom-clean、新規 foundational)**で解決:
M_F=sSup{冪零正規 Hall} は正規 join=積 ゆえ各 p∈π(M_F) で full Sylow を含み Hall ⟹ O_{π(M_F)}(F(M))=M_F
⟹ F(M)=M_F×O_{π'}⟹ F(M)⊆C_M(M_F)·M_F。Thm 15.2 を 3 conjunct 強化(F(M)⊆M_σ / F(M)=Q⊔C_M(Q) /
¬IsCyclic(MF M)、faithful・sorried)。

**⟹ §15 connective corollary 完了: Cor 15.4 ✅ / Cor 15.5 ✅ / Cor 15.6 ✅(すべて本体 sorry-free)。
残 §15 = Lemma 15.1 / Thm 15.2(真の deep core, §14 proof + 構造論, multi-day)/ Cor 15.3(§16 Thm D
の一般元 conjugacy に gate)/ Thm 15.7-15.9(§16-feeder)。** 次は §16-feeder の cite-compress か
deep core(大commitment)— ユーザー裁可待ち。

## 13. `_of_inputs` skeleton 前倒し — 完了 + 「glue を持つ skeleton は尽きた」結論 (2026-06-15, `1d32a3cd`/`cd29c168`)

LAUNCH (2026-06-15 夜) の「sorry-free `_of_inputs` skeleton pre-positioning」を実行。
**結論: §15/§16 で genuine §14-非依存 glue を持つ skeleton は Cor 15.3 と Thm D の 2 つのみで、両方
landing 済。残りは全て passthrough(skeleton 無価値)か deep core(skeleton 化不能)。**

### 13.1 landing した 2 engine + 1 補題(全 sorry-free・axiom-clean)

- **`S15.mf_hall_centralizer_control_of_inputs`** (Cor 15.3, `1d32a3cd`): (a) passthrough +
  (b) **Frattini fusion glue**(genuine)。仮説 = `ha`(Prop 14.2(b1)(e)+Lem 15.1(c))/
  `hconj`(Thm 14.4+自己正規化)/`hfratt`(Thm 15.2 の Q + Frattini argument)。核心 glue =
  H⋬M 枝の交換子論法: `m=n·a`(n∈N_M(H),a∈Q)⟹ `w=axa⁻¹∈H` ∧ `wx⁻¹∈Q` ⟹ `wx⁻¹∈Q∩H=1`
  ⟹ `y=nxn⁻¹`。**Cor 15.3(b) は §16(`S16:384` Thm I fusion + Thm D(1))が consume = funnel 直結。**
- **`S15.normalizer_Msigma_eq_self`** (`cd29c168`): **N_G(M_σ)=M**(任意 maximal M)。
  M_σ=O_{σ(M)}(M)⊴M ⟹ M≤N_G(M_σ); 真の包含 ⟹ N_G(M_σ)=G(極大性)⟹ M_σ⊴G ⟹ M_σ∈{⊥,⊤}
  (simple、両方除外: `Msigma_ne_bot` / M_σ≤M⊊G)。**再利用可能な §14-非依存 brick。**
- **`S16.theoremD_..._of_inputs`** (Thm D, `cd29c168`): mmd L4440 が Thm D を **schematic** と明記
  (D(1)←15.3(b), D(2)←12.17, D(3)(4)←14.4(b)+A(8)+15.9)= upstream の純 assembly。**genuine glue
  は D(1)**: Cor 15.3(b)[H:=M_σ] の N_G(M_σ)-fusion を `normalizer_Msigma_eq_self` で M-fusion に
  upgrade。D(2)/D(3)/D(4) は source からそのまま。**Thm II conjunct 3(funnel 終端)を feed。**

### 13.2 残 §15/§16 endpoint の skeleton 適性 verdict(再調査不要)

| endpoint | verdict | 理由 |
|---|---|---|
| **Cor 15.3** | ✅ engine landed | Frattini glue(genuine) |
| **Thm D** | ✅ engine landed | D(1) の N_G(M_σ)=M glue(genuine) |
| **Thm A/B/C/E** | ❌ skeleton 無価値 | mmd schematic = **各 conjunct が単一 upstream 結果**(A: 10.2b/15.1a/14.2/15.2a等→各句; B: 12.1d/12.5b/15.1→各句; C/E 同様)。glue 0 ⟹ `_of_inputs` は恒等関数 `(h:Concl):Concl:=h` で無意味 |
| **Thm 15.2** | ❌ deep core | Q₀/Q₁ minimal-normal + Frobenius(Thm 3.10)論法が**証明本体**。§14 入力(Lem14.1/14.7f/14.2a)を仮説化しても残りは §1-§6 の hard math で、skeleton でなく multi-day 形式化 |
| **Thm 15.7** | ❌ deep core/large | case 解析(H abelian→type F / 非abelian→cond 2/3)+ rank 論法(Cor10.7/Thm2.5)が本体。§10-13 lemma を多数仮説化する必要 + glue は薄い |
| **Prop 16.1** | ❌ intricate | Type I-V 定義(条件 (Ii)-(Iv)/(T1)-(T7))と §14 family の照合が本体。多数 cite(A5/6/7/8, B1-4, C1/2/3/8/10, D1, 15.7c, 15.2a)+ 定義 unfold で ~50+行。skeleton でなく実証明 |
| **Thm II** | — defer | (Tii)/(Tiii) lossy 復元は Pf consumer 出現待ち(section 12.3、issue 8005) |

⟹ **Lane G の `_of_inputs` skeleton 余地は Cor 15.3 + Thm D で尽きた。** 次の substantive 進捗は
(i) §14(Lane H)proof landing 後の **wrapper 配線**(各 endpoint で「§14 cite + skeleton 適用」)、
(ii) deep core(15.2/15.7)の実証明(§14 + §1-§13 lemma landing 後、multi-day)、
(iii) deferred §14-非依存 brick。

### 13.3 §14-非依存 brick: Frattini factorization lemma ✅ DONE (issue 8010 closed, `cd418cb6`)

`S15.frattini_factorization`(sorry-free・axiom-clean)landing:
`Q⊴M, QH⊴M, Q∩H=1, coprime(|Q|,|H|), solvable ⟹ ∀m∈M, ∃n∈N_G(H),a∈Q, m=n·a`。
証明 = `IsComplement'.exists_conj_of_coprime`(SZ 補群共役, repo 既存)を ↥(Q⊔H) 内で適用
(H と conj m⁻¹•H は Q の補群 ⟹ Q-共役 q を得て n:=m·q, a:=q⁻¹)。complement は
`isComplement'_of_disjoint_and_mul_eq_univ`(disjoint=element-chase, mul_eq_univ=`normal_mul`+
`subgroupOf_sup`+`subgroupOf_self`)、共役の lift-back は `(Q⊔H).subtype` 経由
(`map_map`+intertwine `ext;rfl`+`map_comap_eq`)。

⟹ Cor 15.3 wrapper の `hfratt` は **Thm 15.2 の Q 供給 + `frattini_factorization` 単一 cite** に
縮約(§14 landing 後)。**残 binding constraint = `hconj`(Thm 14.4 conjugacy、§16 RData に deferred)**
ゆえ wrapper 完成は §16 RData / Thm 14.4 待ち。Frattini brick は §14-非依存 groundwork として完済。

⟹ **Lane G の §14-非依存 groundwork は完全に尽きた**(2 engine + N_G(M_σ)=M 補題 + Frattini brick)。
次の substantive 進捗は §14(Lane H)/ §16 RData(Thm 14.4 conjugacy)landing 待ち。

## 14. 🆕 Thm 15.2 証明の解禁 — Prop 14.2(a) landing による (2026-06-15 夜, Lane G 再開セッション)

section 11 の「§14-非依存 groundwork 尽きた」は **statement/skeleton レベルの結論**であって、
**Thm 15.2 の本体証明**については **Prop 14.2 (`typeP_structure`) landing 後に状況が変わった**。
prior audit は Prop 14.2 が gated だった時点の判定ゆえこの解禁を反映していない。

### 14.1 何が解禁されたか

mmd Thm 15.2 証明 (L4190–4202) の **step 2–5 はすべて landed upstream のみを使う**:
- **Prop 14.2(a)** = `typeP_structure` conjunct 1 `ActsPrimeOn (Msigma M) K` — **✅ landed sorry-free** (Lane H)。
- **Lemma 6.3(a)** = `commutator_eq_self_of_isComplement'_le_commutator` (S06:300, proved) / 第2結論 `centralizer_inf_le_derivedInG_of_isComplement'` (S06:396, proved)。
- **Thm 3.7** = `frobeniusKernelIsNilpotent` / `isNilpotent_of_normalizing_primeOrder_fixedPointFree` (S03c, proved)。
- **Thm 3.10** = `S03g.thm310` (proved, §3 サブプログラム完結)。
- **Prop 1.5(a)(d)** = `exists_aInvariant_hall` / `coprime_fixedPoints_quotient` (Isaacs Ch04, proved)。

⟹ **step 2–5（M_σ=[M_σ,K] → K\*≤Q=O_q(M) → M_σ/Q nilpotent → minimal-normal Q̄ chain →
Frobenius KD on Q̄ で p prime/|Q̄|=q^p/D'⊆C_D(Q̄) → (g) F(M)=QC_M(Q)）は §14-非依存に証明可能。**
§14-gate は **step 1 のみ**: `IsTypeP1 M`（Lemma 14.1）と `q=|K\*| prime`（Thm 14.7(f)）。

### 14.2 なぜ skeleton パターンが効かない（Cor 15.6 と違う点）

Cor 15.6 の `typeP_kstar_in_mf_of_inputs` が sorry-free 配線できたのは、入力 (K\*≠1 / K⊔K\* cyclic /
M=KM' / K\*⊆MF) が **すべて §14/§15 定理から cite 可能**だったから。**Thm 15.2 の構造的出力
(Q/D/Q0/Q̄/p/q) は cite 元が存在しない**（この定理自身の新規内容）⟹ `_of_inputs` engine を作っても
wrapper が入力を sorry-free に供給できず orphaned。さらに `IsTypeP1`/`q prime` も §14 から clean cite
不可（grep 済: 該当 §14 定理が無い）⟹ engine restructure は monitor の **sorry-不増 gate に抵触**（net +2）。

### 14.3 唯一の productive path = 証明本体を sorry-free conditional helper で積む

**§14-gated facts (`IsTypeP1`, `ActsPrimeOn`, `q prime`) を明示仮説に取った sorry-free 補題**として
step 2–5 を分割実装する（条件付きゆえ monitor 不抵触・net 0）。完成後、H が Lemma 14.1/Thm 14.7(f)
を landing した時点で wrapper (S15_MF:846) に配線（wrapper の sorry を置換, net −1）。
- これは **multi-session**（step 3 の minimal-normal Q̄ chain + step 4 の Frobenius KD on Q̄ が hard core、
  推定 ~500–800 行）。
- 🚨 **真の第一 gate = BG Theorem 3.8 が未形式化**（confirmed: grep 済）。Thm 15.2 step 2 は
  「[M_σ,K]⊄F(M_σ) ⟹ K\*∩F(M)≠1」に Thm 3.8 を contrapositive 適用するが、**repo に BG 3.8 が無い**:
  - mmd BG Thm 3.8 (L1221) = 「G=KR solvable odd, K⊴G, (1)(|R|,|K|)=1 (2)C_K(x)=C_K(R) ∀x∈R^# (3)C_{F(K)}(R)=1 ⟹ [K,R]⊆F(K)」。
  - S03 群 = S03b(Lem3.3)/c(Thm3.7)/d(Thm3.4)/e(Thm3.5)/f(Thm3.6)/g(Thm3.10) — **3.8/3.9 は欠番**。
  - `S04e_GorThm37:550` の "Theorem 3.8" は **Gorenstein "Finite Groups" の別定理**（p'-自己同型、App E 用）。BG 3.8 ではない。
  - ⟹ **Thm 15.2 を進めるには BG Theorem 3.8 の形式化が前提**（clean §14-非依存 §3 タスク、coprime-action 定理）。
- **Thm 15.2 依存の最終 ledger**: Prop 14.2(a)✅ / Lem 6.3(a)✅ / Thm 3.7✅ / **Thm 3.10 ⚠半分のみ** / Prop 1.5(a)(d)✅ /
  Thm 5.5✅(`solvableAut_of_narrow` S05:976) / **Thm 3.8 ❌→✅ (issue 8011 で形式化済)** / Lem 14.1・Thm 14.7(f) ⏳§14(H)。
  - **⚠ 2026-06-16 訂正 (Lane G)**: 「Thm 3.10✅」は **§15.2 用途には不正確**。repo は conclusion **(a) `|R| prime`
    の abelian-kernel 形のみ** (`prime_card_complement_of_frobenius_conj` / `prime_card_of_abelian_frobenius_weight`,
    Prop 14.2(g) 用 specialized)。**conclusion (b) `|M|=|C_M(R)|^p` と (c) `K'⊆C_K(M)` と一般 (非 abelian)
    kernel は未形式化**。⟹ step 4 (f) `|Q̄|=q^p` + (g) `D'⊆C_D(Q̄)` (kernel=D 非 abelian 可) は **full Thm 3.10
    の未形式化部分に gate** = 新 §3 task (step 2 の Thm 3.8 gate と同型, substantial/multi-session)。正本 = issue 8012 step-4 SCOPE 発見節。
- 第一 leaf 候補（Thm 3.8 後）: `M_σ=[M_σ,K]`（type-P1 complement + M_σ⊆M' を仮説に
  `commutator_eq_self_of_isComplement'_le_commutator` を ↥M 内適用、confirmed API）。

### 14.4 推奨（2026-06-15 夜, Lane G 再開セッション結論）

Thm 15.2 本体は FT keystone（Cor 15.3 の Q / Cor 15.6 の K\*⊆MF を供給）だが、§15 の残 6 sorry は
全て genuinely blocked:
- **Thm 15.2**: BG **Theorem 3.8 未形式化** + §14 facts（Lem 14.1/Thm 14.7f, H）。
- **Cor 15.3**: `hconj` が §16 sharp-transitivity（Thm 14.4 RData）依存 → §15 へ循環 import で構造ブロック。
- **Thm 15.7/15.8/15.9**: 深い §12/§13/FT。
- gated-endpoint skeleton が効く tractable 定理（Cor 15.4/15.5/15.6 + 2 engine）は完成済。

⟹ G の §15 で sorry を減らす clean な道は現状無い。productive な選択肢（**ユーザー/hub の戦略判断**）:
- **(a) BG Theorem 3.8 を形式化**（最有力）: §3 の唯一の未形式化前提を埋める。**§14-非依存・well-scoped・
  coprime-action 定理**（G=KR, K⊴G, 3条件 ⟹ [K,R]⊆F(K)）。Thm 15.2 step 2 を解禁（step 3-5 + §14 wiring は
  なお残るが clean な keystone 前進）。§3 領域だが §3 lane（a-keystone）は退役済ゆえ owner 空き。
- **(b) Lane H（§14, 10 sorry）/ Lane F（§13）支援に再配置**: §14 が §15 の gate ゆえ FT 最短。
- **(c) §15 light-touch**: thin sorry-free conditional helper を積む（Thm 3.8 待ちで step 2 止まり、低価値）。

section 11 の「§14-非依存余地尽きた」は **statement/skeleton レベルでは正**だが、本セッションで
**Thm 15.2 本体証明の解禁状況（Prop 14.2(a) landed、残 §3 gate = Thm 3.8 のみ）を精密化**した。

## 参照

- mmd §16 schematic proof 依存表 = L4424–4449（Thm A–E の gate を 1 行で）。
- Prop 16.1 本文 + 証明 = L4478–4520（Thm A(8)/B(1-3)/C(2)(8)/15.7(c) 使用 → gated 確認）。
- Thm I = L4526、Thm II = L4548、tamely imbedded の定義 remark = L4560。
- Peterfalvi 消費側 = `OddOrder/Peterfalvi/S10_BGInterface.lean`（私の scaffold を既に cite）。

## 2026-06-16 (Lane F): theoremE conjunct 3 (σ-disjointness) を ungated で landing

**`sigma_reps_pairwise_disjoint`** (`S16_MainResults`, commit `7047c92b`, sorry-free + axiom-clean,
AxiomsCheck 登録済) = BG Theorem E の **conjunct 3** (distinct maximal-subgroup conjugacy-class
reps `Mᵢ≠Mⱼ` の `σ(Mᵢ)∩σ(Mⱼ)=∅`)。

導出 (hoist でなく実導出): distinct class reps は `hreps` の `∃!` uniqueness で**非共役**
(両者が `Mᵢ` の class の唯一の rep → `Mᵢ=Mⱼ` 矛盾) → BG **Thm 13.9**
`OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate` (Lane F 既 landing, sorry-free) を直接適用。
真の追加仮説は `hrepsMax`(reps は maximal — Thm 13.9 が要求、class 代表系なら自動)のみ。

**⚠ hub STANDBY 評価への訂正**: 2026-06-16 LAUNCH の「F に ungated FT-critical task 無し
(11-agent review code-verified)」は**不完全**だった — F 自身の §13 landing (Thm 13.9, 2026-06-15) が
theoremE conjunct 3 を unblock しており、review が cross-reference し損ねていた。**教訓: lane が
自分の upstream を landing した直後は、その lane の downstream gate を再評価すべき**
([[feedback-verify-lane-connects-to-goal]] の逆方向: landing が新たに開ける扉)。

**残り §16 は再確認の上 gated** (over-mining せず検証済):
- theoremE conjunct 1 (counting) = Lem 14.5(c) gate / conjunct 2,5 (covering/π分割) = Cor 14.9 gate。
- conjunct 4 (tildeM disjointness) = landed 結果なし、M̃ counting machinery (Cor 14.9/Lem 14.5) gate。
- aSets_support_slice conjunct 1 (zTilde TI) = `S14:2771` = sorried `typeP_duality` (Thm 14.7) の conjunct ⟹ H long pole gate。
- theoremA-D / Prop 16.1 = §14 (Prop 14.2 は landed だが theoremA-D は更に 14.4/14.5/14.7 + §9-10 uniqueness 要)。

⟹ F は本 conjunct landing 後、再び H (14.5/14.7/14.9) + B (6.8) gate の STANDBY。

## 15. Thm 15.2 proof body 着手 — step 2 entry landed (2026-06-16, Lane G)

§14.3 の plan を実行開始。**BG Theorem 3.8 (`S03h.thm38`) を issue 8011 で形式化・main 合流済み**
(sorry-free + axiom-clean, AxiomsCheck 登録) ⟹ Thm 15.2 step 2 の §3 gate 解除。

本体は純 `_of_inputs` skeleton 不可 (§14.2) ゆえ **§14-gated facts を仮説化した sorry-free
conditional helper** で積む方針に確定。追跡 = **issue 8012** (step 2-5 の brick 分解 + friction 列挙)。

landed (sorry-free, leaf build green 3114 jobs):
- **step 2 entry** `msigma_eq_commutator_kappa_of_isComplement'` (S15_MF, Thm 15.2 直前):
  type-P1 complement `IsComplement'(M_σ.subgroupOf M)(K.subgroupOf M)` を仮説に、Lem 6.3(a)
  (`commutator_eq_self_of_isComplement'_le_commutator`) + `Msigma_le_derived` (M_σ⊆M') + M solvable
  で `⁅M_σ,K⁆=M_σ` (inside ↥M)。

次 brick (issue 8012) = **step 2 core = Thm 3.8 application** (`thm38` を G:=↥M, K↦M_σ.subgroupOf M,
R↦K.subgroupOf M で contrapositive 適用 → `C_{F(M_σ)}(K)≠1`)。friction 4 点 (M 奇数性 / κ-σ
coprimality / 冪零⟺`fittingInAmbient=self` 逆向き / R^# 条件形合わせ) は issue 8012 に記録。
`M_σ 非冪零` は `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent` の contrapositive (§14-非依存)。
`fittingInAmbient H=(fitting ↥H).map H.subtype` が thm38 結論形と一致するのは確認済 (S15_MF:345)。

**✅ step 2 core も同セッションで landed** (`centralizer_kappa_inf_fittingInAmbient_ne_bot_of_inputs`,
commit `0047671d`): friction (i)(iii)(iv) 解決、(ii) hcop は仮説化 (wrapper が Hall 構造から供給)。
支持 = 新 reusable `isNilpotent_of_fittingInAmbient_eq_self` (forward の converse, §14-非依存)。
import `S03h_Thm38` 追加。leaf build 3115 jobs, sorry 0。次 = **step 2 tail** (`K*⊆Q=O_q(M)` +
`M_σ/Q` 冪零 via Prop 1.5(d)+Thm 3.7) ⟹ (c)(d)。以降 step 3-5 は hard core (issue 8012)。
