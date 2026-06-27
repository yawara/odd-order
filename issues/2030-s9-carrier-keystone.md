---
id: 2030
slug: s9-carrier-keystone
title: "Pf §9 Clifford counts (9.8)-(9.10) + Section11CharacterData redesign — W3 keystone"
created: 2026-06-27
---

# Pf §9 Clifford counts + `Section11CharacterData` redesign — the W3 keystone

> lane-b (W3). This is the **single deep keystone** the entire W3 frontier converges on: both
> on-path obligations — (10.8)`no_typeV` (via (10.7)) and **(11.8)** (the bare `feitThompson` sorry
> residual `card_kappaHall_lt_of_isTypeIIIorIV`) — bottom out here.

## 背景: W3 が単一 keystone に de-risk された (2026-06-27)

本セッションで **(10.8) の機械的・算術 spine 全体**を実証明 (§7 入力 + line 81→83 + line-87 算術 +
ℚ chain + closer; issue 2020 / `notes/peterfalvi/s12_10_8_noncoherence.md`)。(10.8)・(11.8) の残りは
正確に §9 Clifford 指標理論のみ。

## architectural finding (精密)

`S11.Section11CharacterData data chief` (`S11_MaximalII_III_IV.lean:1479`) は **scaffold-by-design**:
- subgroup/numeric field は constrained: `C ≤ U`, `Uprime ≤ U`, `Cprime ≤ C`, `u_eq_card_quotient`。
- **character field は全て FREE** (property field 無し): `X`, `S`, `XOf`, `SOf`, `H0CprimeSupport`,
  `tau`, および `Prop` の `quotientSemidirectFrobenius`。

ゆえに §9 指標カウント定理は**全て `sorry`** で、現 carrier に対しては genuine に証明不可
(free な `chars.SOf`/`chars.S` 等に量化しているため):
- (9.8) `caseA_character_counts` — `sorry` (S11:2505)
- (9.9) `caseB_character_counts` — `sorry` (S11:2516)
- (9.10) `exceptional_case_frobenius_realization` — `sorry` (S11:2532)
- (9.11) `coherent_H0C_commutator` — (6.8) に wired (witness `sibleyTarget_H0C` が `sorry`, §14-gated)

## なぜ両 W3 obligation を塞ぐか

- **(10.8) `hB` / (10.7) `typeII_derived_frobenius`**: Pf (10.7) 証明 (04.12 line 71) は partner の
  chief factor に (9.10)/(9.8.b)/(9.9.b) を cite。`[S,S]=H⋊U` Frobenius (ゆえ `|U|≥7`,
  `|S|=|H||U|w₂`, TI-counting `hB` の `G₁ ⊆ (H#)^G ∪ V^G`) がこれを要する。
- **(11.8) `exists_zeta_residual_not_orthogonal`**: `S(HC)=S₁` の materialize (定数次数 w₁ の
  `(u−1)/q` 既約、`(U/C)⋊W₁` Frobenius) + (9.8)/(9.9)/(9.11) を要する
  (`notes/peterfalvi/s13_11_8_orthogonality.md`)。
- **(7.8.b)** ((10.8) 最後の §7 gate、`Hypothesis78` for `(M,A(M))`, `H=M'`): その *family* `T` 列挙
  (`Hypothesis76.zeta : Fin (n+1) → …` の degree-ratio 構造) 自体が同じ §9 chief-factor Clifford
  構造に支配される。

## 2026-06-27 lane-b (W3): task A の character-family 部分 COMPLETE (commit `9c41978a`)

**`Section11CharacterData` の character field を genuine 化** (full build 3884 green)。issue 冒頭の
「character field は全て FREE → §9 counts は genuine に証明不可」を直接解消した:

- **genuine families 新規** (S11, all sorry-free, `S12.inducedFamily` パターン):
  `huSub` (HU=H⊔U を ↥M 内に realise) / `hInHu` (H の HU 内表現) / `xiSet` (𝒳={χ∈Irr(HU)|H⊄Ker χ}) /
  `xiOf` (𝒳(Y)={χ∈𝒳|Y⊆Ker χ}) / `induceHU` (Ind_{HU}^M, canonical Invertible bake-in で desync 回避) /
  `induceHU_apply_one` (degree [M:HU]·χ(1)) / `sSet` (𝒮=Ind 𝒳) / `sOf` (𝒮(Y)=Ind 𝒳(Y))。
  基礎 API: `xiOf_subset_xiSet`/`mem_xiOf`/`xiOf_antitone`/`mem_sSet`/`mem_sOf`/`sOf_subset_sSet`/`sOf_antitone`。
- **carrier 再設計**: free な `X`/`S`/`XOf`/`SOf` field を削除 → genuine namespace defs
  (`X=xiSet`,`XOf=xiOf`,`S=sSet`,`SOf=sOf`) + `X_eq`/`XOf_eq`/`S_eq`/`SOf_eq` (rfl simp)。
  ⟹ (9.8)/(9.9)/(9.10) と (9.11) coherence consumer は Peterfalvi の **honest families** を参照
  (以前は free field ゆえ原理的に証明不能)。consumer (S12 `typeII_section11_coherence`,
  `sibleyTarget_H0C`) は `chars.S`/`tau`/`H0CprimeSupport` のみ使用で signature 不変、producer 不在ゆえ
  field 削除も安全。

**残 task A (carrier の部分群)**: `C=C_U(H̄)` (= U-action map `(quotientMulAutHom chief.N_aInvariant).comp
(U.subgroupOf(U⊔W1)).subtype` の `MonoidHom.ker` を G の部分群へ map-down、`u_eq_card_quotient` の range
と双対) / `Uprime=[U,U]=derivedInG U` / `Cprime=[C,C]=derivedInG C` を free field → genuine def 化。
counts が `chars.C`/`chars.Uprime`/`chars.Cprime` に量化するため、これらを pin しないと (9.8)/(9.9) は
genuine families に対しても未証明。pinning 自体は count を unlock しない (count は下記 B/C の deep Clifford)
が、count 証明の prerequisite。**fiddly だが honest-architecture prerequisite、次 brick**。

## 2026-06-27 lane-b (cont.): task A 完了 (subgroups genuine 化) + 文字基盤 (commits `153e866a`+本)

- **subgroup genuine 化** (commit `153e866a`): carrier の free な `C`/`Uprime`/`Cprime` (+ `_le_`) を
  削除し genuine def へ: `uActionHom` (U の H̄ 作用 hom) / `cSub` = C_U(H̄) = uActionHom の kernel を G へ
  map-down (`cSub_le_U`、first iso で |U:C|=u) / `uprimeSub`=derivedInG U / `cprimeSub`=derivedInG C +
  le 定理。⟹ **task A (carrier 再設計) 完了** = families + subgroups 全 genuine。
- **文字基盤** (本 commit): `induceHU_mem_ZIrr` (𝒮-member ∈ ℤ[Irr M]) + `sSet_subset_ZIrr` — counts が
  𝒮 を character として扱う foundation (`ClassFunction.induce_mem_ZIrr` cite)。
- **count 用 infra を特定**: Clifford inertia-induction が `InducedIrreducible.lean` に実在 =
  `isIrreducibleCharacter_induce_of_inertia_eq` (inertia=H ⟹ Ind irreducible) /
  `induce_eq_induce_iff_conj` (Ind 一致 ⟺ 共役) / `card_filter_induce_eq_index_inertia` /
  `sum_div_normSq_induce_image_eq`。§4 Dade は `S06_CertainType*` に (4.3)-(4.9) 実在。

## 2026-06-27 lane-b (cont.²): genuinization が露呈した count 文の imprecision (重要)

carrier を genuine 化したことで、free-field 時代に **vacuous だった (9.8)/(9.9)/(9.10) の文**が実内容を
持ち、Peterfalvi に対する **imprecision** が露呈した (build は green = `sorry` body ゆえ; ただし文が
不正確だと proof 不能)。count 証明前に Peterfalvi (`04.11`) に対し**文の再導出**が必要:

- **(9.9) conjunct 2** `∃ χ ∈ SOf Cprime, χ 1 = u` ⚠: SOf=𝒮 は induced family ゆえ member の degree は
  `[M:HU]·(source) = q·u = qu`((9.8.c) と同じ、(9.10) の "degree qu" とも整合)。Peterfalvi (9.9.a)
  「χ(1)=u」は **𝒳(H₀C')**-member (HU 文字) の degree であり、𝒮-member ではない。⟹ **`u` → `data.q*u`
  (qu)** に修正、または XOf(𝒳) を参照すべき ((9.8) は両所 qu で consistent)。
- **(9.10) hypothesis** `¬∃ χ ∈ SOf C, χ 1 = qu` ⚠: Peterfalvi (9.10) は **𝒮(H₀C')** (=Cprime) で記述。
  Lean は `SOf chars.C` (=C)。⟹ C/Cprime 要確認。
- **(9.8.c)/(9.8.d)/(9.9) の `SOf` 引数が H₀ join を省略** ⚠ (systematic): Peterfalvi は 𝒮(H₀C)/
  𝒮(H₀U')/𝒮(H₀C') (H₀ との join) を使うが、Lean は `SOf chars.C`/`SOf chars.Uprime`/`SOf chars.Cprime`
  (C/U'/C' 単独)。`sOf data Y` = {χ | Y⊆Ker} ゆえ H₀⊆Ker を要求しない → 別物。⟹ `SOf (chief.H0 ⊔ chars.C)`
  等に修正すべき (`chief.H0`/`chars.C` は共に `Subgroup G` ゆえ `⊔` 可)。((9.8.b) の `SOf chief.H0` は
  H₀ 単独で正しい。)
- 一般に SOf(𝒮, degree q·src) と XOf(𝒳, degree src) の使い分け・H₀ join・C/Cprime 引数を Peterfalvi
  (9.5)-(9.10) に対し総点検すること。これは genuine carrier 化の正の副産物 (scaffold 時代は検出不能)。
  **A' は count 証明 (B/C) の前提**: 文が正確になって初めて Clifford/Dade 証明が意味を持つ。

## やること (research-grade, multi-session)

- [x] **A': count 文監査 COMPLETE** (2026-06-28, commit `c170dd32`) — (9.8)/(9.9)/(9.10) を Peterfalvi
      忠実化 (H₀-join / C/C' / `IsIrreducibleCharacter` / 3 vacuity trap 除去)。下記「2026-06-28」節。
- [x] **A**: carrier 再設計 = families (commit `9c41978a`) + subgroups (commit `153e866a`) 全 genuine。
      残 free field = u (pin 済) / tau・H0CprimeSupport (S12-Dade layer) / quotientSemidirectFrobenius
      ((9.10) output) / CliffordCaseBData.field_model・Ubar_cyclic (下記、struct instance plumbing で True 据置)。
- [ ] **B: case-(b) (9.9)/(9.10)** — Singer field model。**✅ 構造核 FPF + char-side FPF + inertia 核 +
      abstract inertia reduction landed** (2026-06-28、下記節): `chiefFactor_caseB_action_fpf` (H̄⋊Ū Frobenius) +
      `chiefFactor_caseB_char_inertia` (θ̄ φU(g)-inv ⟹ φU(g)=1) + `caseB_char_inertia_inflation` (cont.⁵:
      typeP_conjAction-inv ⟹ φU(g)=1)。**(9.9.a) inertia は単一の残 step に縮小** = conjBy↔typeP_conjAction
      realization (H-in-HU ≅ ↥H 同定)。残 = その realization + (9.9.a) degree-u Clifford
      (`isIrreducibleCharacter_induce_of_inertia_eq`)、`|𝒮(H₀)| reducible-count = p−1` = (4.5)/(4.7) Dade on
      L=M/H₀ (S06 cite + 商 inflation)、(9.9.c) 例外含意。
- [ ] **C: case-(a) (9.8)** — (9.8.b,c) = (8.4.d)+(4.5)/(4.7) Dade for L=M/H₀ + θ=θ₁…θ_q1_C 構成;
      (9.8.d) = degree-qa 構成 + inertia counting (`card_filter_induce_eq_index_inertia`)。
      case-(a) factor 構造 (`CliffordCaseAData.Hpart`/`a`) を使う。
- [ ] **D: (9.11) `sibleyTarget_H0C`** 構造 witness (現状 (6.8)/Sibley 経由で §14-gated)。

## 2026-06-28 lane-b (W3): A' count 文監査 COMPLETE + B 構造核 (FPF) landed

**A' 完了** (commit `c170dd32`、full build 3884 green): carrier genuine 化で露呈した (9.8)/(9.9)/(9.10) の
imprecision を Peterfalvi (04.11) に対し総点検・修正。**consumer 0 ゆえ statement 改変は安全** (grep 確認)。
- **H₀-join (systematic)**: `𝒮(H₀C)`/`𝒮(H₀U')`/`𝒮(H₀C')` を `chars.SOf (chief.H0 ⊔ ·)` に修正。
- **C/C'**: (9.10) hypothesis を `C`→`Cprime` (Pf は 𝒮(H₀C') 記述)、(9.9.c) も C' 統一。
- **`IsIrreducibleCharacter`**: 「irreducible」「contains an irreducible」箇所に導入 (9.8.c/9.8.d/9.9.c/9.10)。
- **vacuity trap 除去**: (9.9) 恒真 `u∣qu` → genuine (9.9.a)「∀φ∈𝒮(H₀C'), φ(1)=qu」(定数次数=(5.7) 入力);
  偽 `(𝒮(H₀)).ncard=p−1` → `{φ∈𝒮(H₀)|¬irred}.ncard=p−1` (reducible-count); 恒偽傾向 `ncard=0` trigger →
  「contains no irreducible」(exceptional case で 𝒮(H₀C')=𝒮(H₀)≠∅)。

**B 構造核 = FPF (Frobenius `H̄⋊Ū`) landed** (本 commit、両 axiom-clean+AxiomsCheck 登録):
- **`fixedPointFree_of_aInvariant_irreducible_comm`** (一般、S11): A が K に φ:A→*MulAut K で作用し
  **像可換** (`Commute (φ a)(φ b)`) + irreducible (A-invariant は ⊥/⊤) なら φa≠1 ⟹ FPF (φa x=x→x=1)。
  証明 = Fix(φa) は A-invariant 部分群 (φa,φb 可換) ⟹ ⊥/⊤、⊤ なら φa=1。**Singer field model 不要・純群論**。
  像可換が仮説ゆえ U 非可換でも適用可 (Ū=U/C は可換)。
- **`chiefFactor_caseB_action_fpf`** (case-(b) 系、S11): case-(b) (hcaseB irreducible) で φU g≠1 (g∉C) ⟹
  H̄ 上 FPF。`hComm` (像可換、`chiefFactor_caseB_image_cyclic` と同じ `⁅a,b⁆∈[U,U]⊆C(H)`) + hcaseB を
  一般補題に渡す。これが (9.9) の degree-u Clifford 解析 (I(θ)∩U=C) の構造的入力。

**character-side FPF engine landed** (commit `4efc27ae` の次 commit、axiom-clean+AxiomsCheck 登録):
- **`eq_one_of_invariant_of_fixedPointFree`** (S11): FPF automorphism α (mathlib `MonoidHom.FixedPointFree`)
  が有限 abelian K に作用するとき、α-invariant な character θ:K→*M' (`∀x, θ(αx)=θx`) は trivial。
  証明 = displacement `x↦x/αx` が surjective (mathlib `commutatorMap_surjective`) ⟹ θ は im=K 上で
  消える。**これが inertia I_U(θ)=C の character-side 核**: nontrivial θ∈Irr(H̄) と g∉C で φU(g) FPF
  (`chiefFactor_caseB_action_fpf`) ⟹ θ は φU(g)-invariant でない ⟹ g∉I_U(θ) ⟹ I_U(θ)⊆C。
## 2026-06-28 (cont.): (9.9.a) inertia path 完全 mapping — **全 infra 存在を確認** (de-risked)

(9.9.a) の inertia `I_U(θ)=C` を repo infra で組む経路を完全に特定。**全部品が既存**と確認 (新規証明 0):
- **abelian fixed-class bridge = 既存** `ConjugationBrauer.card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot`
  (H̄ abelian `hcomm` + `C_G({g})⊓H̄=⊥` `hbot` ⟹ `#fixedClasses=1`)。**コメントが「(6.8)(c2) replacement for
  the full Frobenius condition、abelian 商 H̄ 用」と明記** = まさに (9.9) 用に作られている。
- **inertia 除外 = 既存** `not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one` (#fixedClasses=1 +
  nontrivial θ̄ ⟹ g∉inertia(θ̄))。
- **商 inflation 移送 = 既存** `mem_inertia_compHom_iff` (θ=θ̄∘q の inertia in G ⟺ mk' M g の inertia in G/M)。
- **Clifford 誘導次数 = 既存** `InducedIrreducible.isIrreducibleCharacter_induce_of_inertia_eq` /
  `card_filter_induce_eq_index_inertia` (Ind from inertia irreducible、degree=index)。

**∴ 残 (9.9.a) = 純 assembly (新 math 0、intricate な realization)**: (1) G'=HU/H₀ 実現 (H̄=H/H₀⊴G'、
q:H→*H̄)、(2) **`hbot` を FPF から**: u∉C で `C_{HU/H₀}({mk' u})⊓H̄=⊥` ⟺ φU(u) FPF (mk' h∈C(mk' u) ⟺
φU(u)(h̄)=h̄、`chiefFactor_caseB_action_fpf` で =1) — φU を HU/H₀ の conjugation に同定する realization が核、
(3) bridge→not_mem_inertia→mem_inertia_compHom_iff で I(θ)∩U=C、(4) χ=Ind_{HC}^{HU}(θλ) degree u → Ind^M qu。
これは multi-session の **assembly** (各 step は既存補題、繋ぎが realization-heavy)。

## 2026-06-28 (cont.²): §9 degree infrastructure landed (上記 (4) の足回り)

assembly step (4) の degree 計算の足回りを実証明 (axiom-clean+AxiomsCheck 登録、full build green):
- **`huSub_index_eq_q`**: `[M:HU] = q` = `|W₁|`。`HU = H⊔U = M' = derivedInG M` (型P 相補性
  `derivedInG_eq_fitting_sup_U`+`H_eq`) + `[M:M']=|W₁|` (`M_complement.index_eq_card`)。
- **`induceHU_apply_one_eq_q_mul`**: `(Ind_{HU}^M χ)(1) = q·χ(1)` (`induceHU_apply_one` の index を q に解決)。

⟹ **全 §9 count の degree 文 (μ_j(1)=qu、(9.8.c) qu、(9.8.d) qa、(9.9.a) qu) が `φ∈𝒮(Y) ⟹ φ(1)=q·χ(1)`
で `χ(1)=u`/`a` (Clifford 部) に reduce 可能**。(9.9.a) なら `induceHU_apply_one_eq_q_mul` で
`φ(1)=qu ⟺ χ(1)=u` に縮小 (χ(1)=u は inertia/Clifford = 残 assembly)。degree 側は完全に塞いだ。

**route 訂正 (honest)**: 上記 (2) の `hbot` 経路 (centralizer-inf-bot) が repo の inertia API と直結で、
本セッションの `eq_one_of_invariant_of_fixedPointFree` (char-as-Hom engine) は **不要**になる見込み
(後者は Irr(H̄)↔Hom(H̄,ℂˣ) bridge を要し遠回り; centralizer route は bridge 不要)。`eq_one_of_invariant_of_fixedPointFree`
は valid な汎用 lemma として残すが (9.9) critical path 上では centralizer route を使う。**FPF 構造核
`chiefFactor_caseB_action_fpf` は (2) `hbot` に必須**ゆえ critical path 上。

- **残 (9.9.a) = inertia API wiring + Clifford degree** (上記 de-risked plan で実行可能): engine
  (FPF) → centralizer-inf-bot `hbot` → `card_fixedPoints_...` → `not_mem_inertia_...` →
  `mem_inertia_compHom_iff` → I(θ)∩U=C → (1.7.a) χ=Ind_{HC}^{HU}(θλ) degree u → Ind_{HU}^M degree qu。

## 2026-06-28 (cont.³): abelian Irr↔Hom bridge landed — char-engine route が realization-free に

**`exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative`** (S11、axiom-clean+AxiomsCheck):
有限 abelian Γ の irreducible character (`IsIrreducibleCharacter`) は linear character `θ:Γ→*ℂˣ`
(`(θ g:ℂ)=φ g`)。証明 = 既約表現が 1 次元 (`finrank_eq_one_of_isMulCommutative`) ⟹ 各 ρg は scalar
`θ g` (`exists_smul_eq_of_finrank_eq_one`) ⟹ `φ g = trace(ρ g) = θ g`。

**route 再訂正 (cont. の訂正を更新)**: cont. で「char-engine は不要・遠回り」としたが、本 bridge で
**Irr(H̄)↔Hom bridge を実装したので char-engine route が viable かつ realization-free に**。
- char-engine route: θ̄∈Irr(H̄) を bridge で Hom 化 → `eq_one_of_invariant_of_fixedPointFree` (FPF φU(u) +
  invariant ⟹ trivial) で「nontrivial θ̄ は φU(u)-invariant でない」。**H̄ を subgroup に realize せず、抽象
  quotient ↥data.H⧸chief.N + 抽象 φU のまま**動く (conjByPerm/centralizer-inf-bot の realize 不要)。
- ⟹ 2 route が並立: (A) centralizer-inf-bot (conjByPerm、要 H̄-as-subgroup realize) / (B) char-engine+bridge
  (realization-free)。**(B) が realize plumbing を避けるぶん有利見込み**。
- **両 route 共通の残接続** = 「u∈I(θ) (ClassFunction.conjBy in HU) ⟺ θ̄∘φU(u)=θ̄ (inflation)」= θ が H̄
  経由 (H₀⊆ker) であることの conjBy↔φU 接続。これ + Clifford degree (Ind from inertia) が残 assembly。

⟹ **char-engine (commit 25ee31ba) は off-path でなく on-path に昇格** (bridge で接続)。FPF 核も degree infra も
on-path。残 = inflation 接続 (conjBy↔φU) + Clifford 誘導次数。

## 2026-06-28 (cont.⁴): char-side inertia `I_U(θ) ⊆ C` を実証明 (realization-free) — 核心 landed

**`chiefFactor_caseB_char_inertia`** (S11、axiom-clean+AxiomsCheck): case-(b) で θ∈Irr(H̄) nontrivial が
φU(g)-invariant (`∀x, θ(φU(g)x)=θ x`) ⟹ **φU(g)=1** (= g∈C)。= Peterfalvi (9.9.a) の character-side
inertia `I_U(θ)⊆C`。全 engine 統合 (背理法 φU(g)≠1 → FPF `chiefFactor_caseB_action_fpf` → bridge で θ を
Hom 化 → char-engine `eq_one_of_invariant_of_fixedPointFree` で θ trivial → nontrivial に矛盾)。
**抽象 quotient ↥data.H⧸chief.N + 抽象 φU のまま、H̄-as-subgroup realize 完全不要**。char-engine を
`[CommGroup K]`→`[Group K]` に緩和 (商の CommGroup instance 構成を回避、証明は abelian 不要だった)。

⟹ **(9.9.a) の inertia 核 (I_U(θ)⊆C) は完全に proven**。残 (9.9.a) = (i) (9.9) の χ∈Irr(HU) の Res_H
component θ が H̄ 経由 (nontrivial) であることの取り出し + 「u∈I_HU(θ) ⟺ θ̄ φU(u)-invariant」の inflation
接続 (この char_inertia が後者の右辺を閉じる)、(ii) Clifford 誘導次数 χ=Ind_{HC}^{HU}(linear) degree u →
Ind^M qu (degree infra 済)。**inertia の数学核は終わり、残は Clifford 取り出し/誘導の formalization**。

**carrier genuinization の保留** (honest-architecture note): `CliffordCaseBData.field_model`/`Ubar_cyclic`
(True placeholder) を FPF/IsCyclic に genuine 化しようとしたが、**struct field type が
`typeP_quotientCoprimeAction` を参照 → `[Finite G]` + `[chief.N.Normal]` instance を要し、structure 宣言
コンテキストで供給不能** (haveI 不可)。⟹ True 据置、FPF は standalone lemma で供給。B の (9.9) 証明では
`caseB_character_counts` に hcaseB を追加引数する (or clifford_dichotomy 経由) ことで `chiefFactor_caseB_action_fpf`
を cite して FPF を得る (struct plumbing を避ける pragmatic な access pattern)。

## 2026-06-28 (cont.⁵): abstract inertia reduction landed — (9.9.a) inertia が単一 step に縮小 (commit `599c9dad`)

cont.⁴ の inertia 核 `chiefFactor_caseB_char_inertia` (abstract: θ̄ φU(g)-invariant ⟹ φU(g)=1) を、
concrete な χ∈Irr(HU) の inertia 解析へ繋ぐ抽象側の bridge を 2 補題で締めた (両 sorry-free +
axiom-clean + AxiomsCheck 登録、full build 3884 green):

- **`compHom_typeP_conjAction_inflation`** (Lemma A、純代数、証明 `rfl`): 膨張
  `compHom (mk' N) : ClassFunction(↥H/N) → ClassFunction ↥H` が共役作用 `typeP_conjAction a` (↥H 上) と
  降下作用 `quotientMulAutHom a` (chief factor ↥H/N 上) を **intertwine** する
  (`compHom (typeP_conjAction a) (compHom (mk' N) θ̄) = compHom (mk' N) (compHom (quotientMulAutHom a) θ̄)`)。
  `quotientMulAutHom_apply_mk'` (`mk' N (a·h) = a·(mk' N h)`、rfl) が核。
- **`caseB_char_inertia_inflation`** (Lemma B): case-(b) で nontrivial irreducible θ̄ の膨張が
  `typeP_conjAction ((act.U.subtype) g)`-invariant ⟹ **φU(g)=1** (g∈C)。Lemma A で invariance を
  `compHom (mk' N) (φU(g)·θ̄) = compHom (mk' N) θ̄` に書換 → `compHom_injective_of_surjective` (mk' N 全射) で
  θ̄ が φU(g)-invariant → `chiefFactor_caseB_char_inertia` で φU(g)=1。

**∴ (9.9.a) の character-side inertia `I_U(θ)⊆C` は単一の残 step に縮小**: concrete HU-conjugation inertia
(`ClassFunction.conjBy in HU` 上、χ∈Irr(HU) の Res_H constituent θ の inertia) から Lemma B の入力
(`typeP_conjAction`-invariance of the inflation) を生む **conjBy↔typeP_conjAction realization**
(= H-in-HU `(H.subgroupOf M).subgroupOf HU` ≅ ↥data.H の同定 + conjBy(u:HU) = typeP_conjAction(u) の照合)。
S08 `inertia_eq_H_of_c2` が (6.8)(c2) で同型の realization を `mem_inertia_compHom_iff` 経由で実装済 = template。

**残 (9.9.a)** = (i) conjBy↔typeP_conjAction realization (上記、唯一の plumbing 残)、(ii) χ∈Irr(HU) の
Res_H から nontrivial constituent θ (H₀⊆ker) を取り出す + Clifford 誘導次数 χ=Ind_{HC}^{HU}(linear) degree u →
Ind^M qu (degree infra `induceHU_apply_one_eq_q_mul` 済)。**inertia 数学核は完了、残は realization + Clifford 取り出し**。

## 完了条件

(9.8)/(9.9)/(9.10) が genuine な carrier に対し sorry-free。これで (10.7)→(10.8)`hB` と (11.8) の
§9 依存が外れ、W3 の両 on-path obligation が char-content 的に閉じうる状態になる。

## 参照

- carrier: `OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean` `Section11CharacterData` (~1578);
  genuine families `xiSet`/`xiOf`/`sSet`/`sOf` (~1486-1570); counts `caseA_character_counts`(~2626)/
  `caseB_character_counts`(~2638)/`exceptional_case_frobenius_realization`(~2651);
  case-(b) Singer infra `chiefFactor_caseB_image_*` (~2092/2189/2376); `ChiefFactorData` producer
  `exists_chiefFactorData` (~1406)。
- consumers: `S12.typeII_derived_frobenius` (5765), `S12.exists_zeta_residual_not_orthogonal` (~6580),
  S13 type III/IV。
- 原典: Pf §9 = `references/peterfalvi/04.11` + (9.7)-(9.11); (10.7) 証明 = `04.12` line 71。
- 関連: issue 2020, `notes/peterfalvi/s13_11_8_orthogonality.md`,
  `notes/peterfalvi/s12_10_8_noncoherence.md`。
