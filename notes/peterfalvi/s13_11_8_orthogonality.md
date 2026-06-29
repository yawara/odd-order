# Peterfalvi (11.8) — the main orthogonality calculation (lane-b W3 handoff)

> repo `S13_MaximalIII_IV.lean` = **Pf §11** (file 番号 = §番号 −2)。(11.8) は `card_kappaHall_lt_of_isTypeIIIorIV`
> (FeitThompson:426, Pf (11.9.b)) の唯一の deep gate。**(10.9)-half + reduction spine は landed**
> (commits 257f9b45 / dcc00462)、残 = この (11.8) discharge + carrier bridge。
> mmd `04.13` の (11.8.1)-(11.8.4) は `[MISSING_PAGE_FAIL:3]` (p.66) で欠落 → 本ノートに PDF から復元
> ([[nougat-missing-page-recovery]]、references は gitignore ゆえ repo notes が durable home)。

## (11.8) statement

Hypothesis (11.2) (= (10.1) + M Type III/IV、`p=|W₂|`, `q=|W₁|`、`S(X)={χ∈S | X⊆Ker χ}`)。
ζ ∈ S(HC) に対し、`(μ₀−ζ)^τ − ∑_{0≤i<q} ω_{i0}^σ` は (Irr W)^σ に**直交しない**。

## 証明の骨格 (by contradiction)

**S₁ = S(HC)** と置く。`u = |U/C|`。(U/C)⋊W₁ は abelian kernel U/C の Frobenius 群ゆえ、
**S₁ は degree q の既約指標 (u−1)/q 個から成る** (= 定数次数 q!)。τ₁ = τ の Z[S₁] への拡張、
**(5.7) で存在** (定数次数 ⟹ coherent = `S07.coherent_of_constant_degree` ✅ 形式化済)。
α_{ij} = μ_{ij} − δμ_{i0} − nζ (0≤i<q, 0<j<p)。

### (11.8.1) d=u, δ=1, n=|S₁|=(u−1)/q
(9.8)/(9.9) で μ_j(1)=qu (j≠0) ⟹ d=μ_{ij}(1)=u。(U/C)⋊W₁ Frobenius ⟹ u≡1 (mod q) ⟹ δ=1,
n=(d−δ)/q=(u−1)/q。**gate**: (9.8)/(9.9) (§9=repo S11、char)。

### (11.8.2) α_{ij}^τ = X − nζ^{τ₁} + a·∑_{λ∈S₁} λ^{τ₁}, X ⊥ S₁^{τ₁}, a∈{0,1,2}; a=0 or 2 ⟹ X = ω_{ij}^σ − ω_{i0}^σ
(10.5) で α_{ij} 定義。λ∈S₁, λ≠ζ ⟹ (α_{ij}^τ,(ζ−λ)^τ)=(α_{ij},ζ−λ)=−n。∴ ∃ a∈ℤ, X⊥S₁^{τ₁} で
α_{ij}^τ=X−nζ^{τ₁}+a∑λ^{τ₁}。CS: (a−n)²+(|S₁|−1)a² = ‖−nζ^{τ₁}+a∑λ^{τ₁}‖² ≤ ‖α_{ij}^τ‖² = n²+2。
⟹ |S₁|a²−2an ≤ 2 ⟹ n(a²−2a)≤2 ⟹ 0≤a≤2。a=0 or 2 ⟹ ‖X‖²=2 ⟹ X=ω_{ij}^σ−ω_{i0}^σ ((10.5) と同様)。
**gate**: (10.5) (α image、repo S12 char)、‖α_{ij}^τ‖²=n²+2 (`muGridAlpha_tau_inner_self` ✅)。

### (11.8.3) β = α_{ij}^τ − (ω_{ij}^σ−ω_{i0}^σ) + nζ^{τ₁} は i,j 独立 (j≠0)、かつ β は real
(4.8): (α_{ij}−α_{ik})^τ=(μ_{ij}−μ_{ik})^τ=ω_{ij}^σ−ω_{ik}^σ ⟹ β_{ij} は j 独立。
(4.10): (α_{ij}−α_{0j})^τ=ω_{ij}^σ−ω_{i0}^σ−ω_{0j}^σ+ω_{00}^σ ⟹ β_{ij}=β_{0j}、i,j 独立。
real: (3.9.a)+(4.3.b)+(5.9) で β̄_{0j}=β_{0j}。**gate**: (4.8)/(4.10)/(3.9.a)/(4.3.b)/(5.9) (§4/§5、char)。

### (11.8.4) [背理法の仮定] (μ₀−ζ)^τ が (Irr W)^σ に直交すると仮定 ⟹ (μ₀−ζ)^τ = ∑_{0≤i<q} ω_{i0}^σ − ζ^{τ₁}
(μ₀−ζ)^τ=∑_i ω_{i0}^σ−χ と置くと ‖χ‖²=‖μ₀−ζ‖²−q=1 (← **これは coherence-free (10.9) `…residual…`
が与える直交補 + ‖μ₀−ζ‖²=q+1**)。⟨(μ₀−ζ)^τ,(ζ̄−ζ)^τ⟩ を見て χ=ζ^{τ₁} or −ζ̄^{τ₁}。|S₁|=2 ∧ χ=−ζ̄^{τ₁}
なら ζ^{τ₁}↔−ζ̄^{τ₁} を swap して χ=ζ^{τ₁} に正規化。**ここで landed (10.9) が直接効く** (χ⊥(Irr W)^σ, ‖χ‖²=1)。

### (11.8.5) a=0
((μ₀−ζ)^τ,α_{ij}^τ) を 2 通り計算: G 側 = (∑ω_{r0}^σ−ζ^{τ₁}, β+ω_{ij}^σ−ω_{i0}^σ−nζ^{τ₁}) =
(∑ω_{r0}^σ,β)−1−a+n; M 側 = (μ₀−ζ,α_{ij}) = −1+n。⟹ a=(∑ω_{r0}^σ,β)。(β,1_G)=(α_{ij},1_M)=0 (i≠0)
+ β real ⟹ a even。(11.8.2) X=ω_{ij}^σ−ω_{i0}^σ ⟹ β=a∑_{λ∈S₁}λ^{τ₁}、(5.3.b) で a=0。

### (11.8.6) 結論 (矛盾の導出)
(11.8.2)+(11.8.5): α_{ij}^τ=ω_{ij}^σ−ω_{i0}^σ−nζ^{τ₁} (∀i)。⟹ (μ_j−dζ)^τ=∑_i ω_{ij}^σ−dζ^{τ₁} (0<j<p)。
**S₂ = S(C)−S(HC)**。(9.11) で S(H₀C')−S(HC') coherent ⟹ (11.7) で S₂ coherent、(9.8.b)/(9.9.b) で
μ_k∈S₂ (k≠0)。τ₂ = τ の Z[S₂] 拡張。(5.3.b)/(5.5) で S₁^{τ₁}⊥S₂^{τ₂}。
**μ_j^{τ₂}=∑_i ω_{ij}^σ を示せば S(C)=S₁∪S₂ coherent ⟹ (11.3) `S_H0C_not_coherent` (✅ proven) と矛盾**。
μ_j^{τ₂}=∑_i ω_{ij}^σ: S₂∩Irr M=∅ なら (4.9) で τ₂ をそう定義可; λ∈S₂∩Irr M なら
((λ(1)μ_j−μ_j(1)λ)^τ,(μ_j−dζ)^τ)≠0 + (5.8)。

## 形式化プラン (next session, deep multi-step)

**foundation (available)**:
- (5.7) `S07.coherent_of_constant_degree` ✅ — S(HC) (定数次数 q) の coherence τ₁。
- (10.9) coherence-free `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` +
  `residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2` ✅ (本 W3 landed) — (11.8.4) の直交補核。
- (11.3) `S13.S_H0C_not_coherent` ✅ (cite-reduced) — 矛盾の到達先。
- ‖α_{ij}^τ‖²=2+n² `S12.muGridAlpha_tau_inner_self` ✅。
- (4.8)/(4.9)/(4.10) (§4 Dade)、(5.3.b)/(5.5)/(5.8)/(5.9) (§5)、(3.9.a) — 大半 formalized (要 grep 確認)。

**gate (char、未形式化 or sorried)**:
- (9.8)/(9.9)/(9.11) (§9=repo S11、char) — (11.8.1) μ_j(1)=qu, (11.8.6) S₂ coherence/μ_k∈S₂。
- S(HC)/S(C)/S₂ の carrier 材料化 (現 S13 `SOf` は opaque field)。
- §11 Hypothesis の τ₁ (S(HC)-coherent extension) と §10 carrier (muGrid/tau) の bridge (`hyp.base`)。

**攻略順 (上流優先)**: (11.8.1)→(11.8.2)→(11.8.3) は σ/α 算術 (§4/§5 cite)、(11.8.4) は landed (10.9) 直結、
(11.8.5)/(11.8.6) は矛盾導出 ((9.11)+(11.3))。**最大の負荷 = §9 (9.8/9.9/9.11) carrier + S(HC)/S₂ 材料化**。

## carrier bridge (card_kappaHall への翻訳、調査済)

- **|K| = w₁** ✅ available: `card_kappaHall_eq_derived_index` (|K|=[S:S']) + `TypePData.card_W1_eq_derived_index`
  (|W₁|=[S:S']) ⟹ |K|=|W₁|=w₁ (両者 M' を complement)。
- **|Kstar| = w₂**: `card_kappaHall_sup_Kstar` (|K⊔Kstar|=|K|·|Kstar|) + 要 |K⊔Kstar|=|W|=w₁·w₂
  (type-P duality、`typeP_duality`/BG 14.7(4)(5))。⟹ |K|=w₁ より |Kstar|=w₂。bridge は BG §14 duality。
- ∃ ζ∈S(HC) (degree w₁): S(HC) は (u−1)/q≥1 個の degree-q 既約 (Frobenius (U/C)⋊W₁) ⟹ nonempty + degree w₁ 自動。

## 結論

`card_kappaHall_lt_of_isTypeIIIorIV` = [build §10 carrier] + [∃ζ∈S(HC)] + [**genuine (11.8) = 本ノートの deep proof**]
+ [reduction spine ✅] + [|K|=w₁ ✅, |Kstar|=w₂ via duality]。**唯一の deep 残 = (11.8)** (multi-step char、
(5.7)/(10.9)/(11.3) foundation 上、§9 carrier が最大負荷)。

## 2026-06-26 update — carrier translation + reduction fully wired; sole gate = genuine (11.8)

The carrier bridge and reduction are now **landed and wired** into the FT consumer. **The bare
`feitThompson` sorry `card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson:426) is gone**; its proof
assembles:
- `|K| = w₁` (`card_kappaHall_eq_derived_index` + `TypePData.card_W1_eq_derived_index`, both = derived index);
- `|K*| = w₂` = **`card_Msigma_inf_centralizer_eq_card_W2`** (FeitThompson.lean, **axiom-clean**, AxiomsCheck-
  registered). The old "via type-P duality `card_kappaHall_sup_Kstar`+|K⊔Kstar|=|W|" route was replaced by a
  more direct centralizer argument: `W₂ = M' ⊓ C(W₁)` sandwiched by `W₂ ≤ M_F ≤ M_σ ≤ M'`, plus κ-Hall ↔ W₁
  Schur–Zassenhaus conjugacy (no need to identify `K ⊔ K*` with the type-data `W`);
- `w₂ < w₁` = `S12.w2_lt_w1_of_hypothesis` = `S12.exists_zeta_residual_not_orthogonal` (genuine (11.8))
  + `S12.w2_lt_w1_of_residual_not_orthogonal` (coherence-free reduction, already landed).

**Sole remaining W3 gate** = `S12.exists_zeta_residual_not_orthogonal`: ∃ `ζ ∈ inducedFamily M` (degree `w₁`,
Peterfalvi's `ζ ∈ S(HC)`) with the residual `(μ₀−ζ)^τ − ∑ω_{i0}^σ` **not** ⊥ `(Irr W)^σ`. This is the deep
(11.8.1)–(11.8.6) calculation documented above (needs `τ₁` from (5.7) on `S(HC)`, `τ₂` from (11.7)/(9.11),
the α-grid σ-identities, contradiction with (11.3)). The whole §9-char + `S(HC)`/`τ₁` materialization remains
the genuine multi-step load.

## 2026-06-29 update (lane-a) — ζ witness landed; 残 = orthogonality 計算のみ

`exists_zeta_residual_not_orthogonal` (S12:6762) の bare sorry を「**実 ζ witness 供給 + 3/4 conjunct
実証明**」へ還元 (commit 47158295)。
- ζ = `exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)`。
- ∈ inducedFamily / IsIrreducibleCharacter / ζ(1)=w₁ (defeq `hyp.w1=Nat.card hyp.typeP.W1`) 実証明。
- **残 sorry = (11.8.1)-(11.8.6) の orthogonality 計算のみ** (背理法本体)。

**確認済 available infra (次反復の grind 用、S12)**:
- ζ witness ✅ (上記)。τ₁ = `tau1` (S12:2716)。
- α^τ inner: `muGridAlpha_tau_inner_self` (3172, =2+n²)、`_zeta_sub_conj` (3396)、`_muColumn_sub_conj`
  (3489)、`_muColumn_self_sub_conj` (3523)。τ=τ₁ bridge: `tau_zeta_sub_conj_eq_tau1` (3552)、
  `tau_muColumn_sub_conj_eq_tau1` (3576)。τ₁ inner: `muGridAlpha_tau1_inner_muColumn` (3674)、
  `_self_sub_conj` (3716)、`muColumn_tau1_inner_self` (3743)。
- (10.9): `residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2` (6685)、
  `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` (6545)。矛盾先 (11.3): `S13.S_H0C_not_coherent`。
- aligned grid: `exists_intCast_alignedOmegaSigmaGrid_zero_column` (1312)、`alignedOmegaSigmaGrid_zero_zero` (1391)、
  `exists_rowInv_alignedOmegaSigma_conj` (1459)、`muGrid_column_sum_mem_inducedFamily` (2179)。

**次の攻略点**: by_contra h_orth → (11.8.1) n=(u−1)/q (要 μ_j(1)=qu = §9 counts cite) → (11.8.2) α^τ
CS bound a∈{0,1,2} (上記 inner lemmas) → (11.8.4) landed (10.9) 直結 → (11.8.5) a=0 → (11.8.6) S(C)
coherent ⟹ (11.3) 矛盾。§9 counts ((9.8)/(9.9)) は S11 で sorried、signature-contract で cite。

## 2026-06-29 update² (lane-a) — (11.8) assembly 精密 map; tractability 上方修正

(11.8) infra を deep dive した結果、当初の「§9 multi-session gated」は**過度に悲観的**と判明:
- **degree facts available (≠§9-gated)**: `muGrid_apply_one_eq` (S12:1852, μ_{ij}(1) 独立 j≠0)、
  `muGrid_apply_one_within_column` (1554)/`_cross_column` (1794) — CharacterParameters.degree_independent の source。
- **δ available**: `muColumnSign` (1865, columnFamily.sign) = CharacterParameters.delta の source。
- **核心 decomposition (S-coherent ⟹)**: `tau_muColumnZero_sub_zeta_eq` (5039, PROVEN):
  `coh : CoherentHypothesis` + params 条件下で `τ(μ₀-ζ) = ∑ω_{i0}^σ - ζ^{τ₁}` ⟹ residual = -ζ^{τ₁}。
  **向き注意**: これは「S coherent ⟹ decomposition」。(11.8) は**逆**「residual ⊥ ⟹ S coherent」が要点。
- **α^τ/τ₁ inner 群** (3172-3911): muGridAlpha_tau_inner_self (=2+n²) 他、CS bound (11.8.2) の source。
- **(11.3) target**: `S13.S_H0C_not_coherent` (S13:209)。

**`CoherentHypothesis hyp params` = full `S07.IsCoherent hyp.tau hyp.Sset hyp.A0`** (S=hyp.Sset 全体の
coherence)。⟹ (11.8) 証明構造 = by_contra (residual ⊥) → **S-coherence を構成** (CharacterParameters +
CoherentHypothesis を build) → (11.3) `S_H0C_not_coherent` と矛盾。

### concrete 攻略順 (次反復から、available infra で)
1. **`CharacterParameters hyp` 構成** (noncomputable def): zeta=exists_zeta、mu=muGrid、omegaSigma=
   alignedOmegaSigmaGrid、delta=muColumnSign、degree_independent=muGrid_apply_one_eq、d=共通 degree、
   n_formula/two_le_n=parity (d odd ∵ d∣|M| odd; δ=±1; w1 odd ⟹ n even>0)、alpha_support=muGrid_alpha_support、
   w2_prime/d_gt_one。**大半 available、parity と w2_prime が要 sourcing**。
2. **CoherentHypothesis (S(HC)=S₁ coherence τ₁)**: (5.7) `S07.coherent_of_constant_degree` (S(HC) 定数次数 q)。
   但し hyp.Sset = 全 S か S(HC) か要確認 (full S coherence が contradiction target)。
3. residual ⊥ ⟹ μ_j^{τ₂}=∑ω_{ij}^σ (11.8.5 の a=0) → τ₂ glue (S₂ from (9.11)/(11.7)) → S(C) coherent → (11.3) 矛盾。

**評価修正**: (11.8) は「最難 multi-session」だが §9 char counts に gated ではない (degree は muGrid 機構が供給済)。
available infra で assembly 可能な multi-step。次反復 = CharacterParameters 構成から。

## 2026-06-29 update³ (lane-a) — (11.8) construction 完全 recipe; 全 infra 確認済

(11.8) の全 building blocks を S07/S12 で確認。**blocked でなく、執行可能な large multi-step**:

**available (確認済)**:
- params + 全 (10.6.b) 条件: `exists_charParameters_full` (S12:3002)。
- norms: `inner_muColumnZero_sub_zeta_self` (‖μ₀-ζ‖²=w₁+1, S12:6625 で使用)、
  `muGrid_column_sum_inner_self` (‖∑μ_{ij}‖²=w₁, S12:2234)。
- σ-coefficient machinery: `sigmaCoeff_trichotomy` (S05 (3.8))、(10.9) 証明内で完全運用 (S12:6643)。
- S₁=S(HC)-coherence: (5.7) `coherent_of_constant_degree` (COMPLETE)。
- **union 構成 API** (S07_Coherence): `coherentPair` (3415)、`coherentUnion_of_glued` +variants (4407-4581)、
  `coherentPairChain`/`coherentOfPairChainCover` (4803/4841, (6.6) chain)、`coherentPair_fromDade` (5913,
  Dade base で {χ,χ̄} pair の IsCoherent)、`int_eq_zero_of_sq_mul_le_of_two_mul_lt` (5.6.2 core)。
- (11.3) target: `S13.S_H0C_not_coherent` (S13:209)。

**残執行 (large multi-step、新 infra 要)**:
1. **α-identities を S₁-τ₁ で再導出** (= 最大の負荷): 既存 `muGridAlpha_tau_*` (S12:3172-3947) は
   `coh : CoherentHypothesis` = **full S coherence** を要求するので by_contra (full coh 未取得) では使えない。
   (11.8.2)-(11.8.5) の α^τ CS bound・a=0 を **(5.7) の S₁-τ₁** で再導出する新 lemma 群が要る。
2. union 適用: 1 の identity (μ_j-dζ)^τ=∑ω_{ij}^σ-dζ^{τ₁} → `coherentUnion_of_glued`/`coherentPairChain` で
   S(C)=S₁∪S₂ の IsCoherent 構成。
3. τ₂ (S₂=S(C)-S(HC)): (9.11)/(11.7)。(9.11)=`coherent_H0C_commutator` (S11、sibleyTarget_H0C sorry、
   signature-contract で cite 可)。
4. by_contra: residual ⊥ ⟹ 1-3 で full S coherent 構成 → (11.3) `S_H0C_not_coherent` と矛盾。

**状態 (honest)**: (11.8) は完全に scope 済・全 infra 確認済で feasible。執行は **§11 char 終盤の最大の山** =
α-identities-with-S₁-τ₁ の新 lemma 群 (forward 版の S₁-coherence 版) を起点とする large multi-iteration。
ζ witness + params/by_contra 足場は landed (commits 47158295/25ad0aec)。次 = α-identity-with-S₁-τ₁ 起点。

## 2026-06-29 update⁴ (lane-a) — 執行 stack の build 順確定 (foundational bridge は未構築)

(11.8) 執行 = §10-11 coherence-construction infra stack の build。各層を確認した結果の build 順:

1. **§10 hyp → S07.Hypothesis bridge** (未構築・foundational): `S07.Hypothesis S A` は tau_isometry/
   conjugate_closed/no_real_characters/pairwise_orthogonal/difference_image/difference_images_orthogonal
   を要求。現状 `inducedFamily_closedUnderConjugate` (S12:83) のみ。残 (no_real/pairwise_orthogonal/
   difference_image 等) を inducedFamily/Dade tau から build。
2. **S(HC) materialization**: S_HC = {φ∈inducedFamily M | degree w₁} subfamily + constant-degree 条件。
3. **(5.7) 適用** → S₁=S(HC)-coherence τ₁ (`coherent_of_constant_degree`、Nonempty IsCoherent)。
4. **(11.8.x) identities を τ₁ で**: 一部 coh-free 済 (`muGridAlpha_tau_inner_self` =2+n², coh 不要)、
   τ₁ 絡み (`muGridAlpha_tau1_zeta_eq_neg_n`/`zeta_tau1_inner_self`) は full-coh 版あり→S₁-τ₁ 版が要る。
5. **union** (`coherentUnion_of_glued`/`coherentPairChain`) で S(C)=S₁∪S₂ coherence。
6. **τ₂** (S₂): (9.11) `coherent_H0C_commutator` (S11、sibleyTarget_H0C sorry、cite 可) + (11.7)。
7. **contradiction**: by_contra (residual ⊥) → 1-6 で full S coherent → (11.3) `S_H0C_not_coherent` 矛盾。

**honest 評価**: (11.8) は §11 char 終盤の最大の山で、執行は **layer 1 (S07.Hypothesis bridge) から始まる
深い未構築 infra stack** = major multi-iteration。setup (ζ witness/params/by_contra) + 完全 scope は landed。
**次 = layer 1: inducedFamily の S07.Hypothesis 性質 (no_real/pairwise_orthogonal/difference_image) を build**。

## 2026-06-29 update⁵ (lane-a) — assessment 修正: (11.8) infra は完備、no_real は組立で feasible

deep dive で update³/⁴ の「深い再帰未構築 stack」評価が**悲観的すぎた**と判明。layer 1 の核心
`no_real_characters (inducedFamily M)` の build に要る infra は**ほぼ全て available**:
- **Mackey ✅**: `card_mul_inner_induce` (two-fn, InducedIrreducible:135) `|H|⟨Ind θ,Ind ψ⟩=∑⟨θ,ψ^{x⁻¹}⟩`、
  `card_smul_restrict_induce` (99)、`card_mul_inner_self_induce` (120)。
- `ClassFunction.induce_conj` ✅ (S12:107 で使用)。
- conjByOrbit 機構 ✅: `card_conjByOrbit_eq_index_inertia` (227)、`mem_conjByOrbit`/`conjBy_mem_conjByOrbit`
  (Clifford:745/750)、Brauer perm (`ConjugationBrauer.lean`: conjByPerm 30、card_fixedPoints 186)。
- `not_isReal_of_ne_trivial_irreducible_of_odd_card` (S03:155) ✅。

**no_real の証明** (組立、feasible): χ=Ind θ∈inducedFamily, θ≠1。χ.IsReal ⟹ χ.conj=χ ⟹ Ind θ̄=Ind θ ⟹
⟨Ind θ,Ind θ⟩=⟨Ind θ,Ind θ̄⟩。Mackey: |H|⟨Ind θ,Ind θ̄⟩=∑⟨θ,θ̄^{x⁻¹}⟩。θ̄∉conjByOrbit(θ) なら全項 0 ⟹
⟨Ind θ,Ind θ̄⟩=0 だが ⟨Ind θ,Ind θ⟩≥1、矛盾。**θ̄∉conjByOrbit(θ)** = odd-orbit involution 論法:
conjByOrbit(θ) 奇数 card (=[M':I_θ]∣|M'| odd)、σ:η↦η̄ involution が θ̄∈orbit なら orbit を保ち、
**involution on odd-card set ⟹ fixed pt η** (η̄=η ⟹ η real ⟹ η=1 ⟹ 1∈orbit(θ) ⟹ θ=1 矛盾)。

**残る唯一の fiddly piece** = `involution on odd-card finite set has a fixed point` (mathlib に
`Function.Involutive`+odd card であるか要確認、無ければ「非不動点は 2 元 orbit ⟹ 偶数、total 奇数 ⟹ fixed 奇数≥1」で小 helper)。+ `conjBy_conj` (conj が conjBy と可換、ext+simp)。

**評価**: no_real は **available pieces + 2 小 helper (involution-fixed-pt, conjBy_conj) の組立**で feasible。
(11.8) は「最難だが blocked でない」。layer 1 → 7 を incremental commit で積める (commit は persist)。
次 = involution-fixed-pt helper + no_real 組立。

## 2026-06-29 update⁶ (lane-a) — no_real_characters 完成 + S07.Hypothesis character-side 3/6

(11.8) construction layer 1 (S07.Hypothesis for S=inducedFamily) を incremental build:
- **`inducedFamily_hasNoRealCharacters`** ✅ (9-lemma 集大成: conjBy_conj / conjPerm_conjBy_comm /
  conjPerm_mem_conjByOrbit / conjBy_trivial / trivial_not_mem_conjByOrbit /
  conjPerm_ne_self_of_mem_conjByOrbit / conjPerm_conjPerm / conjPerm_not_mem_conjByOrbit / assembly)。
  奇数位数 orbit-involution 論法 (`card_fixedPoints_modEq` p=2 + Brauer `conjPerm` + Mackey
  `card_mul_inner_induce` + `inner_induce_eq_zero_of_not_conj`)。
- **`inducedFamily_pairwiseOrthogonal`** ✅ (induce_eq_induce_iff_conj + inner_induce_eq_zero_of_not_conj)。

**S07.Hypothesis 進捗**: tau / tau_isometry / conjugate_closed ✅ (既存 inducedFamily_closedUnderConjugate) /
no_real_characters ✅ / pairwise_orthogonal ✅ / difference_image / difference_images_orthogonal。
⟹ **character-side 3/6 完了** (conjugate_closed, no_real, pairwise_orthogonal)。残 tau-side
(tau_isometry, difference_image, difference_images_orthogonal) = §10 hyp.tau (Dade isometry, S04) 依存
= 要調査の bridge。

**重要 gotcha** [[lean-induce-transport-instance-desync]]: induce 絡みは **`open scoped FiniteInduce`**
(finiteSubFintype/natCardInvC) で instance を carrier (hreal) と統一せよ。explicit haveI
(Fintype.ofFinite/invertibleOfNonzero) は instance diamond で induce 項が syntactic に非一致になり
congrArg/trans が type mismatch。

**次**: tau-side S07.Hypothesis 性質を §10 Dade isometry (hyp.tau, hyp.dadeData) から build →
full S07.Hypothesis 組立 → (5.7) S(HC)-coherence → (5.6) union → (11.8.1)-(11.8.6) calc。

## 2026-06-29 update⁷ (lane-a) — ⚠ honest reassessment: (11.8) coherence は Dade-based、global S07.Hypothesis でない

update⁵/⁶ で「S07.Hypothesis for inducedFamily を layer 1 として組む」とした approach を **修正**:
- **S07.Hypothesis.tau_isometry = `IsIntegralIsometry` (全 φ,ψ で等長 = global)**。だが Dade map は
  **supported のみ等長** (S07_Coherence:1573 docstring + S08:1452-1454 「global IsIntegralIsometry は
  FT に存在せず Dade-based に置換」)。⟹ inducedFamily + hyp.tau(Dade) で **global S07.Hypothesis は
  構成不可** (tau_isometry が偽)。
- (11.8) coherence の正しい機構 = **Dade-based `SibleyDadeHypothesis`** (S08:3265: dade datum + TI 条件
  のみ、family の character 性質は不要) → **`sibleySetup_is_coherent`** ((6.8) capstone, S08)。
- ⟹ 私の `inducedFamily_hasNoRealCharacters` / `inducedFamily_pairwiseOrthogonal` は **family の真の事実
  (build-green) だが coherence-construction path ではない**。これらは (11.8.x) の **inner-product 計算**
  (⟨μ_j,ζ⟩=0、family 直交性) が消費する genuine な補助事実として残る (orphaned でない、[[feedback-orphaned-not-reason-to-defer]])。

**(11.8) construction の修正版 path**:
1. S(HC)=S₁ coherence: Dade-based (sibleySetup_is_coherent or (5.7) の Dade 版) — **要再調査** ((5.7)
   coherent_of_constant_degree は global S07.Hypothesis を取るので FT 直適用は不可、Dade 版が要る)。
2. S₂=S(C)−S(HC) coherence: (9.11) coherent_H0C_commutator (S11、sibleyTarget_H0C sorry) + (11.7)。
3. (11.8.1)-(11.8.5) α-grid calc (no_real/pairwise_orthogonal + α^τ inner lemmas を消費)。
4. full S(C) coherence → (11.3) `S_H0C_not_coherent` 矛盾。

**教訓** [[verify-port-state-by-number-not-coq-name]]: coherence framework の機構 (global vs Dade-based)
を先に確認すべきだった。S07.Hypothesis の名前から global isometry path と誤読した。

**次**: (11.8) coherence の Dade-based path を S08 framework (SibleyDadeHypothesis/sibleySetup_is_coherent)
で再調査し、§11 hyp の S(HC)/S(C) にどう適用するか特定する。

## 2026-06-29 update⁸ (lane-a) — (11.8) coherence path 確定: §8 Dade machinery 適用

(11.8) coherence の Dade-based machinery は §8 に **substantially built**:
- `SibleyDadeHypothesis.certainTypeSet_isCoherent_tau_canonical` (S08_CaseBAssembly:170)、
  `nonempty_coherent_S_*` (S08_PGroupReduction:159/215/298/343)、`sibleySetup_is_coherent` ((6.8) capstone)、
  `coherentYset_extension_*` (S08_CaseBCoherence)。
- §13 (S13:198-226) は coherence を **hypothesis input** (`(hcoh : Nonempty (S07.IsCoherent ...))`) として取る。
  S12 `CoherentHypothesis` (2886) が `IsCoherent hyp.tau hyp.Sset hyp.A0` を束ねる。

**(11.8) construction の確定 path**:
1. S(HC)=S₁ / S(C) coherence: §8 Dade machinery (sibleySetup_is_coherent / certainTypeSet_isCoherent) を
   §11 hyp の S(HC)/S(C) に適用 — **SibleyDadeHypothesis for §11 setup を構築** (dade datum=hyp.dadeData,
   TI 条件) して coherence を得る。§8 capstone は citeable infra (lane 跨ぎ signature-contract 可)。
2. (11.8.1)-(11.8.5) α-grid calc: no_real/pairwise_orthogonal (built ✅) + α^τ inner lemmas (built) +
   τ₁=coh.tau1 を消費。
3. full S(C) coherence → (11.3) `S_H0C_not_coherent` 矛盾。

**残作業 = §11-specific な SibleyDadeHypothesis 構築 + §8 coherence 適用 + (11.8.x) calc**。深い multi-session
endgame だが機構は確定 (global S07.Hypothesis の誤読を是正済)。foundation (ζ witness/no_real/pairwise) は landed。

## 2026-06-29 update⁹ (lane-a) — S(HC) coherence の concrete path = coherentEqualDegree_fromDade

S₁=S(HC) coherence (FT-correct, Dade-based) の concrete API 確定:
- **`coherentEqualDegree_fromDade`** (S07_Coherence:5968): `(hyp:S04.Hypothesis G A L) (hconj) (χ:Fin n→Irr(↥L))
  (n≥2) (hχinj) (hdeg: 全 equal-degree) (hsuppdiff: χⱼ−χ₀ supported on A) (1∉A) →
  IsCoherent (dadeIntegralCharacterMap hyp ...) (Set.range χ) (supportInSubgroup A L)`。
- これが FT版 (5.7) (global S07.Hypothesis 不要、Dade base map で直接 coherent)。

**S(HC) coherence の構築 path**: S(HC) = inducedFamily の degree-q 既約族を **χ:Fin n→Irr(↥M) として
enumerate** (n=(u−1)/q≥2、Frobenius (U/C)⋊W₁ から) + equal-degree(全 q)/injective/supported-diff を示し
coherentEqualDegree_fromDade 適用 → IsCoherent hyp.tau (range χ=S(HC)) A0。**= S(HC) materialization** (§11
char work、substantial)。

**(11.8) 全 path 確定 (機構レベル)**: 
1. S(HC) coherence = coherentEqualDegree_fromDade + S(HC) materialization (上記)。
2. S(C) coherence = (9.11)/(11.7) + S₂ glue。
3. (11.8.1)-(11.8.5) α-grid calc (no_real/pairwise_orthogonal + α^τ inners + τ₁ 消費)。
4. (11.3) 矛盾。

機構は完全確定。残 = S(HC) materialization (次) → S₂ → calc。深い multi-session endgame だが各 API は特定済。

## 2026-06-29 update¹⁰ (lane-a) — 🛑 honest stall flag: (11.8) endgame は dedicated effort 要

**正直な評価 (要ユーザー判断)**: この session で (11.8) の **foundation (9 feat commits) + 完全機構確定**を
達成したが、endgame の core = **S(HC) full materialization** (degree-q 既約族を Frobenius (U/C)⋊W₁ /
§6 columnFamily から enumerate + coherentEqualDegree_fromDade の preconditions 確立) を **~7 反復 build
できず** (investigation/mapping に終始)。これは §6/Frobenius char theory の深い construction で、bloated な
loop 反復では production 不能。[[feedback-flag-poor-progress]] に従い churning を止め flag する。

**完了済 (build-green, committed)**:
- (11.8) `exists_zeta_residual_not_orthogonal`: 実 ζ witness 供給 + params/by_contra 構造。
- `inducedFamily_hasNoRealCharacters` (9-lemma chain) + `inducedFamily_pairwiseOrthogonal` (inducedFamily の
  真の character 事実、(11.8.x) calc が消費)。
- 全機構確定 (Dade-based、global S07.Hypothesis でない): coherence=coherentEqualDegree_fromDade /
  α^τ inners (muGridAlpha_tau_*) / 矛盾=S13.S_H0C_not_coherent。

**残 (deep multi-session、dedicated effort 推奨)**:
1. **S(HC) materialization** (bottleneck): degree-q 既約族 χ:Fin n→Irr(↥M) を §6 columnFamily /
   Frobenius count から enumerate。coherentEqualDegree_fromDade (S07:5968) に χ + equal-degree +
   supported-diff + n≥2 を渡す。**§6 framework (typePData_toS06Hypothesis 経由) との bridge が要点**。
2. S₂=S(C)−S(HC) coherence: (9.11)/(11.7)。
3. (11.8.1)-(11.8.6) α-grid calc: 上記 coherence の τ₁ + α^τ inners + no_real/pairwise (✅) で。
4. (11.3) 矛盾。

**要判断**: (11.8) endgame に dedicated focused session を割く (fresh /loop) か、lane-a を別 FT-path 作業へ
redirect するか。foundation + roadmap は本ノートに完備。

## 2026-06-29 update¹¹ (lane-a) — S(HC) coherence bridge **landed** (churn 脱却); 残 = enumeration のみ

update¹⁰ の「investigation churn」を脱し、**build-green な 2 commit** で S(HC) coherence の assembly を
materialize。coq `PFsection11.v` 併読で機構を確定 → 旧評価の「§6/Frobenius の深い再帰 stack」は**過大**と判明。

**landed (build-green, committed; leaf S12 3847 jobs)**:
1. **`Hypothesis.inducedFamily_sub_support`** (commit 3dede22f): `inducedFamily M` の任意の**等次数 2 元**
   `ζ₁,ζ₂` (ζ₁(1)=ζ₂(1)) の差 `ζ₁−ζ₂` が `A₀`-supported。`zeta_sub_conj_support` を一般化 (後者は
   conjugate-pair 特例として本補題に還元)。`coherentEqualDegree_fromDade` の `hsuppdiff` 前提そのもの。
2. **`Hypothesis.inducedFamily_isCoherent_of_equalDegreeFamily`** (commit 27481ebd): 等次数単射族
   `χ:Fin n→Irr(M)` (n≥2, 各 χⱼ∈inducedFamily, 同次数) → `IsCoherent hyp.tau (range χ) hyp.A0` を構成する
   `noncomputable def`。`coherentEqualDegree_fromDade` の**全前提を §10 Hypothesis から opaque field なしで
   discharge** (基底 map=hyp.tau 定義的一致 / support=hyp.A0 定義的一致 / hsuppdiff=上記① / 1∉A₀=
   `S04.Hypothesis.ne_one`)。

**coq 併読で確定した機構** (`PFsection11.v`):
- L607 `cohS1 : coherent S1 M^# tau := uniform_degree_coherence scohS1` — **S1=S(HC) coherence は uniform
  (equal) degree から直接**。= 本 Lean bridge `inducedFamily_isCoherent_of_equalDegreeFamily` (機構一致確認)。
- L206-208 `FTtype34_noncoherence` ((11.3)): S(H₀C) coherent ⟹ full S(1) coherent ⟹ `FTtype345_noncoherence`
  ((10.8)) と矛盾。⟹ (11.8) の contradiction target は **(10.8) full-S non-coherence** に bottom-out。
- L660 `cohS2 := subset_coherent (Ptype_core_coherence …)` — S2=S(C)−S(HC) coherence。

**残 = S(HC) enumeration のみ** (genuine だが scope 明確、bridge に渡すだけ):
- S(HC) = inducedFamily M の **degree-w₁ かつ既約**な元 = `{Ind θ | θ∈Irr(M') linear, θ≠1, θ が全 chiRestrict
  column を avoid}` を M-conjugacy で割った代表系を `Fin n→Irr(↥M)` に並べる。⚠ **inducedFamily は reducible な
  Ind θ も含む** (Ind θ 既約 ⟺ θ が column avoid、`exists_zeta_in_inducedFamily_degree_w1` の `havoid` 論法)、
  S(HC) は既約 degree-w₁ 元のみ。injective には M-orbit 代表系が要 (Clifford: Ind θ_i=Ind θ_j ⟺ θ_j∈orbit(θ_i))。
- n≥2 は conjugation-closure (ζ̄∈S(HC), 奇数位数で ζ̄≠ζ) で自動。
- S07 coherence producer は全て **Fin n-indexed** (set-level uniform-degree 版は repo に無し、確認済) ゆえ
  enumeration は回避不能。これが genuine な残工。

**次**: S(HC) enumeration (degree-w₁ 既約 subfamily の Fin n 化)。bridge は landed ゆえ、enumerate さえ
すれば S(HC) coherence が出る。その後 S₂ + glue + α-grid calc + (10.8) 矛盾。

## 2026-06-29 update¹² (lane-a) — 🎉 S(HC)=S₁ coherence **完全 materialized** (bottleneck 突破)

update¹⁰ で「deep multi-session, dedicated effort 要」と flag した **S(HC) materialization を sorry-free で
landed** (commit 5fdc6f12)。enumeration の「Clifford 数え上げ」評価は**過大**だった — **束ね型 IrreducibleCharacter
は単なる subtype** `{φ // IsIrreducibleCharacter φ}` ゆえ bundling は自由、**Finset.equivFin で injective Fin n 化が
自動** (M-orbit 明示不要)。

**`Hypothesis.SHC_isCoherent`** (S12, sorry-free):
`IsCoherent hyp.tau {φ | φ∈inducedFamily M ∧ IsIrreducibleCharacter φ ∧ φ(1)=w₁} hyp.A0`。
- degree-w₁ 既約 ∩ inducedFamily の Finset を `Finset.univ.filter` で取り `equivFin` で Fin n 化。
- bridge `inducedFamily_isCoherent_of_equalDegreeFamily` (前 commit) に渡す。
- n≥2 = {ζ,ζ̄} (`exists_zeta_in_inducedFamily_degree_w1` + `inducedFamily_hasNoRealCharacters` で distinct)。
- range = S₁ identity を Set.ext で示し transport。Prop ∃-elim は hcard (Prop) 内に閉込め (goal=Type)。
= coq `cohS1 := uniform_degree_coherence scohS1` (PFsection11 L607)。

**残 (11.8) endgame (S₁ coherence は供給済)**:
1. **S₂=S(C)−S(HC) coherence** (unconditional、coq L660 `cohS2 := subset_coherent (Ptype_core_coherence)`):
   Lean (9.11) `coherent_H0C_commutator` (S11) + (11.7)。S₁ と同様の materialization を S₂ にも。
2. **union glue** S(C)=S₁∪S₂: `coherentUnion_of_glued`/`coherentPairChain` (S07)。glue 条件は α-grid calc が供給。
3. **α-grid calc** (11.8.1)-(11.8.6): by_contra (residual⊥) → glue 条件確立 (α^τ inner lemmas `muGridAlpha_tau_*`
   消費)。これが残る genuine multi-step character calc。
4. **矛盾**: S(C) coherent → S(H₀C) coherent → (11.3)/(10.8) 矛盾。

本 session = 4 commit (3 Lean: inducedFamily_sub_support / _isCoherent_of_equalDegreeFamily / SHC_isCoherent
+ note)。update¹⁰ の churn (0 commit/7 反復) を脱し flagged bottleneck を突破。
