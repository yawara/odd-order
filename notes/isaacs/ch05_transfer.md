# Isaacs Ch.5: Transfer — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.5 (pp. 147-180).
形式化先: `OddOrder/Isaacs/Ch05_Transfer/Main.lean`.
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 2799-3312.
ROADMAP 上の位置: **第 4 波 (Ch.4 後の Ch.4 → Ch.5 → Ch.6 シーケンス)** — 前提は Ch.3 (Hall), Ch.4 (Commutators) 中心. mmd には "Transfer is mathlib 既存で速い" と注記済.

## TL;DR — mathlib 大半カバー、FT 経路の核は Focal Subgroup (5.21)

**mathlib カバレッジは Ch.5 中で最も厚い**. `Mathlib/GroupTheory/Transfer.lean` (350 行) + `Focal.lean` (218 行) + `Schreier.lean` + `SpecificGroups/ZGroup.lean` で 主要結果 (transfer 定義・Burnside 5.13・cyclic Sylow 5.14・Focal Subgroup 5.21・Schur 5.7・Z-group 構造 5.15-5.16) を直接実装済. ⇒ ラッパー仕事中心、新規実装は **Thm 5.24 (nilpotent maximal)** などに残る. **§5C の Thm 5.13, §5D の Thm 5.20-5.23, §5E の Thm 5.25 / 5.26, Cor 5.29 / 5.30 は 2026-05-25 に sorry-free 完成**.

**FT 経路で最重要**: **Focal Subgroup Theorem (5.21)** — **BG が独自 Thm 1.17 として再述**し本文 3 ヶ所 (L2723, L5042, L5068) で使う. mathlib `commutator_inf_eq_focalSubgroup` / `ker_transferFocal_inf_eq_focalSubgroup` を BG 流ステートメントに橋渡しすれば足りる. **Burnside (5.13)** は BG が独自 Thm 1.18 として再述するが本文での明示利用は少ない (BG 索引と冒頭サマリ程度).

**Peterfalvi 本体 §4-§16 では transfer / focal を使わない**. Suzuki 定理付録 (05.4) のみで `T(x) = x^{|Q|+1}` という transfer-evaluation の直接利用が 1 件あるが ([H] = Huppert を citation し Isaacs ナンバリングは引かない). 従って Phase 2b 本体には Ch.5 直接被引用ゼロ.

## 章のセクション分割と全 30 結果

mmd 抽出では `### 5a`, `Problems 5A`, `### 5b`, `Problems 5b`, `### 5c`, `**Problems 5C**`, `**5D**`, `Problems 5D`, `### 5E`, `Problems 5E` が捕捉でき (5D は `### 5D` ヘッダ欠落だが本文中の `**5D**` でセクション開始は同定可、~L3097), § 5A-5E の 5 節構成が確定:

| § | mmd 行 | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 5A | 2801-2874 | Transfer 写像の定義・welldefinedness・準同型性 | 5.1 – 5.4 | transfer welldef (5.1), transfer 準同型 (5.2), Sylow 非可換性 (5.3), Schur multiplier corollary (5.4) |
| 5B | 2911-2986 | 中心への transfer = n 乗、Schur, Dietzmann | 5.5 – 5.10 | transfer-evaluation (5.5), **central transfer (5.6)**, **Schur (5.7)**, Dietzmann (5.10) |
| 5C | 2999-3080 | Hall transfer、Burnside、cyclic / abelian Sylow | 5.11 – 5.19 | Hall index (5.11), N_G(P) controls Cent fusion (5.12), **Burnside normal p-complement (5.13)**, cyclic smallest prime (5.14), Z-group solvable (5.15), Z-group 構造 (5.16-5.17), **abelian Sylow Burnside 強化 (5.18)** |
| 5D | ~3097-3209 | Focal subgroup theorem と p-transfer control | 5.20 – 5.24 | A^p(G) = ker(v) (5.20), **Focal Subgroup Theorem (5.21)**, H controls p-transfer (5.22-5.23), nilpotent maximal ⇒ p-group (5.24) |
| 5E | 3229-3300 | Frobenius normal p-complement theorem と系 | 5.25 – 5.30 | Sylow controls own fusion ⇔ normal p-comp (5.25), **Frobenius normal p-complement (5.26)**, q ∤ p^e−1 → normal p-comp (5.29), p odd central order-p → normal p-comp (5.30) |

### § 5A — Transfer definition + homomorphism (lines 2801-2874)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 5.1 | Theorem | transfer 写像 v: G → H/H' が transversal 選択に依存しない | L2827 |
| 5.2 | Theorem | transfer 写像は準同型 | L2843 |
| 5.3 | Theorem | p ∣ \|G' ∩ Z(G)\| ⇒ Sylow_p(G) 非可換 | L2857 |
| 5.4 | Corollary | Z ⊆ Z(Γ) ∩ Γ', p ∣ \|Z\| ⇒ Γ/Z の Sylow_p は noncyclic (Schur multiplier 文脈) | L2865 |

### § 5B — Central transfer, Schur, Dietzmann (lines 2911-2986)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 5.5 | Lemma   | transfer-evaluation lemma (orbital 分解) | L? (~2925, セクション冒頭) |
| 5.6 | Theorem | **Z ⊆ Z(G), \|G:Z\|=n ⇒ transfer to Z は g ↦ g^n; 特に冪写像が準同型** | L2941 |
| 5.7 | Theorem | **Schur**: \|G:Z(G)\| < ∞ ⇒ G' 有限 | L2953 |
| 5.8 | Lemma   | T が Z(G) の transversal ⇒ 全 commutator が [s,t] 形 (s, t ∈ T) | L2957 |
| 5.9 | Corollary | \|G:Z(G)\| = n ⇒ 全 commutator の n 乗 = 1 | L2963 |
| 5.10 | Theorem | **Dietzmann**: X ⊆ G 有限・共役閉・∃n, x^n=1 ⇒ ⟨X⟩ 有限 | L2969 |

### § 5C — Hall transfer, Burnside, cyclic / abelian Sylow (lines 2999-3080)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 5.11 | Lemma   | H Hall subgroup, v: G → H/H' transfer ⇒ v(H) = v(G), \|H:H∩ker v\| = \|G:ker v\| | L3005 |
| 5.12 | Lemma   | P ∈ Syl_p(G) ⇒ N_G(P) controls G-fusion in C_G(P) | L3015 |
| 5.13 | Theorem | **Burnside normal p-complement**: P ∈ Syl_p(G), P ⊆ Z(N_G(P)) ⇒ G has normal p-complement | L3021 |
| 5.14 | Corollary | P cyclic Sylow_p, p smallest prime ⇒ normal p-complement | L3035 |
| 5.15 | Corollary | 全 Sylow が cyclic ⇒ G solvable | L3041 |
| 5.16 | Theorem | 全 Sylow cyclic ⇒ G' と G/G' 共に cyclic で coprime | L3049 |
| 5.17 | Theorem | P cyclic Sylow_p ⇒ p は \|G'\|, \|G:G'\| のたかだか一方を割る | L3051 |
| 5.18 | Theorem | **P abelian Sylow_p ⇒ G' ∩ P と Z(N_G(P)) ∩ P が direct factor 形で分解** (Burnside 強化) | L3063 |
| 5.19 | Corollary | Sylow_2 が cyclic direct factor を最大に持つ direct product ⇒ G 単純でない | L3075 |

### § 5D — Focal Subgroup theorem (lines ~3097-3209)

5D の `### 5D` ヘッダは mmd 抽出失敗で本文中 `**5D**` マーカーのみ (~L3097). focal subgroup の定義 (L3132) と A^p(G) = O^p(G)·G' (L3128) が冒頭の説明文中に入る.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 5.20 | Theorem | v: G → P/P' transfer ⇒ ker(v) = A^p(G) (G^{ab,p'} kernel); `APrime_eq_transferFocal_ker` | L3130 |
| 5.21 | Theorem | **Focal Subgroup Theorem (D. G. Higman)**: Foc_G(P) = P ∩ G' = P ∩ A^p(G) = P ∩ ker(v); `focalSubgroupTheorem` | L3138 |
| 5.22 | Corollary | P ⊆ H controls G-fusion in P ⇒ H controls p-transfer; `APrime_eq_subgroupOf_APrime_of_controlsFusionIn` | L3180 |
| 5.23 | Corollary | abelian Sylow_p ⇒ N_G(P) controls p-transfer; `APrime_normalizer_eq_subgroupOf_APrime_of_isMulCommutative_sylow` | L3186 |
| 5.24 | Theorem | G 単純, H ⊆ G maximal nilpotent ⇒ H は p-group (Wielandt: 最大冪零部分群分類入口) | L3194 |

### § 5E — Frobenius normal p-complement theorem + corollaries (lines 3229-3300)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 5.25 | Theorem | G has normal p-complement ⇔ Sylow_p(G) controls its own G-fusion | L3233 |
| 5.26 | Theorem | **Frobenius normal p-complement** (3 同値条件: normal p-complement / 全 p-local が normal p-comp / N_G(X)/C_G(X) は p-group ∀ p-subgroup X) | L3247 |
| 5.27 | Lemma   | 5.26 内: (1) ⇒ (2) ⇒ (3) は容易 | L3257 |
| 5.28 | Lemma   | 全 p-subgroup X で N/C が p-group ⇒ P, Q ∈ Syl_p に対し Q = P^c, c ∈ C_G(P ∩ Q) | L3265 |
| 5.29 | Corollary | \|G\| = p^a m, q ∤ p^e−1 (1 ≤ e ≤ a) ⇒ G has normal p-complement | L3283 |
| 5.30 | Corollary | p odd, 全 order-p 元が中心 ⇒ G has normal p-complement | L3293 |

## mathlib カバレッジ

**Ch.5 主要結果のうち 50% 以上が mathlib 既収載**. 残りは概念的に近い既存 API の上に立つ薄い実装.

### 直接利用できるもの

| Isaacs | mathlib | 備考 |
|---|---|---|
| transfer 定義 (5.1, 5.2) | `MonoidHom.transfer` (`Mathlib/GroupTheory/Transfer.lean:144`) | transversal 経由の welldef + 準同型性込み |
| transfer evaluation (5.5) | `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot` (`Transfer.lean:161`) | orbital 分解 explicit 形 |
| 5.6 central transfer = pow | `MonoidHom.transfer_eq_pow` (`Transfer.lean:205`), `transfer_center_eq_pow` (`Transfer.lean:222`), `transferCenterPow` (`Transfer.lean:228`) | g ↦ g^n の準同型化 |
| **5.13 Burnside** | `MonoidHom.ker_transferSylow_isComplement'` (`Transfer.lean:275`) + `hasNormalPComplement_of_sylow_normalizer_le_centralizer` | project `HasNormalPComplement` 入口まで完了 |
| Burnside transfer (補) | `MonoidHom.transferSylow` (`Transfer.lean:244`) + `transferSylow_eq_pow` (`Transfer.lean:263`) | 5.13 の証明部品も完備 |
| 5.7 Schur | `Subgroup.card_commutator_le_of_finite_commutatorSet` (`Schreier.lean:208`) + `finite_commutator_of_finiteIndex_center` | mathlib bound 付き強化版 + Isaacs の finite-index-center 形 |
| **5.14 cyclic Sylow smallest prime** | `IsCyclic.isComplement'` (`Transfer.lean:339`) + `IsCyclic.normalizer_le_centralizer` (`Transfer.lean:308`) | 直接 |
| 5.15 Z-group solvable | `Mathlib/GroupTheory/SpecificGroups/ZGroup.lean` の `IsZGroup` API; `IsZGroup.isCyclic_commutator` (L144) と quotient cyclic で induct | 構造組み立てで導出可 |
| 5.16 Z-group G', G/G' cyclic + coprime | `IsZGroup.isCyclic_commutator` (`ZGroup.lean:144`) + `IsZGroup.isCyclic_abelianization` (L133) + `IsZGroup.coprime_commutator_index` (L280) | 直接 (3 ピースを bundle) |
| 5.16 G ≅ semidirect product | `isZGroup_iff_exists_mulEquiv` (`ZGroup.lean:315`) | 直接 |
| Foc_G(H) 定義 | `Subgroup.focalSubgroup` (`Focal.lean:58`), `focalSubgroupOf` (`Focal.lean:67`) | 直接 (元の生成 set はやや異なる: `{g ∈ H \| ∃ x ∈ H, u ∈ G, g = ⁅x, u⁆}`, Isaacs の `x^{-1}y` 形と同等) |
| transfer to focal | `Subgroup.transferFocal` (`Focal.lean:151`) | 直接 |
| **5.21 Focal Subgroup Theorem** | `Subgroup.commutator_inf_eq_focalSubgroup` (`Focal.lean`, ~L200) + `Subgroup.ker_transferFocal_inf_eq_focalSubgroup` (`Focal.lean:198`) + `focalSubgroupTheorem` | BG/Peterfalvi 入口まで完了 |
| Foc(P) ⊆ G' | `Subgroup.focalSubgroup_le_commutator` (`Focal.lean:105`) | 直接 |
| H/Foc(H) abelian | `IsMulCommutative (H ⧸ focalSubgroupOf H)` instance (`Focal.lean:146`) | 直接 |
| transfer surjectivity | `Subgroup.transferFocal_surjective` (`Focal.lean:180`) | 直接 |

### 新規実装が必要 (mathlib 未収載)

| Isaacs | 状況 | コスト見積もり |
|---|---|---|
| 5.3 \|G' ∩ Z\| 素数 ⇒ Sylow 非可換 | ✅ `not_isMulCommutative_sylow_of_dvd_card_commutator_inf_center` (2026-05-23, ~70 LOC). Cauchy in G' ∩ Z(G) + zpowers z normal (z central) + Sylow II conj + transfer id : P→P (P abelian) + transfer_eq_pow + map_commutatorElement | ✅ |
| 5.4 Schur multiplier 弱形 | ✅ `not_isMulCommutative_sylow_of_le_commutator_inf_center` (2026-05-23, ~7 LOC). 5.3 hypothesis weakening via `Subgroup.card_dvd_of_le`. フル形 (Sylow_p(Γ/Z) noncyclic) は `commutative_of_cyclic_center_quotient` 経由で追加可 | ✅ |
| 5.5 transfer-evaluation lemma | mathlib `transfer_eq_prod_quotient_orbitRel_zpowers_quot` で同等内容. Isaacs 流ステートメント (T_0 ⊆ T と n_t) への変換が必要 | 中 (ラッパー) |
| 5.8, 5.9 Z(G) transversal の commutator 構造 | ✅ `commutatorElement_eq_centerQuotient_out`, `finite_commutatorSet_of_finiteIndex_center`, `pow_index_center_eq_one_of_mem_commutator`, `commutatorElement_pow_index_center_eq_one` (2026-05-25). `Subgroup.LeftTransversal` bridge は増やさず `G ⧸ Z(G)` の `out` 代表元で形式化 | ✅ |
| 5.10 Dietzmann theorem | mathlib `Mathlib/GroupTheory` 全体を grep する限り Dietzmann 名は未登場. Schur 5.7 の証明で間接的に使用 (`Schreier.lean` で別経路の bound 経由) | **新規実装** (Isaacs §5B 末) |
| 5.11 Hall transfer | ✅ `ker_transfer_sup_eq_top_of_hall` (2026-05-23). 1st iso + Lagrange + Lem 3.16. ~10 LOC. | ✅ |
| 5.12 N_G(P) controls C_G(P) fusion | ✅ `normalizer_controls_centralizer_fusion` (2026-05-23). Sylow II in K = C_G(y) + `Sylow.smul_subtype` + `Sylow.subtype_injective` + `Sylow.smul_eq_iff_mem_normalizer` で ~50 LOC | ✅ |
| 5.17 cyclic Sylow ⇒ p ∤ \|G'\|·\|G:G'\| | ✅ `isaacs_thm_5_17` (2026-05-23; axiom-free 化 2026-05-25). Ch.4 §4D Thm 4.28 + 4.34 を `fitting_coprime_abelian_decomp` adapter で subgroup conjugation 形へ変換し、cyclic-pgroup-chain theorem と合わせる. Schur-Zassenhaus + Fitting + cyclic chain で C_P(K) = ⊥ vs ⁅P,K⁆ = ⊥ 場合分け, Burnside (mathlib `ker_transferSylow_isComplement'`) for case 1, P ⊆ G' for case 2 | ✅ |
| **5.18 abelian Sylow 強化 Burnside** | ✅ 2 形式: (i) **弱形** `abelian_sylow_commutator_inf_eq_focal` (mathlib `commutator_inf_eq_focalSubgroup` alias, G' ∩ P = focal P 形); (ii) **強形** `eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer` (2026-05-23, ~80 LOC, Isaacs p.166 流) — `G' ∩ P ∩ Z(N_G(P)) = 1` の要素形式. 強形は transfer id : P→P + transfer_eq_pow に Lem 5.12 (N_G(P) controls C_G(P) fusion) + `Commute.pow_right` を組み合わせ. **下流 Cor 5.19 (cyclic Sylow_2 ⇒ G 非単純) を unblock** | ✅ |
| 5.19 Sylow_2 direct product 系 ⇒ 非単純 | ✅ `not_isSimpleGroup_of_isCyclic_sylow_two` (2026-05-23, ~110 LOC, cyclic Sylow_2 特殊化). Helper `cyclic_finite_unique_order_two` (IsCyclic.card_orderOf_eq_totient + Nat.totient_two = 1). 主体: Cauchy + Thm 5.18 強形 + cyclic unique order-2. **axiom-free** (5.18 強形 + mathlib のみ, Ch.4 不要) | ✅ |
| 5.20 ker(v) = A^p(G) | ✅ `APrime_eq_transferFocal_ker` (2026-05-25). 既存 `A^p(G) ≤ ker(transferFocal)` と `A^p(G) ∩ P = Foc_G(P)` に、normal p-power index subgroup の index 比較を加えて full kernel equality 化 | ✅ |
| **5.21 Focal Subgroup Theorem** | ✅ `focalSubgroupTheorem` (2026-05-25). `G' ∩ P = Foc_G(P)`, `A^p(G) ∩ P = Foc_G(P)`, `ker(transferFocal) ∩ P = Foc_G(P)` を 1 つの BG §1.17 入口に package. | ✅ |
| 5.22 H controls fusion ⇒ controls p-transfer | ✅ `Subgroup.ControlsFusionIn` + focal core + `A^p(H)=H∩A^p(G)` equality (2026-05-25). transfer image cardinal phrasingは別 predicate化せず `APrime` equalityで保持 | ✅ |
| 5.23 abelian Sylow ⇒ N controls p-transfer | ✅ `APrime_normalizer_eq_subgroupOf_APrime_of_isMulCommutative_sylow` (2026-05-25). Lem 5.12 + 5.22 | ✅ |
| **5.24 G simple maximal nilpotent ⇒ p-group** | mathlib 未収載. transfer + Sylow + nilpotent 引数. **BG/Peterfalvi 直接被引用無し** | 後回し可 |
| 5.25 controls own fusion ⇔ normal p-comp | ✅ 完成 (2026-05-25). `OPrime`/`APrime` 定義 + `APrime_characteristic` + `A^p(N)=N` (`APrime_eq_top_of_eq_OPrime`) + transfer-focal kernel で Isaacs p.173 の `A^p(N)=N → Foc_N(Q)=Q` を bridge 過剰化せず実装. | ✅ |
| **5.26 Frobenius normal p-complement** | ✅ 完成 (2026-05-25). `hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer` は 5.25 + 5.27 + 5.28 で sorry-free. 追加で Cor 5.29/5.30 共通入口 `hasNormalPComplement_of_prime_subgroups_centralize` も実装. | ✅ |
| 5.27 (Lem, easy 1⇒2⇒3) | ✅ 完成 (2026-05-24, sorry+axiom-free, ~160 LOC). `def HasNormalPComplement p G` 導入 (mathlib 未収載). **Part 1** (1⇒2 strong, `hasNormalPComplement_of_subgroup`, ~70 LOC): Sylow `card_eq_multiplicity` + `not_dvd_index` + `relIndex_dvd_index_of_normal` + `factorization_mul` で `\|N \cap H\| * \|Q\| = \|H\|` 確立 + `isComplement'_of_coprime`. **Part 2** (2⇒3, `isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement`, ~80 LOC): `[K', X_n] ≤ K' ⊓ X_n = ⊥` (`commutator_le_inf` + coprime) ⇒ `K' ≤ C_n` ⇒ `C_n.index ∣ K'.index = p^a` (`index_dvd_of_le`) ⇒ `IsPGroup.of_card`. helper instance `centralizer_subgroupOf_normalizer_normal` (`normalizerMonoidHom_ker` 経由). X = ⊥ case は subgroup = ⊤ ⇒ index = 1 で吸収. | ✅ |
| 5.28 (Lem, key Sylow 共役) | ✅ 完成 (2026-05-24 overnight ralph-loop, sorry+axiom-free, ~250 LOC). Steps 1-11 全実装: 1-2 (P/Q ⊓ N > D via normalizers grow), 3-4 (S, T : Sylow p ↥N, R : Sylow p G), 5 (S ⊔ C = ⊤ via helper), 6 (Sylow II in ↥N), 7 (n = yC·sS via mem_sup_of_normal_left), 8 (T = yC • S via smul_eq_iff_mem_normalizer), 9 (Q ⊓ N ≤ yR via Sylow.coe_subgroup_smul + mem_pointwise_smul_iff_inv_smul_mem + .val 翻訳 + convert), 10 (index strict via index_dvd_of_le + cancellation), 11 (二回 IH chain + c = x · yC⁻¹ · z; c ∈ C_G(D) from centralizer_le + yC centralizes D ⇒ D ⊆ yR via h_smul_eq). | ✅ |
| 5.29 q ∤ p^e−1 ⇒ normal p-comp | ✅ 完成 (2026-05-25). `hasNormalPComplement_of_no_prime_dvd_pow_sub_one`: 5.26 の p-local criterion + `MulAction.fixedPoints` orbit counting (`IsPGroup.card_modEq_card_fixedPoints`) で非自明 q-作用から `q ∣ p^e - 1` を抽出. | ✅ |
| 5.30 p odd, 全 order-p 元中心 ⇒ normal p-comp | ✅ 完成 (2026-05-25). main 由来 Ch.4 `isaacs_thm_4_36` を q-subgroup action `QN →* MulAut X` に適用し、`hasNormalPComplement_of_prime_subgroups_centralize` で閉じた. | ✅ |

FT クリティカル公開面は `OddOrder.AxiomsCheck` で `focalSubgroupTheorem`, `hasNormalPComplement_iff_controlsOwnFusion`, `hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer`, `hasNormalPComplement_of_no_prime_dvd_pow_sub_one`, `normal_p_complement_of_order_p_central_odd` を確認対象に入れている.

### mathlib カバレッジ概観

| 種別 | 数 | 比率 |
|---|---|---|
| 直接利用可 (Transfer.lean / Focal.lean / Schreier.lean / ZGroup.lean) | ~12 / 30 | 40% |
| 同等概念有り、ラッパー必要 | ~5 / 30 | 17% |
| 新規実装が必要 | ~13 / 30 | 43% |

Ch.3 (Hall, Schur-Zassenhaus) と並んで **mathlib 既存資産の活用度が高い章**. ただし FT クリティカル §5E (Frobenius 5.26) は新規実装が中心.

## 下流被引用 (Isaacs Ch.6+, BG, Peterfalvi)

### Isaacs Ch.6-10 内 (mmd L3313-末尾を grep)

```
2 Theorem 5.26   ← Frobenius normal p-complement (Ch.6 で 2 回)
1 Theorem 5.6    ← central transfer
1 Theorem 5.16   ← Z-group 構造
1 Lemma 5.5      ← transfer evaluation
1 Lemma 5.12     ← N_G(P) controls C_G(P) fusion
1 Corollary 5.22 ← H controls p-transfer
```

⇒ **5.26 (Frobenius)** が下流被引用筆頭. Ch.6 §6.23 は Thompson の normal p-complement theorem (5.26 の odd-prime 強化) を扱うため自然.

### BG での引用 (`references/bg/local-analysis.mmd`)

| BG 名 | Isaacs 対応 | BG 出現 | 重要度 |
|---|---|---|---|
| **Theorem 1.17 (D. G. Higman, "Focal Subgroup Theorem")** | **Isaacs 5.21** | L507 定義, L2723, L5042, L5068 で利用. **索引にも記載 (L5552, L5586)** | **HIGH** |
| **Theorem 1.18 (Burnside)** | **Isaacs 5.13** | L513 定義. 本文での明示利用は限定的だが索引にあり (L5506 Burnside) | MEDIUM |
| Burnside p^a q^b (別) | Isaacs §6.23 周辺 | L2633, L2745 等で言及 (Goldschmidt の char-free proof 引用) | (Ch.6 範疇) |

BG は Isaacs ナンバリングではなく `**G**` (= Gorenstein 1968) を引用するスタイルだが, **§5.21 Focal Subgroup と §5.13 Burnside は BG 自身が再述して使う** という形で Ch.5 への依存が明確.

### Peterfalvi 本体 §4-§16 (`references/peterfalvi/04.*.mmd`)

```
04.X 全ファイルで transfer / focal / Higman / Burnside の直接出現: 0 件
```

⇒ Peterfalvi character theory 本体は Ch.5 内容を **使わない**. 指標論ベースの議論で transfer 写像は登場しない.

### Peterfalvi Suzuki 付録 (05.X)

| ファイル | 文脈 | Ch.5 対応 |
|---|---|---|
| 05.0 / 05.1 Introduction | "theorems based on transfer guarantee that O^{2'}(G) ≠ G" | 一般的言及 |
| 05.4 The First Case (p.108-114) | L85: "Let T be the transfer from G to H/(QKW) ([H], Kapitel IV, §§1)" — transfer-evaluation 直接利用で `T(x) = x^{|Q|+1}` を計算 | **5.5 transfer-evaluation の特殊化**, [H] = Huppert を citation. Isaacs ナンバリングは引かない |

⇒ Suzuki 定理付録のみが transfer を素朴に使う. ステートメントは Isaacs と同等だが Phase 2b Suzuki 付録で **その場 wrapper でも実装可能** な単発利用.

## 章内依存 (Ch.5 内で 5.X が引用される頻度)

`awk` で Ch.5 本文 (L2799-3312) を切り出し grep:

```
最頻 被引用:
- 5.6  (central transfer = pow)        — 5.7 Schur の核
- 5.10 (Dietzmann)                     — 5.7 Schur の核 (5.6 + 5.10)
- 5.5  (transfer evaluation)            — 5.6, 5.18, 5.21 の証明部品
- 5.12 (N_G(P) controls C_G(P))         — 5.13, 5.22 の核
- 5.18 (abelian Sylow Burnside)         — 5.19 系の核
- 5.21 (Focal Subgroup Theorem)         — 5.22, 5.23 の核
- 5.25 (Sylow controls own fusion)      — 5.26 Frobenius の核
- 5.26 (Frobenius normal p-comp)        — 5.29, 5.30 の核
```

**章内ハブ**:
- §5A → §5B 軸: 5.1 → 5.2 → 5.5 → 5.6 → (5.7, 5.10)
- §5C 軸: 5.11 → 5.12 → 5.13 → 5.14 → 5.18 → 5.19
- §5D 軸: (5.5 + 5.12 + 5.18 経由) → 5.21 → (5.22, 5.23, 5.24)
- §5E 軸: (5.21 経由) → 5.25 → 5.26 → 5.27/5.28 → (5.29, 5.30)

## 着手順 (提案)

FT クリティカル度 + mathlib カバレッジ + 章内依存で並べる:

1. **§5A 全 (5.1-5.4)**: mathlib `MonoidHom.transfer` のラッパー + 5.3, 5.4 を新規実装. ウォームアップ.
2. **§5B 核 (5.5, 5.6, 5.7)**: mathlib `transfer_eq_prod_quotient_orbitRel_zpowers_quot`, `transfer_center_eq_pow`, `card_commutator_le_of_finite_commutatorSet` をラップ.
3. **§5B 残り (5.8, 5.9, 5.10)**: 5.8/5.9 は quotient `out` 代表元版で完成. 5.10 Dietzmann は新規実装が必要だが、mathlib の Schreier 経路で 5.7 は既に閉じているため後回し可.
4. **§5C 前半 (5.11, 5.12, 5.13, 5.14)**: 5.13 Burnside は `hasNormalPComplement_of_sylow_normalizer_le_centralizer` で project API 接続済み, 5.14 は `IsCyclic.isComplement'` 直接. 5.11, 5.12 は新規実装.
5. **§5C 後半 (5.15, 5.16, 5.17)**: mathlib `IsZGroup` API でほぼ直接. 5.17 は単一 prime に分離.
6. **§5D 核 (5.20, 5.21, 5.22, 5.23)**: **FT クリティカル**. `APrime_eq_transferFocal_ker` と mathlib `Focal.lean` の API を Isaacs ステートメントに橋渡し済み. 5.21 = BG Thm 1.17 として再述.
7. **§5C/5D 残り (5.18, 5.19, 5.24)**: 5.18 が中. 5.24 は単独で重い証明だが Ch.6+ 被引用無いので後回し可.
8. **§5E (5.25, 5.26, 5.27, 5.28, 5.29, 5.30)**: **FT クリティカル**. 5.25-5.30 は完成. 5.30 (p odd) は Ch.4 Thm 4.36 を q-subgroup action に適用して閉じた.

優先度 (FT クリティカル度): **5.21 (Focal) ≫ 5.13 (Burnside)** > 5.6, 5.7 (mathlib カバー厚) > その他. 5.26 (Frobenius), 5.30 は完成済み.

## 開発時の注意点

### mathlib API 確認事項

- **`focalSubgroup` の生成 set 形**: mathlib は `{g ∈ H | ∃ x ∈ H, u ∈ G, g = ⁅x, u⁆}` (commutator 形), Isaacs は `x^{-1}y` (x, y ∈ H が G-conjugate) で生成. `x^{-1}y = [x, g]` where `y = x^g` の同等変換は短い補題で済む.
- **`MonoidHom.transfer` の domain/codomain**: mathlib は `(ϕ : H →* A) (g : G) : A` 形 (A 可換群への transfer). Isaacs の `H/H'` 標的は `A := H/H'` で具体化, mathlib `transferFocal` がまさにこれ.
- **`IsZGroup` API**: `IsZGroup.isCyclic_commutator` + `IsZGroup.coprime_commutator_index` + `IsZGroup.isCyclic_abelianization` の 3 ピースで Isaacs 5.16 が直接得られる. 弧立 lemma 化は不要.
- **`transferCenterPow`**: mathlib は `[FiniteIndex (center G)]` 仮定下の `G →* center G`. Isaacs 5.6 の "g ↦ g^n は準同型" 部分は `MonoidHom` 型として自動.
- **`A^p(G)` 定義**: mathlib 未収載. 新規 def 候補は `Subgroup.commutator G ⊔ closure {g^p^k | g ∈ G, k : ℕ}` ベース. ただし 5.20 (ker(v) = A^p(G)) を Isaacs ステートメントとして要するなら必要. `Subgroup.commutator G ⊔ Subgroup.OpPrime G` のような form (OpPrime = O^p) も可.

### Foc_G(P) と Foc_G(H) の使い分け

Isaacs は **任意の subgroup H** に対して `Foc_G(H)` を定義 (L3132), mathlib は同様. しかし 5.21 (Focal Subgroup Theorem) は **P が Sylow** であることを使う (5.5 transfer-evaluation で P が Sylow に特殊化される). 一般 H への拡張は §5D 末で Hall π-subgroup 版を言及 (mmd L3140 周辺) するのみで、本筋では Sylow に絞る.

### BG / Peterfalvi 橋渡し名

将来 BG/Peterfalvi 章を書く時に Isaacs 5.X を引用する局面:

- **BG §1.17 Focal Subgroup**: Isaacs 5.21 を直接利用. BG 流ステートメントを `OddOrder.BG.Ch1.S?` で section docstring に明記.
- **BG §1.18 Burnside**: Isaacs 5.13 を直接利用. 同様.
- **Peterfalvi 05.4 Suzuki 付録**: transfer-evaluation を `T(x) = x^{|Q|+1}` 形で使う. その場で mathlib `transfer_eq_pow` をラップ.

⇒ Phase 1 で Isaacs 5.13, 5.21 を BG 名と互換な記述的 Lean 名 (`hasNormalPComplement_of_sylow_normalizer_le_centralizer`, `focalSubgroupTheorem`) で揃えると, Phase 2a での橋渡しが滑らか.

## 未解決の疑問

- **mmd 抽出失敗の整理**: 全 30 結果のうち `### 5D` ヘッダ欠落以外に MISSING_PAGE marker 無し (Ch.3 の 3 件と比べ Ch.5 mmd 品質は良好).
- **Thm 5.18 (abelian Sylow 強化) の証明 strategy**: mathlib `Focal.lean` の `commutator_inf_eq_focalSubgroup` (P abelian で P^{ab} = P) から導く線で良いか, あるいは Isaacs の直接 transfer 計算 (L3071 の `v(x) = x^{|G:P|}` 引数) を写すか. 後者の方が短い可能性.
- **Thm 5.26 Frobenius normal p-complement の証明戦略**: Isaacs は (3) ⇒ (1) を 5.25 + 5.27 + 5.28 で示す. (3) ⇒ (1) で 5.28 が肝 (任意 p-subgroup X で N/C が p-group ⇒ P, Q ∈ Syl_p が C_G(P∩Q) 内で共役). mathlib に類似補題が無い可能性が高く Isaacs 流を follow.
- **Thm 5.24 (G simple, H maximal nilpotent ⇒ H は p-group)** を実装すべきか: BG/Peterfalvi 直接被引用なし, Isaacs Ch.6+ 引用も Wielandt 文脈で 1 回程度. 後回し可.
- **5.10 Dietzmann の置き場所**: mathlib に Schur 5.7 が `card_commutator_le_of_finite_commutatorSet` として既収載で, この証明では Dietzmann を経由しない別経路 (closureCommutatorRepresentatives) を取っている. Isaacs 5.7 を mathlib 経由で示すか, 5.10 を経由して Isaacs 流で示すかは美学の問題. Dietzmann 単独の下流被引用は Ch.5 内に閉じる.

## 2026-07-17 Ch.5 完備化 (レーン a) — 章として全番号付き結果クローズ

survey (`notes/meta/three_books_full_survey_2026_07_16.md`) の Ch.5 残 4 ギャップを全てクローズし、
**Isaacs Ch.5 の 30 番号付き結果は全て形式化済み** (mathlib 被覆 9 + repo 実装 21) となった。

| 結果 | 実装 | 所在 |
|---|---|---|
| Cor 5.4 商版 | `not_isCyclic_sylow_quotient_of_le_commutator_inf_center` | `Basic.lean` |
| Thm 5.10 Dietzmann | `dietzmann` / `dietzmann_setFinite` (list 化した書籍証明; §5B 完備化) | 新 leaf `Dietzmann.lean` |
| Cor 5.19 一般形 | `not_isSimpleGroup_of_sylow_two_cyclic_strict_max_factor` (`A ⊔ B = ⊤` + exponent 条件 encode; 旧 cyclic 版は `B = ⊥` 特殊化) | 新 leaf `SylowTwoDirectFactor.lean` |
| Thm 5.24 | `exists_isPGroup_of_isCoatom_of_isNilpotent` | 新 leaf `NilpotentMaximal.lean` |

5.24 の支持補題 (公開 API、他章から再利用可):

- `APrime_lt_top_of_isNilpotent_of_prime_dvd_card`: 有限 nilpotent `H`, `p ∣ |H|` ⇒ `A^p(H) < H`。
  `Sylow.directProductOfNormal` の p 成分射影 ∘ abelianization の kernel を `APrime_le` の witness にする。
- `exists_sylow_coe_eq_of_normalizer_le` (Sylow promotion): `H` の maximal p-subgroup `P` で
  `N_G(P) ≤ H` なら `P ∈ Syl_p(G)`。normalizer growth (Ch01 Thm 1.22) 経由。

旧「未解決の疑問」のうち 5.24 (後回し可) と 5.10 (置き場所) は上記で決着。AxiomsCheck 登録済
(5.4 商版 / 5.10 / 5.19 一般形 / 5.24)。全 leaf sorry-free、full build green。
