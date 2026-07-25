---
id: 2053
slug: pf-suzuki-theorem-b
title: "Peterfalvi II Ch.II The First Case: Theorem B campaign"
created: 2026-07-21
---

# Peterfalvi II Ch.II The First Case: Theorem B campaign

## 背景

Part II Ch.I (§1–§3, pp. 97–107) は **sorry 0 で完全** (Lemma 5 =
issue 2048 で完結)。文書順の次 = **Ch.II The First Case (pp. 108–114)**、
完全未着手。主定理 **Theorem B**: (B1) (V が素数位数 p の P を含み
C_G(P) の 2-rank が 1) の下で Theorem A の結論が成り立つ。

構造 (2026-07-21 に pp. 108–114 全読で確定):
(B2) 「G に指数 p の正規部分群なし」を仮定 (否定側は Ch.I §3 Prop 2 =
InductionNonSimple で済) して番号付き steps (1)–(17):

- (1) `V = W ⋊ P`, `|Q₀| = 2^p`, `N_G(P) = C_G(P)`,
  `C_D(P) = C_W(P) × P` — Ch.I §2 Prop 3 + §3 Prop 1(b) 部品
- (2)(a) `C_G(P)` は Ω_P 上で (A1) を満たす; kernel N。
  (b) near-field F で `C_G(P)/N = (F ⋊ C_Q(P)) ⋊ Σ` —
  Ch.I §1 Prop 4(c) + **Appendix II Prop 1 (NearFields.lean 実装済)**
- (3) `|Q₁|` の素因数 r ≡ 2^i (mod 2^p−1) — [Is] Thm 15.16
  (coprime 次元 dim M = p·dim C_M(P)) + Clifford ([Is] 6.5) +
  **Appendix I Prop 2 (SemilinearField.lean 実装済)** の field 構造
- (4) `|Q| = |C_Q(P)|^p` — **Wielandt fixed point thm ([HB] XI 12.4)**、
  Z[KP] の Frobenius identity 経由 (repo 被覆要確認:
  GroupTheory/WielandtPerFactorDischarge / CoprimeFixedPoints)
- (5) F 非可換 → F ≅ F_{9,2} ∧ Q₁ = 1 — Ch.I §2 Cor to Prop 2
  (SylowTwo) + [H] III 8.2 (2-rank 1 quaternion) +
  Appendix II Prop 2 (F_{r²,2} 分類)
- (6) Q₁ = 1 → |Σ| ∈ {1,3} or (|F| = f or 9 ∧ Σ = 1) —
  [HB] IX 2.7 型算術 (f^a = 2^b + 1)
- (7) N = P ∧ Σ ≅ C_W(P) — §3 Prop 1(c) の |R| 三分岐で場合消去
- (8) Q₁ ≠ 1 → ℓ = |Σ| prime、|F| = 3^ℓ/5^ℓ/9^ℓ
- (9) p = f — transfer T : G → H/(QKW) の直接計算 (coset reps = §1
  Prop 4(a))、p ∣ |Q|+1
- (10) |F| = p^m の二分岐 (10.1) p ∤ |Σ| ∧ |G|_p = p^{m+2} /
  (10.2) p = |Σ| = 3, F ≅ F_{9,2}, W cyclic of 3 or 9 —
  **Ch.I §3 Lemma 5 を使用 (完成済!)** + (3)(4)(6)(8) の算術
- (11) R = T × P、C_Q(P) が A − {P} に正則作用
- (12) case (10.2) が成立 — (10.1) を否定。R₁ = Sylow p (order p³,
  class 2 < p) に **Hall-Wielandt**: `G/O^p(G) = N_G(R₁)/O^p(N_G(R₁))`。
  ⚠ ここは A = Sylow 自身なので **weakly closed 自明 + class < p =
  Isaacs Cor 10.2 (transfer_range_eq_of_nilpotencyClass_lt, 実装済)** で
  賄える見込み — 必要なのは「transfer range equality →
  G/O^p ≅ N/O^p 同型」への bridge (focal subgroup 系)
- (13) C_G(Z₁) は 3-group (Z₁ = ⟨st⟩) — PSL(2,8) 構造 (§3 Lemma 4)
- (14) Z(RΣ) = Z₁P、N_G(RΣ)/RΣ ≅ S₃、R₂ = C_G(Z₁)
- (15) L cyclic of 9 (PSL(2,8) 内)、Ω₁(LV) = Z₁ΣP
- (16) Z₁PΣ ⊆ Z₂(R₁)、N_G(Z₁PΣ) = R₂⟨s⟩
- (17) 結論 — Z₁PΣ abelian weakly closed in R₂、
  **Hall-Wielandt (p = 3 > 2, A abelian 版)**: `G/O³(G) ≅
  R₂⟨s⟩/O³(R₂⟨s⟩)` → (B2) と矛盾 2 連で Theorem B 完結

## Hall-Wielandt の所在 (2026-07-21 調査)

- statement は Peterfalvi p. 108 に明記: P Sylow p、A weakly closed in
  P rel G、`A ⊆ Z_{p−1}(P)` or `p > 2 ∧ A abelian` ⟹
  `G/O^p(G) ≅ N_G(A)/O^p(N_G(A))` ([Ha] Thm 14.4.2)
- Gorenstein は §7.6 で「M. Hall [1] pp. 206–212 参照、本書では証明せず」
  — **references/ に M. Hall・Huppert とも無し**。Coq odd-order にも無し。
  Isaacs FGT は weakly closed を演習 5C.6 のみ (Grün 周辺 p.163)。
- (12) 用は上記のとおり Cor 10.2 で回避可能。**(17) 用の
  「p > 2 ∧ A abelian weakly closed」版が真の新規 infra** (shared:
  Isaacs/Ch10 delta → 9300 claim を検討)。証明再構成は transfer/fusion
  標準論法 + 必要なら ChatGPT 相談・ユーザーへ Hall 原文追加依頼を報告。

## やること (文書順 + 上流優先)

- [x] Ch.II hypothesis carrier — `FirstCaseHypothesis` (FirstCase/Basic.lean,
      `4a2fede50`): (B1) は「C_G(P) 内 EA-2 部分群 ≤ 2」形。
      p_odd / P ∩ W = ⊥ / C_{Q₀}(P) ≤ 2 も同 leaf
- [x] (1) **完了 (2026-07-21)** — 全 5 主張 sorry 0・axiom-clean・
      AxiomsCheck 6 本登録
  - [x] |Q₀| = 2^p (FirstCase/FieldAction.lean `card_Q0_eq_two_pow`,
        `a39140c69`): P ↪ V̄ (toVbar) → semilinear model 消費 →
        固定体 = F₂ (B1) → Artin で [F : F₂] = p
  - [x] C_K(P) = 1 (StepOne `K_inf_centralizer_eq_bot`, `42ed5777d`);
        |C_{Q₀}(P)| = 2 (StepOne `card_Q0_inf_centralizer_eq_two`,
        軌道計数+Fermat, `c89a19234`); FieldAction は
        `exists_adapted_field_model` bundle (eQ/μ/σhom + 固定元 0∨1) に
        リファクタ済
  - [x] V = W ⋊ P (`W_join_P_eq_V` + `exists_decomp_of_mem_V`;
        |V̄| ∣ |Aut F| = p は natCard_ringAut_eq_finrank + char-2 同定)
  - [x] N_G(P) = C_G(P) (`normalizer_P_eq_centralizer`; Prop 1(b) +
        W∩N(P) ≤ C(P) の commutator トリック) と
        C_D(P) = C_W(P) × P (`D_inf_centralizer_eq_W_inf_centralizer_join_P`;
        D̄ = fitting ⋊ V̄ の成分分離 + `fitting_eq_one_of_conjAction_fixed`)
- [x] (2) C_G(P) の near-field 構造 — StepTwo.lean (`c022a3d01` +
      `e4e7eb646`): `exists_four_subgroup_of_quotient` (奇数 kernel の
      EA-4 lift)、`rankOneQuotient` (RankOneHypothesis、sorry 0)、
      `exists_affineNearFieldModel` (App C Prop 1 sorried-cite — 9318 待ち)。
      ⚠ NearFields → Suzuki hub の import のため StepTwo は root/AxiomsCheck
      直接配線 (hub 経由は cycle)
  - **設計 (2026-07-21 調査)**: (2)(a) は §3 Prop 1(a) 部品
    (`centralizerHypothesisA1 (X := P)` : HypothesisA1 C_G(P) Ω_P、
    CentralizerInduction.lean:246) + kernel N = C_D(C_Q(P)) ∩ C_G(P) の同定。
    (2)(b) は faithful 商 C_G(P)/N に `RankOneHypothesis` (NearFields.lean:652;
    (A1)+(A2)+2-rank-1、2-rank-1 は (B1) から) を構成し
    **`rankOne_affine_nearField` (App C Prop 1) を sorried-cite** して
    `AffineNearFieldModel` を得る。
  - ⚠ `rankOne_affine_nearField` は honestly-stated **sorry** (NearFields:741)。
    未形式化前提 = (i) Huppert III 8.2 (2-rank 1 → Sylow-2 cyclic/quaternion)、
    (ii) **Brauer–Suzuki** (G = O_{2'}(G)·C_G(u))、(iii) Huppert II 3.2
    (normal complement)。方針 = sorried-cite で Theorem B の下流を実証明しつつ、
    Brauer–Suzuki 形式化を独立 campaign として起票 (shared infra、9300 claim)
    - **📌 2026-07-22 hub 裁定更新**: (i)(iii) は c が完了済 (9404 closed)、
      (ii) = **issue 9318 は b → c に移管** (ユーザー裁可、issues/9318 冒頭
      HUB RULING)。b は本 campaign で `rankOne_affine_nearField` を
      sorried-cite し続けるだけでよい (producer = c、b 側の追加作業なし)
- [ ] (3) 素因数の合同条件
  - **被覆調査 (2026-07-21)**: (i) Q₁ = `hyp.Q1` (SylowDecomposition.lean:89、
    Q1Subgroup + sylowTwoProdQ1MulEquiv で S × Q₁ 分解済) ✓。
    (ii) [Is] 15.16 (dim M = |P|·dim C_M(P)) 相当 =
    `finrank_eq_card_mul_finrank_invariants_kernelFPF` (WielandtKernelFPF:303)
    ほか free/freeBlock 3 変種 — 適合形の確認要 ✓ 有望。
    (iii) [H] V 8.15 (Frobenius complement の pq-部分群 cyclic →
    dim C_M(P) = 1 で使用) — **無ヒット、ギャップ**。ただし使用点は
    「C_M(P) の 1 次元性」1 箇所で、KP ≤ 近傍の cyclic 性など別供給も
    検討余地あり。
    (iv) App I Prop 2 = SemilinearField.lean「Proposition 2(a)」✓。
    次: (ii) の正確な適合確認 → M (極小 EA r-部分群) の存在と KP-正規化の
    構成 → (iii) ギャップの扱い決定
  - **適合確認済 (2026-07-21)**: kernelFPF 変種が完全適合 — L := KP、
    U := K (normal)、E := P、k := ZMod r、W := M (additive)。
    invariants(ρ|K) = ⊥ は conjQByK_fixed_eq_one (K fpf on Q)。
    結論 dim M = p·dim C_M(P) で **C_M(P) ≠ 0 も dim 等式から従う**
    (原文の Frobenius 論法不要)。dim C_M(P) = 1 は原文どおり (2)(b) の
    near-field 構造経由 = sorried 継承側。M 存在 =
    MinimalInvariantNormal (exists_aInvariant_normal_isElementaryAbelian 系)。
    実装プラン: StepThree.lean で (a) M 存在、(b) dim 等式 (sorry-free 側)、
    (c) Clifford 二分岐 + App I Prop 2 + (2)(b) 消費 (sorried 継承側) の順
  - **進捗 (2026-07-22, commit 760be19d9)**: (b) dim 等式 =
    `card_eq_card_inf_centralizer_pow` (f8954166a)、`|C_M(P)| = r` =
    `card_inf_centralizer_eq_prime` (9318 継承)。(c) Clifford 二分岐 =
    `exists_prime_order_invariant_or_irreducible` (9318 継承)、**第一分岐
    r ≡ 1 = `card_K_dvd_sub_one_of_prime_order_invariant` sorry-free 完了**
    (AxiomsCheck 登録)。残 = **第二分岐 (M が K-既約) → r ≡ 2^i**。
  - **第二分岐プラン (2026-07-22 精読 p.109 + infra 全確認、上流 gap 無し)**:
    3 部品に分解 (すべて既存 infra の assembly):
    - **Half A (Q₀ 側, M 非依存)**: `∃ i ≤ p-1, ∀ k∈K, a·k·a⁻¹ = k^(2^i)`
      (a = P の生成元)。供給 = `FieldAction.exists_adapted_field_model`
      (σhom : P →* RingAut F, F = 𝔽_{2^p}; μ : fitting(D̄) ≃* Fˣ; 共役律
      `μ(fittingConjAction (toVbar g) t) = fieldRingAutOnUnits F (σhom g) (μ t)`)
      + RingAut(𝔽_{2^p}) = ⟨Frobenius x↦x²⟩ 位数 p ⟹ σhom(a) = Frob^i
      + K ≅ K̄ = fitting(D̄) (`SemilinearIdentification.Kbar_eq_fitting`)。
      ⚠ fittingConjAction ↔ 実 K 上共役、K→fitting の橋が要工作。
      - **A1 (RingAut 𝔽_{2^p} = power-2, mathlib path 確定 2026-07-22)**:
        `frobeniusAlgEquivOfAlgebraic (ZMod 2) F : F ≃ₐ[ZMod 2] F`
        (Mathlib/FieldTheory/Finite/Basic.lean:367)、`orderOf = finrank = p`
        (`orderOf_frobeniusAlgEquivOfAlgebraic`) ⟹ Gal 生成、σ = Frob^i、
        `coe_frobeniusAlgEquivOfAlgebraic_iterate` で σ(x) = x^(2^i)。
        friction 4 点: (1) CharP F 2 を Nat.card F = 2^p から (2 prime)、
        (2) Algebra (ZMod 2) F instance (CharP 経由; `ZMod.algebra`?)、
        (3) RingAut F → (F ≃ₐ[ZMod 2] F) 橋 (prime field 固定ゆえ自動、
        `AlgEquiv.ofRingEquiv` + commutes)、(4) orderOf = card ⟹ 全元が冪
        (`mem_powers`/`zpowers_eq_top`)。汎用ゆえ将来 leaf 化候補だが当面
        StepThree.lean 内 section。
    - **Half B (M 側)**: `∀ k∈K, a·k·a⁻¹ = k^r`。供給 =
      `SemilinearField.exists_field_semilinear` (F' = 𝔽_{r^p} on M,
      K ↪ F'ˣ (M 1-dim over F', K が F'-linear), a は σ-semilinear で
      σ = Gal 生成元 = Frobenius x↦x^r; 共役 k ↦ σ(k) = k^r)。⚠ 最重量。
    - **Combine**: k^(2^i) = k^r ∀k∈K cyclic 位数 2^p−1 ⟹ r ≡ 2^i (mod 2^p−1)。
    - **package (3)**: |Q₁| の素因数 r ⟹ ∃i, r≡2^i (第一分岐 i=0 + 第二分岐)。
    (iii) の [H] V 8.15 ギャップは「dim C_M(P)=1」= 2(b) near-field 経由で
    9318 継承、独立ギャップではない。
  - **進捗 (2026-07-22): 第二分岐 4/5 完了 (StepThree.lean, hB パラメータ化で sorry-free)**:
    A1 `ringAut_card_two_pow_eq_pow` (f444719e0)、Half A
    `exists_pow_two_fittingConjAction` (ec7f1be5c)、A2
    `fittingConjAction_pow_of_K_conj` (9407e5de2)、combine
    `exists_pow_two_modEq_of_K_conj` (131319f5b: hB → ∃i r≡2^i)。
  - **Half B 完了 (2026-07-22)**: `exists_K_conj_pow_of_irreducible`
    (StepThree.lean 末尾) — M K-既約 ⟹ ∃ a∈P, ∀k∈K a·k·a⁻¹=k^r。
    実装 = `exists_field_semilinear_with_scalar` (App I Prop 2(a)+(b) の
    μ : K→*F'ˣ 保持版; E:=↥M, T:=↥K, ψ:=正規化共役) で F'=𝔽_{r^p} を取得、
    μ 単射 (fpf `conjQByK_fixed_eq_one`)、生成元 a₀ の共役が σ-semilinear、
    σ=x↦x^{r^j} (`ringAut_card_prime_pow_eq_pow` q:=r)。p∣j なら σ が Fˣ 固定
    → a₀ が K 中心化 → `K_inf_centralizer_eq_bot`+|K|=2^p−1>1 で矛盾;
    さもなくば m=j⁻¹ (mod p) で a:=a₀^m が Frobenius = x↦x^r → μ 単射で
    K に転送。9318 継承 (`card_inf_centralizer_eq_prime` 経由) ゆえ
    AxiomsCheck 非登録。
  - **package (3) 完了 (2026-07-22) → step (3) 完結**:
    `exists_pow_two_modEq_of_prime_dvd_card_Q1` (StepThree.lean 末尾) —
    r ∣ |Q₁| prime ⟹ ∃i, r ≡ 2^i [MOD 2^p−1]。M の存在+極小性 =
    `exists_minimal_invariant_elab` (Q1MinimalInvariant, X := K⊔P ≤ H) が
    丸ごと供給、dichotomy 消費、第一分岐 = `card_K_dvd_sub_one...` の
    (2^p−1) ∣ (r−1) を Nat.modEq_iff_dvd' で r ≡ 2^0 化、第二分岐 =
    Half B → combine。9318 継承 (AxiomsCheck 非登録)。
- [x] (4) **完了 (2026-07-22)** — `card_Q_eq_card_inf_centralizer_pow`
      (FirstCase/StepFour.lean 新設、root 配線済): |Q| = |C_Q(P)|^p。
      Wielandt = **Pf (9.1) 実装済** (`wielandt_fixedPoint_trivial_U_fixed`,
      sorry-free) を消費 — port 不要だった。carrier `CoprimeFrobeniusAction`
      (L = K⊔P, U = K, E = P) を組立: Frobenius 構造 =
      `isFrobeniusGroup_of_prime_complement_fixedFree` (C_K(P)=1)、
      C_Q(K)=1 = fpf、coprime = `coprime_card_Q_K` + **p ∤ |Q|**
      (`not_p_dvd_card_Q1`/`not_p_dvd_card_Q`: step (3) の合同 r≡2^i と
      p odd の矛盾 — 書籍の「r ≠ p は (3) の帰結」を形式化)。9318 継承。
- [x] (5) **完了 (2026-07-22)** — `card_nearField_eq_nine_and_Q1_eq_bot`
      (StepFive.lean, FirstCaseHypothesis): `(∀ x y : F, comm) ∨ (|F| = 9 ∧
      |C_Q(P)| = 8 ∧ Q₁ = ⊥)`。本体 sorry-free (Higman `pow_four` + 9318 model
      継承のみ)。詳細は末尾「step (5) 完了記録」。
- [ ] (6)–(9) — **(6)(7)(8) 完了, 残 = (9) `p = f`**
  - **(6) 体の場合 完了 (2026-07-22)** — `card_field_eq_and_D_eq_one_of_comm`
    (axiom-clean ∀-model): Q₁=1, F 可換 ⟹ (|F|=char ∨ |F|=9) ∧ |D|=1。
    部品完備: arithmetic + ringAut_sq + fieldOfComm + 抽象核 + `dAutHom`
    (dAut→RingAut 群 hom, crux) + `card_Q_eq_two_pow_of_Q1_eq_bot`。全 StepSix.lean。
  - **(6) 全体形 landing (2026-07-22)** — `card_field_and_D_of_Q1_eq_bot`:
    Q₁=1 ⟹ (可換 → (|F|=char∨9)∧|D|=1) ∧ (非可換 → |D|∈{1,3})。field case は
    実証明、`card_D_le_three_of_noncomm` (非可換=F_{9,2}) は **gated sorry**
    (Aut(F_{9,2}) 奇部分=3、F*=Q₈ ゆえ; near-field Aut infra 無し、D_odd は在り
    |D|∣3 だけ欠く; shared 9300 候補)。StepSix の唯一の sorry。
  - **(7) 完了 (2026-07-22, FirstCase/StepSeven.lean 新設・root+AxiomsCheck 配線)** —
    `N = P ∧ Σ ≅ C_W(P)` (p. 110)。3 commit:
    - **decomposition (axiom-clean)**: `kernelN` (= book の N = `(H.subgroupOf L).normalCore`
      を L↪G で map)、`P_le_kernelN` (P ⊆ C_{D_L}(Q_L)=N)、`kernelN_le_V`
      (N ≤ C_D(P)=C_W(P)·P ≤ V)、`kernelN_eq_kernelInf_W_join_P` (`N=(N∩W)⊔P`、
      n∈N⊆V を exists_decomp で g·w 分解、g∈P⊆N ⟹ w=g⁻¹n∈N∩W)、
      `kernelN_eq_P_of_kernelInf_W_eq_bot` (N∩W=1 ⟹ N=P)。
    - **f = char (axiom-clean ∀-model)**: `orderOf_st_eq_char` — s̄,t̄ (π(s),π(t) in L/N)
      が distinct involution (s∈Q∖D / t∉H⊇D / st⁻¹∉H) ⟹ char=|s̄t̄|
      (`model.orderOf_mul_of_involutions`) ⟹ (st)^char∈N ⟹ odd-kernel bridge
      `orderOf_mul_eq_prime_of_pow_mem_odd_kernel` で |st|=char。書籍の "(2), §1 Prop 4(c)
      + App II Prop 1"。 ⚠ 当初懸念した「quotient 用 hA3 が (B1) で偽」問題は core bridge
      が qhyp 不要ゆえ回避 (X=P で直接適用可)。
    - **|C_Q(X)| readoff (axiom-clean)**: `Hypothesis.cQ_card_and_pGroup_of_trichotomy` —
      `centralizer_trichotomy_of_induction` を branch cases 展開、
      `|C_Q(X)|=|C_{Q₀}(X)|^k` (k=1,2,3) を `distinguishedProduct_order`(f=3/5/3) と対で返す。
    - **contradiction (sorryAx: 9318+Higman)**: `kernelN_inf_W_eq_bot` — X=N∩W≠1 仮定、
      X≤W が Q₀ 中心化 ⟹ C_G(X) に four-subgroup ⟹ trichotomy。R=C_Q(X) 2群 +
      C_Q(P)⊆R ⟹ C_Q(P) 2群 ⟹ (step4) Q 2群 ⟹ Q₁=1 (**Q₁=1 は仮定でなく導出**、
      当初の解釈修正)。step(5)/(6) で `|C_Q(P)|∈{2,8,4}` + `cQ_card_cases_of_Q1_eq_bot`
      (`c=char-1 ∨ (c=8∧char=3)`、|F|=9⟹char=3 は addOrderOf で導出)。faithful
      (`centralizer_Q_inf_D_eq_bot`) ⟹ R⊊Q; Q₀⊆R strict when c>2 (|C_{Q₀}(P)|=2)。
      5 consistent (k,m) 組を `step_seven_numeric` (2冪 exponent 比較) で全消去。
    - **Σ ≅ C_W(P) (sorryAx: kernelN_inf_W_eq_bot 経由)**: `sigma_mulEquiv_centralizer_W` —
      `rankOneQuotient.D = (D_L).map(mk' N)` (rfl!)、`w↦[w]` が iso (inj = C_W(P)∩N⊆W∩N=1、
      surj = C_D(P)=C_W(P)·P + P⊆N)。assembly = `N_eq_P_and_sigma_mulEquiv_centralizer_W`。
    - 数学的には step (7) 完結。sorryAx は 9318 (model) + Higman (step5 F_{9,2} 枝、lane a)
      の legitimate 上流 sorried-cite のみ。
  - **(8) 完了 (2026-07-22, FirstCase/StepEight.lean, root+AxiomsCheck 配線)** —
    `Q₁≠1 ∧ ℓ=|Σ|≠1 ⟹ ℓ prime ∧ |F|∈{3^ℓ,5^ℓ,9^ℓ}` (p. 110)。endpoint =
    `card_prime_and_card_field_of_Q1_ne_bot` (sorryAx=9318+Higman)。以下 sub-lemma 群:
    - `comm_of_Q1_ne_bot` (∀-model, sorryAx=9318+Higman): 「By (5), F is a field」—
      step5 の dichotomy (comm ∨ F_{9,2}∧Q₁=1) から Q₁≠1 ⟹ comm。
    - `st_mem_and_cQ_isPGroup_of_mem_centralizer_W` (**axiom-clean**): w∈C_W(P)#
      で trichotomy を X=⟨w⟩ に適用 ⟹ f=|st|∈{3,5} ∧ C_Q(w) 2群。readoff の直接消費。
    - **fixed-field arithmetic heart 完了 (2026-07-22, axiom-clean, model-free)**:
      `exists_card_fixedSet_eq_char_pow` (σ:F≃+*F 固定集合を AddSubgroup で構成 →
      additive Lagrange で |{x:σx=x}|=f^a) + `card_fixedSet_mem_of_units_two_pow`
      (固定単位 2^b群 ⟹ f^a=2^b+1 ⟹ |固定体|∈{f,9}、step6 算術補題)。書籍の
      「|C_F(w)|=f^a=2^b+1 ⟹ ∈{f,9}」を model 非依存に切り出し済。
    - **equivariance linchpin 完了 (2026-07-22, axiom-clean, model-general)**:
      `model_dAut_one`/`model_dAut_hom`/`model_dAut_inv_cancel` (dAut は D→Aut(F) 群 hom) +
      **`model_qEquiv_conj`** (crux: g∈D,q∈Q で `qEquiv(g q g⁻¹) = dAut g (qEquiv q)`、
      emb(1) を g q g⁻¹ 共役して dAut_conj/qEquiv_conj で unwinding、emb/ofAdd 単射)。
      consumables: `ringEquivOfAddEquivMul` (dAut g を RingEquiv 化) +
      `card_fixedSet_eq_card_fixedUnits_add_one` (|{x:σx=x}|=|fixed units|+1) +
      heart 2 本。**crux 全部 done — 残りは mechanical assembly**。
    - **(B) 完了 (2026-07-22)**: `card_fixedUnits_eq_card_fixedConj` (axiom-clean,
      model-general) — qEquiv + model_qEquiv_conj で `{u:Fˣ//dAut g ↑u=↑u}` ≅
      `{q:↥Q//[g]q[g]⁻¹=q}`、card 一致。equivariance の直接 payoff。
    - **(C) 完了 (2026-07-22)**: per-`w` fixed-field order。3 宣言 (StepEight.lean 末尾):
      - `sigmaElt` (axiom-clean, def): w∈C_W(P) → [w]∈rankOneQuotient.D (=mk'N⟨w,hwP⟩、
        membership = mem_map_of_mem∘mem_subgroupOf∘V_le_D∘W_le_V)。σ_w は本体で
        `dAutHom hcomm model [w]` (step6 の D→*RingAut 橋を再利用、`ringEquivOfAddEquivMul`
        直書きより堅牢)。
      - `exists_card_fixedM0_eq_two_pow` (**axiom-clean**, AxiomsCheck 登録): w-fixed part of
        M₀=C_Q(P) は C_Q(w) 2群に属す ⟹ card = 2^b。実装 = fixed⟺centralizes⟨w⟩ (`hfix_iff`)、
        `{m:↥M₀//w-fixed} ≃ ↥(M₀.subgroupOf K)` (K=centralizer(zpowers w))、
        `M₀.subgroupOf K ≤ Q.subgroupOf K` (comap_mono) + st_mem の IsPGroup 2 で `to_le` +
        `exists_card_eq`。
      - `cardFixedField_char_or_nine` (**sorryAx=9318+Higman**): Q₁≠1 ⟹ 各 nonid w∈C_W(P) で
        `|{x:F//dAut[w]x=x}| ∈ {char, 9}`。chain = card_fixedUnits_eq_card_fixedConj ∘
        cardFixedConj_eq_cardFixedM0 ∘ exists_card_fixedM0_eq_two_pow で |C_{F*}(w)|=2^b、
        card_fixedSet_eq_card_fixedUnits_add_one で |C_F(w)|=2^b+1、b≥1 は char∈{3,5} odd から
        (fixedSet=char^a odd ⟹ 2^b+1 odd ⟹ b≥1)、heart `card_fixedSet_mem_of_units_two_pow`。
        Field 化 = `fieldOfComm hcomm` (hcomm=comm_of_Q1_ne_bot)、CharP F char は step6 導出流用。
    - **(D) 完了 (2026-07-22) → step (8) 完結**: `card_prime_and_card_field_of_Q1_ne_bot`
      (**sorryAx=9318+Higman**、∀-model): `Q₁≠1 ∧ ℓ=|Σ|=|C_W(P)|≠1 ⟹ ℓ prime ∧
      |F|∈{3^ℓ,5^ℓ,9^ℓ}`。汎用 axiom-clean 3 補題 (StepEight top、AxiomsCheck 登録):
      - `card_eq_card_fixedPoints_pow_orderOf` (Artin): σ:RingAut(有限体) で
        `|F|=|{x:σx=x}|^{orderOf σ}`。zpowers σ の MulSemiringAction + `FixedPoints.finrank_eq_card`。
      - `isCyclic_ringAut_of_charP`: 有限体の `RingAut F` cyclic。RingAut F ↪ Gal(F/𝔽_q)
        (`AlgEquiv.ofRingEquiv`, prime field 固定) + Gal cyclic instance + `isCyclic_of_injective`。
      - `card_prime_of_isCyclic_forall_ne_one_orderOf`: cyclic 群で全 nonid 同位数 ⟹ card prime
        (`IsCyclic.card_orderOf_eq_totient` + `Nat.totient_eq_iff_prime`)。
      assembly: ψ=(dAutHom hcomm model).comp f (f:C_W(P)→*Σ、sigma_mulEquiv の f と同構成)、
      単射 (f 単射=kernelN∩W=⊥ + dAut_injective)。IsCyclic(RingAut F)⟹IsCyclic C_W(P)。
      constancy = 各 nonid w で |F|=char^{a_w·orderOf σ_w} (a_w∈{1,2}=step C+char_pow、
      orderOf σ_w odd=D_odd)、N=a_w·orderOf の parity が a_w 一意決定 ⟹ |C_F(w)| 一定。
      ⟹ orderOf σ_w 一定 ⟹ generator で ℓ prime + |F|=|C_F(g)|^ℓ、|C_F(g)|∈{3,5,9}。
  - **(6) 算術補題 完了 (2026-07-22, StepSix.lean 新設)**:
    `eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one` (axiom-clean, AxiomsCheck
    登録) — [HB] IX 2.7: `f 奇 ∧ f^a = 2^b+1 (b≥1) ⟹ a=1 ∨ f^a=9`。純 ℕ 算術
    (幾何和の偶奇で a 偶 → (f^c-1)(f^c+1)=2^b で 2 冪 → f^c=3)。steps (6)/(8) が消費。
  - **(6) 体の場合 crux 完了 (2026-07-22)**: `ringAut_sq_eq_one_of_card_prime_or_prime_sq`
    (StepSix.lean, axiom-clean, AxiomsCheck 登録) — 有限体 F (位数 q or q²) の
    RingAut は exponent ≤ 2 (∀σ, σ²=1)。`ringAut_card_prime_pow_eq_pow` (σx=x^{q^i})
    + `FiniteField.pow_card_pow` (x^{|F|^i}=x)。⟹ Σ 奇位数 ↪ exponent-2 群 → Σ=1。
  - **(6) 本体 assembly プラン (2026-07-22 精査済)**: model 上で 2 分岐 (letI-prefix,
    step 5 と同型)。**核心の ungated/gated 判定完了**:
    - **体の場合 (F 可換) = ungated だが plumbing 多層**:
      (i) NearField 可換 → Field インスタンス橋 = **未整備** (`nearField_field_structure_of_index_two`
      は別型 K を返すのみ; `NearField.mul_add_of_mul_comm` で distributivity はある →
      Field 構造を F 上に直接構成する def が要る)。
      (ii) dAut g (F≃+F 乗法的) → RingAut F (体なら ring equiv)、D →* RingAut F 単射。
      (iii) |F*| = |C_Q(P)| が 2 冪 (Q₁=1 ⟹ Q=Sylow-2 2群) → |F|=|F*|+1=2^b+1 →
      **arithmetic lemma** で |F|∈{f,9} → **ringAut_sq_eq_one** → Σ 奇 → Σ=1。
    - **F_{9,2} の場合 = gated (深い near-field Aut)**: `Twisted`/`TwistData` に
      automorphism infra 無し。「Aut(F_{9,2}) 奇部分 = 3 (F*=Q₈ ゆえ)」は sorried-cite
      (shared 9300 claim 候補) or 独立 campaign。arithmetic lemma・ringAut_sq は供給済。
    - 供給済 upstream: arithmetic lemma, ringAut_sq_eq_one。残 = (i) Field 橋 +
      (ii) dAut→RingAut + (iii) |F*|=2冪 plumbing + F_{9,2} sorried-cite。
  - **(5) 被覆調査 (2026-07-22): 3 部品すべて実装済、assembly のみ**:
    (i) Ch.I §2 Cor = `sylowTwo_isMulCommutative_or_isSuzuki2Group`
    (Suzuki/SylowTwo.lean:60、S 可換 or Suzuki 2-group)。
    (ii) App II Prop 2 = `cyclic_index_two_nearField_classification`
    (NearFields.lean:958、**proved axiom-clean 2026-07-21**: F*が指数2巡回
    部分群 → F field ∨ F≅F_{r²,2} ∧ |Z(F*)|=r−1)。
    (iii) [H] III 8.2 = `RankOneHypothesis.sylow_two_isCyclic_or_quaternion`
    (NearFields.lean:691、2-rank 1 → cyclic ∨ quaternion)。
    Suzuki 2-group 指数 4 = `higman_classification`
    (Appendices/Suzuki2Groups.lean:76)。
    証明筋 (p. 109–110): C_Q(P) 非可換 → C_S(P) 非可換 → S Suzuki 2-group
    (可換なら C_S(P) 可換) → exp 4 + 2-rank 1 → C_S(P) quaternion order 8
    → F* ≅ C_Q(P) が指数 2 巡回部分群を持つ → (ii) で F≅F_{r²,2},
    |Z(F*)|=r−1 → |F*/Z(F*)|=4 (quaternion 構造) = r+1 → r=3, |C_Q(P)|=8
    → (4) より |Q|=8^p=|F*|^p... Q₁=1 は |Q|=2^{3p} 2-群化から。
    F の supply = StepTwo `exists_affineNearFieldModel` (9318 sorried-cite)
    経由 — (5) も 9318 継承。statement 形 = AffineNearFieldModel を ∀-model
    パラメータで消費 (letI-prefix statement)。
  - **(5) 部品 2 点完了 (2026-07-22, FirstCase/StepFive.lean 新設・root 配線)**:
    (i) `centralizer_inf_mulEquiv_units` — **C_Q(P) ≅ F*** (書籍の standing
    identification)。qEquiv ∘ (mk' N の Q⊓C_G(P) への制限)。単射 = N ≤ D_L
    + Q⊓D=1 (StepThree の ι イディオム)、全射 = Q̄ := map の定義から。
    (ii) `Q1_eq_bot_of_card_two_pow` — |Q| = 2^n → Q₁ = ⊥。
  - **(5) 抽象核 完了 (2026-07-22, 5641a66bf)**:
    `nearField_card_eq_nine_of_nilpotent_units` (StepFive.lean, 本体
    sorry-free) — F near-field + Fˣ nilpotent + 2-rank 1 + 2-元指数 4 +
    非可換 → |F| = 9 ∧ |F*| = 8。helper 3 点 (c4e069e7b):
    `pow_four_eq_one_of_isSuzuki2Group` (**Higman sorried-cite**、lane a
    campaign 待ち)、`card_center_eq_two_of_card_eq_eight`、
    `isCyclic_odd_pSubgroup_of_nearField_units`。
    残 = **fc-level assembly**: ⚠ hexp4 の供給は S Suzuki 経由なので
    F-可換で場合分けしてから: F 非可換 → **抽出補題** (要実装:
    `exists_noncommuting_two_elements_of_nearField_units` — abstract 証明の
    prefix (O/T 分解 + hTnc) を再利用して Fˣ の非可換 2-元 pair を返す)
    → e.symm で Q の非可換 2-元 → S 非可換 →
    `sylowTwo_isMulCommutative_or_isSuzuki2Group` で S Suzuki → 全 Q の
    2-元が指数 4 (2-元 ∈ S) → hexp4 供給 → 抽象核 → |C_Q(P)| = 8
    (`centralizer_inf_mulEquiv_units` で転送) → step (4) で |Q| = 8^p =
    2^{3p} → `Q1_eq_bot_of_card_two_pow` → Q₁ = ⊥。
    最終形: `(∀ x y : F, comm) ∨ (card F = 9 ∧ card C_Q(P) = 8 ∧ Q₁ = ⊥)`。
  - **step (5) 完了記録 (2026-07-22)**:
    - 抽象核の O/T 分解 prefix を共有補題 **`exists_nilpotent_units_sylowTwo_decomp`**
      (axiom-clean) に括り出し、抽象核と抽出補題が共に消費 (二重化回避、
      抽象核は signature 不変で内部だけ差し替え・regression 無)。
    - **`exists_noncommuting_two_elements_of_nearField_units`** (axiom-clean):
      nilpotent 非可換 near-field の Fˣ から非可換 2-元 pair (共に 2-元)。
    - **`card_nearField_eq_nine_and_Q1_eq_bot`** (∀-model, letI-prefix):
      hnc で場合分け → 非可換なら抽出補題 → `toQ = incl∘e.symm` で C_Q(P)≤Q へ
      転送 → `mem_sylowTwo_of_orderOf_two_pow` で S 到達 → S 非可換 →
      `sylowTwo_isMulCommutative_or_isSuzuki2Group` で S Suzuki →
      `pow_four_eq_one_of_isSuzuki2Group` で hexp4 供給 → 抽象核 → |F|=9,|Fˣ|=8
      → `centralizer_inf_mulEquiv_units` で |C_Q(P)|=8 → step(4) で |Q|=8^p=2^{3p}
      → `Q1_eq_bot_of_card_two_pow`。hnil = Q nilpotent の subgroup を e で転送、
      h2rank = (B1) を e.symm で転送。
    - #print axioms 実測: 抽象核・bundle・extraction = clean (hexp4 は仮説ゆえ
      Higman 非依存)、conclusion のみ sorryAx (pow_four 経由)。
    - AxiomsCheck: StepFive を import 追加、clean 3 本を登録 (conclusion は
      Higman+9318 継承ゆえ意図的に非登録、注記済)。
- [x] (9) `p = f` — **transfer 半分 + endgame 完了 (2026-07-22)、残 = 構造ゲート 1 本**:
  - **算術半分** (既済): `char_eq_p_of_p_dvd_card_Q_add_one` (sorryAx=9318 through model):
    `p∣|Q|+1 ⟹ char=p`。|Q|=|C_Q(P)|^p (step4) + |C_Q(P)|=|F|−1 (units) ⟹ Fermat ⟹ p∣|F|
    ⟹ additive Cauchy + char_spec ⟹ p=char。near-field F でも成立 (additive 経路)。
  - **transfer 半分 完了 (axiom-clean)**: 予想と違い `transfer_eq_pow` の key 条件 (universal
    weakly-closed) は不要だった。真の機構 = **transversal `R = {1}∪{ty}` が x∈P 共役で不変**
    (`x∈V=C_D(t)` が t 中心化 + Q normal ⟹ `x⁻¹(ty)x=t(x⁻¹yx)`)。→ 汎用補題
    **`OddOrder.GroupTheory.transfer_eq_pow_of_conj_invariant_transversal`**
    (`GroupTheory/TransferInvariantTransversal.lean` 新設・root 配線): 左 transversal が x 共役
    不変なら `transfer ϕ x = ϕ(x)^[G:H]` (mathlib 左 transversal で `x•S=S·x` を示す、
    axiom-clean・reusable)。右版 corollary + `isComplement_inv_of_isComplement` も。
    - `CanonicalForm.lean`: `rightTransversalTQ`={1}∪{ty} + `isComplement_H_rightTransversalTQ`
      (Prop 4(a) を IsComplement 化、`exists_canonicalForm`+`canonicalForm_unique` から)。
    - `StepNine.lean`: `rightTransversalTQ_conj_invariant` (R が x∈P 共役不変) +
      **`transfer_eq_pow_card_Q_add_one`** (`transfer ϕ x = ϕ(x)^{|Q|+1}`、[G:H]=|Ω|=|Q|+1)。
  - **endgame 完了 (axiom-clean)**: **`p_dvd_card_Q_add_one`** — ϕ=Abelianization.of:H→H^ab。
    `T=transfer ϕ` は可換群への hom ゆえ `⁅G,G⁆≤ker T`；(B2)=`p∤|G^ab|` で p-元 x∈⁅G,G⁆ ⟹
    `T(x)=1`；`T(x)=ϕ(x)^{|Q|+1}` かつ `P∩⁅H,H⁆=1` で `ord ϕ(x)=p` ⟹ `p∣|Q|+1`。
    **`char_eq_p`** = p_dvd + 算術半分の連結 (= step (9) `p=f`、model sorry 継承)。
  - **構造ゲート `P∩⁅H,H⁆=⊥` 完了 (2026-07-22、axiom-clean)** = 書籍の `P∩QKW=1` (∵ `⁅H,H⁆≤QKW`):
    `P_inf_commutator_H_eq_bot` (StepNine.lean)。機構 = 保持 hom `hToAbDbar : ↥H→*Abelianization Dbar`
    (`Abelianization.of ∘ mk'_W ∘ hToD`) が `⁅H,H⁆` を殺すが `P^#` 上非自明。部品:
    - `QD_isComplement_in_H` (H=Q⋊D、`isComplement'_subgroupOf_of_disjoint_mul_eq_univ`) +
      **`hToD:↥H→*↥D`** (Q-kill 保持、`dToV` clone) + `QsubgroupOfH_normal` instance。
    - 非自明性 `hToAbDbar_ne_one_of_mem_P`: x∈P# の Dbar 像は Vbar (既存 `toVbar`) ∈、≠1
      (`P∩W=⊥`)、∉ Kbar=fitting Dbar⊇commutator Dbar (`Kbar⊓Vbar=⊥`、`fitting_Dbar_cyclic_fpf_abelian.2.2`)。
    - **`p_dvd_card_Q_add_one`/`char_eq_p` は hPinj 仮説を撤去** → char_eq_p は **hB2 + model のみ**。
  - **残 = hB2 (B2 standing 仮説) の carrier 化のみ** (ゲートでない): `p∤|G^ab|` = 「index-p 正規
    部分群なし」。Theorem B が全体で仮定するので step (17) 組立時に carrier/statement で threading。
    (否定側は Ch.I §3 Prop 2 = InductionNonSimple で処理済。) model sorry は 9318 継承。
- [x] (10) 二分岐 — **完了 (2026-07-23、FirstCase/StepTen.lean・StepFive.lean)**。
      endpoint = `step_ten_dichotomy` (`|F|=p^m` の下で (10.1) `¬p∣|Σ| ∧ |G|_p=p^{m+2}` ∨
      (10.2) `p∣|Σ| ∧ p=3 ∧ |F|=9 ∧ IsCyclic W ∧ |W|∈{3,9} ∧ 3^|G|_3=3^4·|W|`)。
      sorryAx=9318+Higman through model (AxiomsCheck 非登録)。
  - **arithmetic core (axiom-clean)**: `padicValNat_pow_sub_one_add_one` (LTE
    `v_p((N-1)^p+1)=v_p(N)+1`)、`card_field_eq_prime_pow` (|F|=p^m, m≥1、additive
    p-group)、`padicValNat_card_Q_add_one` (opening `(|Q|+1)_p = p^{m+1}`)。
  - **structural |G|_p (axiom-clean 群論部)**: `card_D_eq_card_Dbar_mul_card_W`
    (|D|=|D̄||W|)、`card_Kbar_mul_card_Vbar` (|D̄|=|K̄||V̄|)、`card_Kbar_eq_two_pow_sub_one`
    (|K̄|=2^p−1=|K|、Prop 2 経由)、`not_p_dvd_card_Kbar` (Fermat)、`card_Vbar_eq_p`
    (|V̄|=p、V=W⋊P の image)、`factorization_card_Dbar_eq_one`/`factorization_card_D_eq`
    → `factorization_card_G_eq` (model): **|G|_p = p^{m+2}·|W|_p**。
  - **(10.1) 完了 (model)**: `P_le_normalizer_W` + `not_p_dvd_card_W_of_not_p_dvd_card_centralizer_W`
    (P p群が W に共役作用、mod-p 固定点合同 `|W|≡|C_W(P)|`、fixedPoints≃W⊓C_G(P)、
    両 axiom-clean) → `factorization_card_G_eq_of_not_p_dvd_card_centralizer_W`:
    **p∤|Σ| ⟹ |G|_p = p^{m+2}**。
  - **(10) Q₁=1 (model)**: `Q1_eq_bot_of_p_dvd_card_centralizer_W` — p∣|Σ|∧Q₁≠1 で
    step8 の |F|∈{3^ℓ,5^ℓ,9^ℓ} → p∈{3,5}, |C_Q(P)|∈{26,3124,728} の奇素因数
    r∈{13,11,13} が step3 の r≡2^i mod(2^p−1) と矛盾 (`pow_two_mod_seven`/`pow_two_mod_31`
    + `dvd_card_Q1_of_odd_prime_dvd_card_Q` 全 axiom-clean helper)。
  - **(10.2) numeric core 完了 (model)**: `card_field_eq_nine_of_p_dvd_card_centralizer_W`
    — p∣|Σ| ⟹ **p=3 ∧ |F|=9 ∧ |C_Q(P)|=8 ∧ |Σ|=3** (step6 で可換 F は |Σ|=1 ⟹ 矛盾 →
    非可換 → step5 で |F|=9; step7 Σ≅C_W(P) で |Σ| 変換)。
  - **(10.2) 完了 (2026-07-23)**: `w_cyclic_of_p_dvd_card_centralizer_W` — p∣|Σ| ⟹
    p=3 ∧ |F|=9 ∧ IsCyclic W ∧ |W|∈{3,9} ∧ 3^|G|_3=3^4·|W|。3 部品:
    - **`isSuzuki2Group_Q_of_noncomm` (StepFive 新規、model-carrying)**: F 非可換 ⟹
      IsSuzuki2Group Q。|C_Q(P)|=8 (`card_nearField_eq_nine_and_Q1_eq_bot`) で |Q|=8^p=2^{3p}
      は 2-群 ⟹ 任意 Sylow-2 S=⊤ (`Sylow.card_eq_multiplicity`+`eq_top_of_card_eq`)、
      `↥S≅↥Q` (`subgroupCongr`+`topEquiv`)。非可換 units 2 個 (`exists_noncommuting_two_elements`)
      を Q へ転送 ⟹ Q 非可換 ⟹ `sylowTwo_isMulCommutative_or_isSuzuki2Group` で S Suzuki ⟹
      `IsSuzuki2Group.of_equiv eS` で Q Suzuki。⚠ `of_equiv` は full name
      `...SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv` (dot notation は Suzuki2Group
      namespace を見るので不可)。
    - **`orderOf(st)=3`**: `orderOf_st_eq_char model` (step7) + char=3 (|F|=9 の additive
      order 論法、StepSeven パターン流用)。
    - **Lemma 5 消費**: m:=p, `card_Q0_eq_two_pow` (|Q₀|=2^p), |Q|=|Q₀|^3 (step4+p=3)。
      `lemmaFive_of_orderThree` ⟹ IsCyclic W ∧ |W|∣2^p+1=9。|Σ|=3∣|W| (`card_dvd_of_le`)
      で |W|≠1 ⟹ |W|∈{3,9} (`dvd_prime_pow`)。|G|_3 = `factorization_card_G_eq` (m=2) +
      |W|=3^k で 3^4·|W|。
- [ ] (11)–(12) (Cor 10.2 bridge: transfer range → G/O^p 同型)
- [ ] (13)–(16)
- [ ] Hall-Wielandt abelian 版 (shared infra、claim してから)
- [ ] (17) 結論 → Theorem B assembly

## 完了条件

- Theorem B (`(B1) → Theorem A conclusion for G`) が sorry-free で
  landing、AxiomsCheck 登録

## 参照

- references/peterfalvi/pdf/05.4_pp_108_114_The_First_Case.pdf (全 7 頁)
- issues/closed/2048-pf-suzuki-lemma5.md (Ch.I 部品への pointer)
- OddOrder/Peterfalvi/Appendices/NearFields.lean (App II)
- OddOrder/Peterfalvi/Appendices/SemilinearField.lean (App I)
- OddOrder/Isaacs/Ch10_MoreTransfer/Yoshida.lean:509 (Cor 10.2)
- OddOrder/GroupTheory/WielandtPerFactorDischarge.lean (要調査)

---

## 📝 2026-07-24 hub 監査メモ (checklist が実装に遅行)

実測: `FirstCase/` に **StepNine.lean / StepTen.lean が既に存在**し、`OddOrder/Peterfalvi/
Appendices/Suzuki/FirstCase/**` は実 sorry 0。本文 checklist の「残 = (9) p = f」は遅行記述。
owner (lane b) が次回 sync 時に checklist を実状態へ更新し、Theorem B 最終 assembly の
有無 (`theoremB` 相当の endpoint 宣言) を明記すること。

---

## ❄ 2026-07-24 FROZEN (ユーザー裁定) — pending へ

Pf II Ch.II Theorem B campaign (lane b の現 frontier) はユーザー裁定で凍結。
凍結時点の実状態 = StepOne〜StepTen まで leaf 存在・`FirstCase/**` 実 sorry 0
(checklist は「残 (9) p=f」表記のまま遅行 — 解凍時に実測で再同期すること)。
Theorem B 最終 assembly の有無も解凍時に確認。lane b の次 frontier は hub 裁定で再割当。

---

## 🔓 2026-07-25 再活性化 (ユーザー指示)

ユーザーが本 issue を含む pending 4 件 (0106/0131/2053/8005) の再着手を指示。
pending の凍結/トリガー待ち/ユーザー判断待ちはいずれも解除 — main セッションが引き取る
(3 レーンとも 2026-07-23 から停止中・未マージ 0 を確認済、territory 衝突なし)。

## 📝 2026-07-25 解凍・実測再同期 (再活性化指示による)

- **FirstCase/** 全 12 file (Basic/FieldAction/StepOne〜StepTen) = 実 sorry 0** (comment-strip
  census で確認)。checklist の「残 = (9) p = f」は遅行 — **(1)〜(10) は全て完結済み**。
  StepSix の gated sorry (`card_D_le_three_of_noncomm`) も解消済み。
- **Higman Thm 1(a) landing 済** (lane b 最終 commit `bcf5dbfa2`):
  `pow_four_eq_one_of_isSuzuki2Group` (Higman/Suzuki2Groups/ExponentFour.lean) は sorry 0。
  StepFive の sorried-cite は実証明化された。
- **NearFields.lean = 実 sorry 0** — `rankOne_affine_nearField` 本体は証明済み。残る sorryAx
  経路は上流 **BS Q₈ (|S|=8)** のみ (= issue 0147、Navarro PDF 購入待ち)。Theorem B の
  axiom 状態はこれを継承する (sorried-cite 方針どおり、campaign は block されない)。
- **Theorem B 最終 assembly (`theoremB` 相当 endpoint) は未作成** (grep 0 件)。
- ⟹ **真の残作業 = steps (11)〜(17) + Hall-Wielandt abelian 版 (9500 claim 要) + assembly**。
  次の一手 = (11) R = T × P、C_Q(P) の A − {P} 正則作用 (p. 111)。

## 📖 2026-07-25 step (11)(12) 精読ノート (PDF pp. 111-112 直読、実装用)

**(11) statement**: R := F の G 内逆像 (= mk' P : C_G(P) → C_G(P)/P の下で F-並進部分群の
preimage、step (7) の N = P 使用)。主張:
(i) **R = T × P** — T は C_Q(P)·C_W(P) に正規化される部分群、**T ⋊ C_Q(P) ≅ F ⋊ F***。
(ii) **C_Q(P) は 𝒜 − {P} に正則作用** — 𝒜 := 「R の位数 p 部分群で T に含まれないもの」。

**(11) 証明**:
1. R abelian: 非可換なら [R,R]=Z(R)=P (C_Q(P) が F* に推移的)、N_G(R) ⊆ N_G(P)。
   - case (10.1): R が N_G(P) の (よって G の) Sylow-p、|R|=p^{m+1} が |G|_p=p^{m+2} と矛盾。
   - case (10.2): RC_W(P) が N_G(P) の Sylow-3; Σ が R/P≅F に非自明作用 ⟹
     Z(RC_W(P))=Z(R)=P ⟹ RC_W(P) が G の Sylow-3、|RC_W(P)|=3^4 が |G|_3=3^4|W|≥3^5 と矛盾。
2. T := [R, s] (s = involution)。R abelian ⟹ R = T × C_R(s) = T × P。
3. |𝒜| = (p^{m+1}−p^m)/(p−1) = p^m = |F|。正則性: a ∈ C_Q(P)^# が P₁ ∈ 𝒜 を正規化 ⟹
   a は T を正規化し R/T ≅ P を中心化 ⟹ [a,P₁] ⊆ P₁∩T = 1 ⟹ a が P₁ 中心化。
   a は R/P に fpf ⟹ C_R(a) = P ⟹ P₁ = P。

**(12) Case (10.2) holds** (= (10.1) を否定):
1. (10.1) 下で R は N_G(R) の Sylow-p でない ⟹ N_G(P) ⊊ N_G(R)。
2. 𝒜' := N_G(R) 下の P の軌道。P₁ ∈ 𝒜' ⟹ P₁^# は strongly real でない (Ch.I §3 Lemma 3、
   P と共役ゆえ)。T の元は s に反転される ⟹ P₁ ∩ T = 1 ⟹ {P} ⊊ 𝒜' ⊆ 𝒜。
   C_Q(P) の 𝒜−{P} 正則性 ⟹ 𝒜' = 𝒜。[N_G(R):N_G(P)] = |𝒜| = p^m ⟹ (10) より **m = 1、
   |G|_p = p³**。
3. N_G(R)/R 内: C_G(P)‾ = C_Q(P)‾ ⋊ C_W(P)‾、C_Q(P)‾ が 𝒜−{P} 正則、C_W(P)‾ が
   C_Q(P)‾ に忠実。**App II Prop 1 を N_G(R)/R ↷ 𝒜 に適用** ⟹
   N_G(R)/R = (R₁/R) ⋊ C_Q(P)C_W(P)、R₁ = G の Sylow-p、C_Q(P) が (R₁/R)^# に正則。
4. R₁ 非可換位数 p³ ⟹ class 2 < p ⟹ **Hall-Wielandt (= Isaacs Cor 10.2 で賄う予定、
   issue 本文の (12) 注記どおり)**: G/O^p(G) = N_G(R₁)/O^p(N_G(R₁))。
5. T ⊴ R₁ (N_G(R) が 𝒜 に推移的)。R₁/T = (R/T) × (T₁/T)、T₁ = [R₁/T, s]。
   𝒜₁ := R₁/T の位数 p 部分群で T₁/T と異なるもの。(11) と同様に C_Q(P) が
   𝒜₁ − {R/T} に正則 ⟹ N_G(R) ⊊ N_G(R₁) なら [N_G(R₁):N_G(R)] = |𝒜₁| = p が (10) と矛盾
   ⟹ **N_G(R₁) = N_G(R)**。T₁C_Q(P)C_W(P) が N_G(R₁) 内 index p 正規 ⟹ 4 と合わせ
   G に index p 正規部分群 ⟹ **(B2) 偽** ⟹ (10.1) 不成立。□

**実装設計メモ**:
- R の構成 = `(mk' P) ⁻¹' (F-並進部分群の像)` — StepTwo の `exists_affineNearFieldModel`
  bundle と step (7) `N_eq_P_...` の合流点。model の F-部分群を G に引き戻す comap 構成。
- (11) は FirstCase/StepEleven.lean 新設 (leaf 配線 = OddOrder.lean 追記を忘れない)。
- 使用部品: C_Q(P) の F* 推移性 (model qEquiv 経由)、s の反転作用 (Q₀ 系 =
  `model.orderOf_mul_of_involutions` 周辺)、fpf (`conjQByK_fixed_eq_one` 型)、
  (10) = `step_ten_dichotomy`。
- (12) の App II Prop 1 = NearFields.lean `rankOne_affine_nearField` (実 sorry 0、BS Q₈ 継承)
  を N_G(R)/R に再適用する形 — RankOneHypothesis の新しい実例化が要る。
- Ch.I §3 Lemma 3 (strongly real) の被覆確認が (12) 着手時の最初の grep 項目。

## 🚧 2026-07-25 step (11) 進捗 (FirstCase/StepEleven.lean、全 push 済)

**landing 済 (全て leaf+root green・警告ゼロ、∀-model 形で leaf 自体は axiom-clean)**:
- `invImageF` (R = emb(F) の mk' preimage の G 押し出し) + le_centralizer / P_le / mem_iff
- `conj_mem_invImageF` (R ⊴ C_G(P)、range_normal の comap)
- `addSubgroup_eq_bot_or_top_of_mul_units_mem` (near-field F*-右乗不変 → ⊥∨⊤)
- `conjInvariant_eq_bot_or_range_emb` (model-level、qEquiv_conj 消費; generic 形)
- `eq_P_or_eq_invImageF_of_conj_invariant` (G-level 二択、ind 消費で kernelN=P)
- `P_le_center_invImageF` / `commutator_invImageF_le_P` (⁅R,R⁆ ≤ N=P)
- `center_eq_P_of_not_isMulCommutative` (Z(R) = P、非可換時)
- `card_invImageF` (|R| = |F|·|P|、Lagrange×2 + index_comap)
- `normalizer_invImageF_le_normalizer_P` (N_G(R) ≤ N_G(P)、Z(R)=P の特性性)

**次 = R abelian の完成 (p. 111 証明 1 の残り = 位数矛盾)**。ポイント:
- **step (1) の `normalizer_P_eq_centralizer` (N_G(P) = C_G(P)) が使える** ⟹ 書籍の
  「R Sylow in N_G(P)」は C_G(P) の p-part 勘定に還元 (Aut(P) 埋め込み不要)。
- |C_G(P)| = |N'|·|F|·|Q̄|·|D̄| (Lagrange + model.isComplement.card_mul + Q_mul_D_eq_H)、
  p-part = p^{m+1} (p∤(p^m−1) + case (10.1) の p∤|Σ|)。
- (10.1): R < P₁ (Sylow_p G, p^{m+2}) → p-群の normalizer 成長 (mathlib 名要確認:
  IsPGroup 系 lt_normalizer) → N_{P₁}(R) ≤ N_G(R) ≤ C_G(P) が p-part 超過で矛盾。
- (10.2): RC_W(P) を 3-Sylow として同型の論法 (|RC_W(P)|=3^4 vs |G|_3=3^4|W|≥3^5)。
- その後: T := [R,s] 分解 (R abelian + s 反転) → |𝒜| = p^m → 正則性 (a fpf on R/P)。
- **(10.1) 側 R abelian 完了** (`a1b9159c3`): `invImageF_mul_comm_of_not_dvd_card_D`。
  次 = (10.2) 側 arm (p=3, RC_W(P) が N_G(P) の 3-Sylow、|RC_W(P)|=3^4 vs |G|_3=3^4|W|≥3^5)。
  部品はほぼ同型: card 勘定 (|R·C_W(P)| = |R|·|Σ|/...) + Σ の R/P への非自明作用で
  Z(RC_W(P)) = Z(R) = P。その後 step_ten_dichotomy を消費して無条件 R abelian。
- **R abelian 両 arm 完成** (`4cff5efb8`〜`8ca894010`): 共有 Sylow engine
  (`false_of_ppart_subgroup_center_P`) + (10.1) arm + (10.2) arm
  (Z(R·C_W(P)) = P は faithfulness core `eq_one_of_dAut_sigmaElt_eq_id` 経由)。
  次 = step_ten_dichotomy を消費する無条件 `invImageF_isMulCommutative`
  (|F| = p^m の供給 = card_field_eq_prime_pow + char_eq_p の hB2 threading に注意) →
  T := [R,s] 分解 → |𝒜| = p^m → C_Q(P) 正則性 → step (11) statement 完成。
- **step (11) 第一主張 (R abelian) 完成** (`71e1d3b12`): `invImageF_mul_comm` が
  step_ten_dichotomy 消費で両 arm を接続 (無条件、hB2 + |F|=p^m を threading)。
  p. 111-112 の (11) 証明 ¶1 が完全形式化。
  次 = **T := [R,s] 分解**: s = Q₀ 側の distinguished involution (StepSeven の s/t 系を確認)、
  R abelian + s が R を正規化 → T = {r·(s r s⁻¹)⁻¹ | r ∈ R}-型の構成 or [R,s] 部分群 +
  R = T × C_R(s) = T × P (C_R(s) = P は s-fixed part)。その後 𝒜 の定義と正則性。
- **R = T × P 分解完成** (`55906c7ee`): `exists_sInverted_complement` — T = s-反転部分群、
  T⊔P=R / T⊓P=⊥ / s-inverted。並進側の ψ(x)=x·u−x 単射→全射が核。
  残 (11): (i) T の C_Q(P)C_W(P)-正規化句 — c が s と可換なら即時; s の Q₀-中心性
  or unique_involution_in_H 経由で c s c⁻¹ = s を先に確立するのが筋。
  (ii) 𝒜 := {位数 p の R-部分群で T ⊄} の |𝒜| = p^m と C_Q(P) 正則性
  (a ∈ C_Q(P)# が P₁ ∈ 𝒜 を正規化 → [a,P₁] ⊆ P₁∩T = 1 → a が P₁ 中心化 →
  a fpf on R/P (u-乗の固定点なし) → P₁ = P)。
