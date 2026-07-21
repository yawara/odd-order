---
id: 1051
slug: feitsibley-lemma2a-clifford
title: "FeitSibley Lemma 2(a) Sset_eq_induced_of_Q: Clifford 特徴付け (𝒮 = 誘導集合)"
created: 2026-07-21
---

# FeitSibley Lemma 2(a) Sset_eq_induced_of_Q: Clifford 特徴付け (𝒮 = 誘導集合)

lane a frontier (文書順、Lemma 1(a) = issue 1049 の次)。FeitSibley 残 sorry の最上流。

## 背景

`FeitSibley.Sset_eq_induced_of_Q` (FeitSibley.lean:386, sorry): **𝒮 = {Ind_Q^H φ | φ∈Irr(Q),
Q₁⊄Ker φ}**。𝒮 := {χ∈Irr(H) | Q₁⊄Ker χ} (定義)。これが誘導集合に等しいという full Clifford
特徴付け。下流の 2(b)-isometry (𝒮 が H−Q 上で消える → induction isometry) と 2(c) (𝒮|_{Q₁D}
既約非自明 → no real char) が依存する構造事実。

**構造 (FeitSibley.Hypothesis)**: H = Q ⋊ D (Q⊴H, Q∩D=1, QD=H, coprime), Q = S × Q₁
(内部直積: S∩Q₁=1, SQ₁=Q, 元ごと可換, coprime, S nilpotent), D は Q₁ に FPF
(`D_fixedPointFree_on_Q1`), Q₁ は非 2-群。⚠ **D が Q₁ を normalize する事実は hypothesis に無い**
— Q₁ は coprime ゆえ Q の characteristic Hall 部分群 ⟹ Q⊴H から Q₁⊴H が**導出可能**
(field 追加は不要, deriving lemma が要る)。

## 証明ルート (product-char 全分解を回避する Clifford route)

crux = **inertia I_H(φ) = Q** (φ∈Irr(Q), Q₁⊄Ker φ)。書籍の λθ 分解の代わりに:

1. **Q₁ ⊴ Q** (直積因子): q=sy と書き qxq⁻¹ = s(yxy⁻¹)s⁻¹ = yxy⁻¹ ∈ Q₁ (S 中心化 + Q₁ subgroup)。
2. **Q₁ char Q ⟹ Q₁ ⊴ H** (coprime Hall: |Q|=|S||Q₁|, gcd=1 ⟹ Q₁ = Hall π-部分群 char in Q; Q⊴H)。
   ⟹ D は Q₁ を normalize (`D_fixedPointFree_on_Q1` の action が well-defined になる)。
3. **φ|_{Q₁} = e·θ (単一 θ∈Irr(Q₁))**: Clifford (`clifford_decomposition`, Clifford.lean) で
   φ|_{Q₁} = e·∑(Q-orbit of θ)。Q は Irr(Q₁) に**自明作用** (q=sy: s 中心化 ⟹ θ^s=θ; y∈Q₁ ⟹
   θ^y=θ class-fn 不変) ⟹ orbit={θ}。
4. **θ ≠ 1**: Q₁⊄Ker φ ⟺ φ|_{Q₁} ≠ e·1 ⟺ θ≠1_{Q₁}。
5. **inertia I_H(φ) = Q**: I_H(φ)⊇Q 常成立 (φ は class fn, Q 内 conj 不変)。d∈D 非自明が φ^d=φ ⟹
   φ|_{Q₁}^d=φ|_{Q₁} ⟹ θ^d=θ。d FPF on Q₁ ⟹ (Brauer `not_mem_inertia_of_ne_trivial_of_
   card_fixedClasses_eq_one` / `card_fixedPoints_conjByPermIrr_eq...`, ConjugationBrauer.lean)
   θ^d=θ ⟹ θ=1。矛盾。⟹ I_H(φ)=Q。
6. **Ind_Q^H φ 既約**: `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq`
   (CliffordCorrespondence.lean:385, Isaacs 6.11) を inertia=Q で。
7. **Q₁ ⊄ Ker Ind_Q^H φ**: Ind の Q₁D への制限 = Ind_{Q₁}^{Q₁D} θ (θ≠1) ⟹ Q₁ ⊄ Ker。
8. **⊆ (逆)**: χ∈𝒮 ⟹ Clifford で χ は φ∈Irr(Q) の上に乗る (χ lies over φ); Q₁⊄Ker χ ⟹ Q₁⊄Ker φ;
   inertia=Q ⟹ χ = Ind_Q^H φ (`eq_of_induce_eq_induce_of_liesOver_of_inertia_eq` 系)。

## 既存 infra (再利用)

- `induce_apply_eq_zero_of_not_mem_normal` (InducedCharacter.lean:338) — Ind が normal subgroup 外で消える (2(b) にも要る)
- `clifford_decomposition` (Clifford.lean, 0 sorry) — Clifford 制限
- `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq` / `eq_of_induce_eq_induce_of_liesOver_of_inertia_eq` (CliffordCorrespondence.lean:385/550) — Clifford correspondence
- `not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one` (ConjugationBrauer.lean:253) — Brauer FPF inertia
- `CharacterProduct.lean` — 積指標基盤 (今回は full 分解不使用の見込み)

## やること (上流から)

- [ ] **構造補題群** (FeitSibley.lean, hyp.* として): `Q1_normal_in_Q` (直積因子), `Q1_normal_in_H`
  (char Hall), `D_normalizes_Q1`, 元の s·y 一意分解。
- [ ] **inertia=Q 補題** (φ∈Irr(Q), Q₁⊄Ker φ ⟹ I_H(φ)=Q): 上記 route step 3-5。⚠ 最大の塊。
- [ ] **forward** (⊇): step 6-7。
- [ ] **converse** (⊆): step 8。
- [ ] `Sset_eq_induced_of_Q` の sorry close。

## 完了条件

`FeitSibley.Sset_eq_induced_of_Q` の sorry が消え、build green + axiom-clean。可能なら下流
2(b)-isometry / 2(c) が消費できる補助形 (𝒮 が H−Q で消える等) も派生。

## 進捗 (2026-07-21) — 数学的核心 landing、forward/converse 組立が残る

**完了 (4 commit landing、全て build green + sorry 非退行 + 新 axiom 無し)**:

- **Piece 1** (`c70b2a034`): 構造補題 (Hypothesis 名前空間, G-level)
  - `mem_Q1_of_mem_Q_of_coprime_orderOf` (π-元特徴付け), `D_normalizes_Q1`, `Q1_normal_in_H`。
- **Piece 2** (`90f3c95ae`): Frobenius Q₁D の inertia 排除 (route B, ↥H に留まる)
  - `fixedPointFree_of_mem_Q1_mul_D` (kδ が FPF, commutatorMap_surjective 経由),
    `H_le_normalizer_Q1`, `Q1_subgroupOf_H_normal`, `delta_fixed_class_eq_one`,
    `card_fixedClasses_Q1_eq_one`, `delta_notMem_inertia_Q1` (δ∈D^# ∉ I_{↥H}(θ))。
- **Piece 3a** (`bb60bdee7`): **inertia crux** `inertia_theta_eq_Q` (非自明 θ∈Irr(Q₁) の
  ↥H-inertia = Q)。+ `exists_mem_Q_mul_mem_D_subtype`, `Q_conjBy_eq`。
- **Piece 3b** (`22e9bab07`): `exists_ne_trivial_liesOver_of_not_forall_eq_one` (汎用:
  N⊄Ker χ ⟹ ∃ 非自明 θ∈Irr(N), χ liesOver θ。Fourier 展開)。

**残 (forward ⊇ + converse ⊆ の組立、`Sset_eq_induced_of_Q:411` sorry)**。核心は済み、
残りは Clifford correspondence への配線 (subgroupOf/compHom transport が主):

- **forward part A** (Ind_Q^H φ 既約): φ∈Irr(QH), Q₁⊄Ker φ に対し
  - Piece 3b で N':=Q1H.subgroupOf QH から非自明 θ'∈Irr(N') 抽出 (RHS 条件 = N'⊄Ker φ,
    `Subtype.forall` で変換)。
  - θ := untransport θ' to Irr(Q1H): `θ := compHom (subgroupOfEquivOfLe hHT).symm.toMonoidHom θ'`
    (irreducible = `IsIrreducibleCharacter.compHom_of_surjective`, InflationCharacter.lean:164)。
    roundtrip `compHom(subgroupOfEquivOfLe hHT) θ = θ'` は ext + `equiv.symm_apply_apply`。
  - `inertia_theta_eq_Q hθne` (θ nontrivial) で hinertia。
  - `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq (G:=↥H) hHT hθirr hinertia φ hover`
    (CliffordCorrespondence.lean:385)。consumer idiom = CliffordDecomposition.lean:153。
  - 要 instance: `Q1_subgroupOf_H_normal`, `(Q1H.subgroupOf QH).Normal`
    (`Subgroup.Normal.subgroupOf`, mathlib Subgroup/Basic:901), Fintype/Invertible。
- **forward part B** (Q₁⊄Ker(Ind φ)): Ind φ は θ の上に乗る (Ind φ liesOver φ liesOver θ,
  restriction 推移律)。Q₁⊆Ker(Ind φ) なら Res_{Q1H}(Ind φ)=deg·trivial ⟹ trivial のみに
  lies over、θ≠trivial に矛盾。
- **converse ⊆**: χ∈Irr(↥H), Q₁⊄Ker χ ⟹ Piece 3b で θ∈Irr(Q1H) 非自明 (χ liesOver θ),
  `inertia_theta_eq_Q` で I=Q、Clifford correspondence の全射性 (χ = Ind_Q^H φ for some
  φ∈Irr(QH) lying over θ) + φ の Q₁⊄Ker は χ の逆算。`eq_of_induce_eq_induce_of_liesOver_of_inertia_eq`
  (CliffordCorrespondence.lean:550) 系、または Clifford correspondence の全単射補題を探す。

census テーブル (FeitSibley.lean:59) の Lemma 1(a) 行は stale (1049 で close 済) — 要修正。

## 参照

- `OddOrder/Peterfalvi/Appendices/FeitSibley.lean:411` (残 sorry), `:92` (Hypothesis 構造),
  構造補題群は Hypothesis 名前空間 (`mem_Q1_of_mem_Q_of_coprime_orderOf`〜`inertia_theta_eq_Q`)
- `references/peterfalvi/pdf/09.0_*.pdf` p.145 (Lemma 2(a)), coq `PFsectionN` の対応 Clifford
- issue 1049 (Lemma 1(a), closed), 下流 = 2(b)-isometry (FeitSibley.lean:436) / 2(c) (:456)
- Clifford correspondence: `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq` /
  `eq_of_induce_eq_induce_of_liesOver_of_inertia_eq` (CliffordCorrespondence.lean:385/550)

## 完了 (2026-07-21)

`Sset_eq_induced_of_Q` の sorry close (commit `1a4ea3d7b`)。build green (default heartbeats、
3.7s) + axiom-clean (`propext`/`Classical.choice`/`Quot.sound` のみ)。FeitSibley 残 sorry
4 → 3 (2(b) isometry / 2(c) / Theorem)。

- forward/converse とも issue 記載の recipe 通り。converse の全射性は Clifford 対応の
  全単射補題でなく、新汎用補題 `exists_restrictionMultiplicity_ne_zero_intermediate`
  (2 段制限恒等式 ⟨Res_N χ, θ⟩ = Σ_ψ ⟨Res_T χ, ψ⟩⟨Res ψ, θ'⟩ の standalone 化) +
  既約指標直交性で閉じた (`eq_of_induce_eq_induce_...` は不使用)。
- 新汎用 helper 6 本は FeitSibley.lean の Piece 3b 隣に配置 (compHom roundtrip ×2 /
  trivial transport ×2 / 定数⟹非自明乗数 0 / 中間 constituent 通過)。将来 hub 判断で
  CliffordCorrespondence.lean 系へ移設可。
- ⚠ 技術注意 (再発防止): `restrictionMultiplicity_eq_zero_of_forall_eq_one` の適用は
  `(N := ...)` 明示 pin 必須 — implicit N が `(x : ↥H)` coercion 経由で ambient 群に誤
  unify し whnf heartbeat 爆発。bundled ↑⟨_, h⟩ と plain の混在は
  `simp only [IrreducibleCharacter.coe_mk]` で正規化してから rw/exact する。
- census テーブル (Lemma 1(a)/2(a) 行) も修正済み。
