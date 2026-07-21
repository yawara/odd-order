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

## 参照

- `OddOrder/Peterfalvi/Appendices/FeitSibley.lean:386` (sorry), `:92` (Hypothesis 構造)
- `references/peterfalvi/pdf/09.0_*.pdf` p.145 (Lemma 2(a)), coq `PFsectionN` の対応 Clifford
- issue 1049 (Lemma 1(a), closed), 下流 = 2(b)-isometry (FeitSibley.lean:411) / 2(c) (:431)
