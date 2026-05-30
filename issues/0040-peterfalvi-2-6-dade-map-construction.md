---
id: 40
slug: peterfalvi-2-6-dade-map-construction
title: "Peterfalvi (2.6.b)/(2.8)-(2.10) Dade 写像の構成 (inclusion-exclusion)"
created: 2026-05-27
---

# Peterfalvi (2.6.b)/(2.8)-(2.10) Dade 写像の構成 (inclusion-exclusion)

## 背景

§4 The Dade Isometry のうち、**(2.7) adjoint formula は issue 0039 で完成**
(`OddOrder/Peterfalvi/S04_DadeIsometry.lean`, sorry-free).  残るのは

- **(2.6.b)** Dade 写像 τ が virtual character を virtual character に写すこと
- **(2.8)-(2.10)** その証明に使う構造補題 + inclusion-exclusion 公式

で、これらは合わせて **Dade 写像 τ の明示的構成** に相当する.

現状 S04 は (2.6) を `DadeIsometryData` / `FullDadeIsometryData` の
**インターフェース (仮定束)** として扱い、構成は保留している.  §5-§8 は
このインターフェース + (2.7) adjoint formula を使うので、本 issue は §4 の
完成度を上げるものだが §5-§8 の前提ではない (優先度は中).

## 証明構造 (教科書 `04.4_pp_10_14_The_Dade_Isometry.mmd` L56-124)

- **(2.8)** 非空 `B ⊆ A` に対し `H(B) = ⋂_{a∈B} H(a)`, `N_L(B)` = `B` の L-正規化群,
  `M(B) = H(B)·N_L(B)`.  このとき `M(B) = H(B) ⋊ N_L(B)`
  (H(B) ◁ M(B), H(B) ∩ N_L(B) = 1).  `card_centralizer_eq` 同様の積構造.
- **(2.9)** Notation: `α ∈ CF(L,A)` と非空 `B` に対し `α_B ∈ CF(M(B))` を
  `α_B(hx) = α(x)` (h∈H(B), x∈N_L(B)) で定義.  = `α ∘ f_B`,
  `f_B : M(B) → L` は核 `H(B)` の商準同型.  α が virtual char ⟹ α_B も virtual char.
- **(2.10)** **核心の inclusion-exclusion**: ℬ = 非空部分集合の L-共役類代表系 として
  `α^τ = -∑_{B∈ℬ} (-1)^|B| Ind_{M(B)}^G α_B`.
  右辺は誘導指標の交代和なので virtual character ⟹ (2.6.b).
  - **(2.10.1)** `x∈L`, 非空 `B` に対する Ind 値の式 (g の共役での寄与).
  - **(2.10.2)** `C_{H(B)}(a) = H(B∪{a})` (a∈A).
  - **(2.10.3)** `g ∉ ⋃_a (aH(a))^G` なら `(Ind_{M(B)}^G α_B)(g) = 0`;
    `g ∈ (aH(a))^G` なら値の明示式.
  - 証明: γ := -∑(-1)^|B| Ind α_B とおき、γ(g) を場合分け.  項が 2 つずつ相殺
    (B と B∪{a} のペア, (2.10.2) 経由) し `B={a}` の項だけ残る.
    `𝒜(g, H(a)a) = x·C_G(a)` (= issue 0039 の `card_conj_fiber` の中身) を使い
    `γ(g) = α(a)·|C_G(a)|/(|C_L(a)||H(a)|) = α(a) = α^τ(g)`.
- **(2.6)** (a) (2.7) から従う (β^τ が aH(a) 上定数). (b) (2.10) から.
- **(2.11)** `A₁ ⊆ A` が L-正規化されるとき (2.2) が A₁ で成立し、τ₁ は τ の
  CF(L,A₁) への制限.  (現 S04 の `restrict` インターフェースを実 τ で正当化.)

## 必要インフラ

- 誘導指標: `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
  (`induce`, `induceSum`, 加法性, support) は存在.  **誘導指標値公式
  (Frobenius reciprocity / Ind の明示値)** が追加で要りそう ((2.10.1)/(2.10.3)).
- 商準同型 `f_B : M(B) → L` と `α_B = α ∘ f_B` の virtual-char 保存.
- 非空部分集合の L-共役類代表系 ℬ と Möbius 型相殺の組合せ論.
- issue 0039 で作った `card_conj_fiber`, `card_centralizer_eq` を再利用.

## やること

- [x] (2.8) `M(B) = H(B) ⋊ N_L(B)` の構造補題 (H(B), N_L(B), M(B) を定義)
      — 2026-05-30 完了 (sorry-free, axiom-clean; 下記「進捗 (3)」).
- [x] (2.9) `α_B` を商準同型 `f_B` 経由で定義、virtual char 保存
      — 2026-05-30 完了 (sorry-free, axiom-clean; 下記「進捗 (3)」).
- [x] **(2.10.2)** `C_{H(B)}(a) = H(B∪{a})` — 2026-05-30 完了 (`centralizer_inf_hIntersection`
      + `mem_H_of_mem_centralizer_coprime`; 下記「進捗 (4)」).
- [x] **(2.9) 定義方程式** `α_B(h·b)=α(b)` — 2026-05-30 完了 (`alphaB_apply_mul` +
      `dadeQuotientHom_coe_of_mem_nLStabilizerIn`; Möbius keystone; 下記「進捗 (4)」).
- [x] **(2.5)+(2.6.a) Dade 写像 τ を pointwise 構成** — 2026-05-30 完了
      (`Hypothesis.dadeMap` / `isDadeMap_dadeMap` / `dadeIsometryData`; **実 DadeIsometryData**,
      もはやインターフェース仮定でない; 下記「進捗 (4)」).  **これで (2.10) は (2.6.b) 専用に縮小**.
- [x] 誘導指標値公式 (transversal collapse): `induceSum_apply_eq_sum_filter` /
      `induce_apply_eq_sum_filter` (= **(2.10.3)** unscaled/normalized 点別値の generic 形;
      `x⁻¹gx∈H` の x のみ寄与) — 2026-05-30 完了 (下記「進捗 (5)」).
- [x] **(2.10.1) Ind L-共役不変 (generic 形)**: `induceSum_map_conj` / `induce_map_conj`
      (= `Ind_{H^ℓ}^G (transportConj ℓ θ) = Ind_H^G θ`) — 2026-05-30 完了 (下記「進捗 (5)」).
- [x] **(2.10.1) Dade-specific** `Ind_{M(B^x)} α_{B^x} = Ind_{M(B)} α_B` — 2026-05-30 完了
      (`induce_alphaB_conjFinset`; M(B^x)=M(B)^x の subgroup 共役 + α_{B^x}=transportConj x α_B の
      class function transport + generic `induce_map_conj`; 下記「進捗 (6)」).
- [x] **(2.10.1) packaged form** `induceAlphaBTerm_conjFinset` — 2026-05-30 完了.  bare-`induce`
      不変性 `induce_alphaB_conjFinset` を packaged summand `induceAlphaBTerm`
      (自前 `Invertible (|M(B)|:ℂ)` instance 持ち) に持ち上げ.  transversal `ℬ` 和
      `-∑_{B∈ℬ}(-1)^|B| Ind_{M(B)} α_B` が代表元選択に依らない well-definedness 事実
      (`conjFinset_card` で sign も `L`-不変).  `simp only [induceAlphaBTerm]` +
      `induce_alphaB_conjFinset`; Invertible は `Invertible.subsingleton` で整合.
- [~] (2.10.3) Dade-specific 点別値: **transversal half + vanishing + value (N_L(B)-集計形) 完了**:
      `induce_alphaB_apply_eq_sum_conjFiber` (第 1 式 `(Ind α_B)(g)=⅟|M(B)|∑_{x∈𝒜(g,M(B))}induceTerm`)
      + `exists_nLStabilizerIn_alphaB_induceTerm` (per-term `α_B(x⁻¹gx)=α(b)` collapse, (2.9) keystone)
      (2026-05-30「進捗 (7)」); **vanishing case** `induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport`
      (g∉⋃(aH(a))^G ⇒ 0) 完了 (2026-05-30「進捗 (10)」, (2.1) keystone `exists_mem_centralizer_conj`);
      **value case (N_L(B)-集計形)** `induce_alphaB_apply_eq_sum_nLStabilizerIn`
      (`(Ind α_B)(g)=⅟|M(B)|·∑_{b∈N_L(B)} α(b)·|𝒜(g,H(B)b)|`, f_B coset partition; 2026-05-30「進捗 (10)」);
      **support-restricted 形** `induce_alphaB_apply_eq_sum_nLStabilizerIn_inA`
      (`∑_{b∈N_L(B)}` → `∑_{b∈N_L(B), b∈A}`; α 台外項脱落, 2026-05-30「進捗 (11)」).
      **a^L 特殊化完了** `induce_alphaB_apply_eq_alpha_mul_sum_conjL` (2026-05-30「進捗 (12)」, STEP 1):
      g∈(aH(a))^G で `(Ind α_B)(g)=(α(a)/|M(B)|)·∑_{b∈N_L(B)∩a^L}|𝒜(g,H(B)b)|`.
- [~] (2.10) inclusion-exclusion 本体 (Möbius 相殺) — **part (d) (RHS∈ℤ[Irr G]) 完了**
      (2026-05-30, 下記「進捗 (9)」); part (c) (Möbius 相殺で点別恒等式) は (2.1) coprime-action
      primitive 欠落でブロック (residual 精密化済).
- [x] **(2.6.a) を (2.7) から** — `IsDadeMap` + `HConjInvariant` ⟹ `IsDadeIsometry`
      を導出 (`isDadeIsometry_of_isDadeMap`, 2026-05-30 完了; 下記参照).
- [x] **(2.6.b) 前提 — `restrict_mem_ZIrr` + `induce_mem_ZIrr`** (Res/Ind が virtual char を
      保存; InducedCharacter.lean, 2026-05-30 完了, sorry-free + axiom-clean; 下記「進捗 (2)」).
      これは (2.6.b) の単一最大前提だった.
- [ ] (2.6.b) `PreservesVirtualCharacters (hyp.dadeMap)` → `FullDadeIsometryData` (残り)
- [ ] (2.11) restriction 互換性 (現 `restrict` インターフェースを実 τ で正当化)

## 完了条件

Dade 写像 τ が `IsDadeMap` + isometry + virtual-char 保存を満たすものとして
**構成** され (インターフェース仮定でなく)、(2.8)-(2.11) が形式化される.
規模が大きいので sub-issue 分割可.

## 参照

- 教科書: `references/peterfalvi/04.4_pp_10_14_The_Dade_Isometry.mmd` (2.6),(2.8)-(2.11)
- (2.7) 完成: issue 0040 の前提 = issues/closed/0039-*, commits 40211fe..0d8307e
- ミニロードマップ: `notes/peterfalvi/s04_dade_isometry.md`
- インフラ: `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`

## 進捗 2026-05-30 — (2.6.a) isometry を Dade-map equations から導出 (sorry-free)

**landed** (`OddOrder/Peterfalvi/S04_DadeIsometry.lean`, `section AdjointFormula`, green):

- `adjointAverageFun_dadeMap_eq` — Dade map `τ` と `β ∈ CF(L,A)` に対し
  (2.7) の平均化写像 `adjointAverageFun hyp (τ β)` が `A` 上で `β` に一致する.
  証明: `τ β` は coset `aH(a)` 上で定数 `β(a)` (`IsDadeMap.map_eq_of_mem_hCoset`)
  なので `H(a)` 上の平均は `β(a)`.  教科書 (2.6.a) 冒頭「`β^τ` は `aH(a)` 上定数」の計算.
- `isDadeIsometry_of_isDadeMap` — **(2.6.a) 本体**.  `IsDadeMap hyp τ` ((2.5) の
  pointwise equations) と `hyp.HConjInvariant` ((2.4.a)) だけから `IsDadeIsometry τ`
  (= `(α^τ,β^τ)_G = (α,β)_L`) を導出.  教科書の証明そのまま: (2.7) `adjoint_formula`
  に `χ := τ β`, `ψ := β` を入れる (`hψ` は `adjointAverageFun_dadeMap_eq`).
- `DadeIsometryData.ofIsDadeMap` (+ `_toDadeMap` simp) — Dade map と (2.5)/(2.4.a)
  仮定だけから `DadeIsometryData` を束ねる constructor.  従来 isometry を独立 field
  として仮定していたのを、defining equations から導けるようにした (インターフェース改善).

**意義**: (2.6.a) はもはやインターフェース仮定でなく `IsDadeMap` から導出される定理.
残る未構成は (2.6.b) (virtual char 保存) と、その前提となる Dade 写像 τ の明示構成
((2.8)-(2.10) inclusion-exclusion) のみ.

### 残作業の精密プラン ((2.6.b)/(2.8)-(2.10) — 大規模, 別 sub-issue 推奨)

検証済みのブロッカーと工数見積り (本セッションで mmd / 既存 API を確認):

1. **BLOCKER (critical, (2.6.b))**: `induce_mem_ZIrr` が repo にも mathlib にも無い.
   必要な statement:
   ```lean
   theorem induce_mem_ZIrr {H : Subgroup G} [Invertible (Nat.card H : ℂ)]
       {θ : ClassFunction H ℂ} (hθ : θ ∈ ZIrr H) :
       ClassFunction.induce H θ ∈ ZIrr G
   ```
   `InducedCharacter.lean` には `induce`/`induceSum` と線形性 (`induce_add`,
   `induce_smul`) はあるが、誘導が virtual char を virtual char に送る事実 (Frobenius
   相互律 + 整係数性) が無い.  証明には `⟨Ind χ_i, ψ⟩_G = ⟨χ_i, Res ψ⟩_H` 型の
   Frobenius reciprocity を整係数で先に立てる必要 (~80-100 LOC).  これが (2.6.b) の
   唯一かつ最大の前提 — **独立 sub-issue 化推奨**.

2. **(2.8) `M(B) = H(B) ⋊ N_L(B)`**: `hIntersection B = ⨅ a ∈ B, hyp.H a` と
   `N_L(B)` (B の L-set-stabilizer) を定義し disjointness を示す.
   - disjointness の数学は容易: `x ∈ H(B) ∩ N_L(B) ⊆ H(a) ∩ L`; `commute_of_mem_H`
     で `x ∈ C_L(a)`; `centralizer_disjoint` で `x = 1` (~20 LOC).
   - 注意: `Subgroup.setNormalizer` は mathlib では `Subgroup.normalizer` の **alias で
     subgroup 用** — Finset `B` の set-stabilizer には使えない.  `N_L(B)` は
     conjugation による `L` の set-stabilizer を手書き subgroup (carrier + closure 証明)
     として定義する必要があり、faithful な `N_L(B)` 構成自体が ~40-50 LOC.
3. **(2.9) `α_B = α ∘ f_B`**: 商準同型 `f_B : M(B) →* L` (核 `H(B)`) を (2.8) の
   semidirect 分解から構成し `α_B := α.comp f_B`.  `α ∈ ZIrr L ⟹ α_B ∈ ZIrr (M B)`
   は (1) の `induce_mem_ZIrr` とは別に「ZIrr の準同型 pullback (Res along f_B)」が要る.
4. **(2.10.1)-(2.10.3) + Möbius 相殺**: (2.10.3) の Ind 値公式 → `B` と `B∪{a}` の
   項が `(2.10.2) C_{H(B)}(a)=H(B∪{a})` 経由でペア相殺、`B={a}` のみ残す.
   `card_conj_fiber` (= 𝒜(g,H(a)a)=xC_G(a)) を再利用.  組合せ engine は
   `Finset.sum_powerset_insert` + `Finset.sum_powerset_neg_one_pow_card_of_nonempty`.
   最難、~150-200 LOC.
5. **接続**: `dadeSumMap` を (2.10) 公式で定義 → `IsDadeMap` を (2.10.3) から証明 →
   (2.6.a) は本セッションの `isDadeIsometry_of_isDadeMap` で自動 → (2.6.b) は (1)+(3)+
   (4) → `FullDadeIsometryData` 完成.  `[Fintype {a // a ∈ A}]` は `[Fintype G]` から
   `Fintype.ofFinite` で供給 (A は `Set G`).

依存順: (1) induce_mem_ZIrr [独立] → (2)(3) → (4) → (5).  全体 ~400-500 LOC.

## 進捗 2026-05-30 (2) — (1) induce_mem_ZIrr + restrict_mem_ZIrr 完成 (sorry-free, axiom-clean)

**landed** (`OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`,
`section VirtualCharacters` / `section InduceVirtualCharacters`, `lake build OddOrder` green,
`#assert_only_allowed_axioms` 両定理とも 3 axioms 全て allowlist 内):

- `restrict_repCharacterClassFunction` — `Res^G_H (χ_ρ) = χ_{ρ.comp H.subtype}` (ext で即).
- **`restrict_mem_ZIrr`** `(H : Subgroup G) [Finite G] {φ} (hφ : φ ∈ ZIrr G) : restrict H φ ∈ ZIrr H`.
  (2.6.b) の片側.  上の進捗ノートの「critical BLOCKER」評価は**誤りだった**: 当初は
  「ρ|H は既約でないので `repCharacterClassFunction_mem_ZIrr` が使えず、char-of-restriction
  分解 (issue 0026 module-theoretic blocker) が要る」と見ていたが、**同日 landed の keystone
  `character_mem_ZIrr` (CharacterCompleteness.lean、任意の有限次元複素表現の指標 ∈ ℤ[Irr]) が
  既約性を要求しない**ため、span induction の base case (φ = χ_ρ, ρ 既約) で
  `restrict H φ = repCharacterClassFunction (ρ.comp H.subtype)` と書き換え
  `character_mem_ZIrr (ρ.comp H.subtype)` を直接適用するだけで済む (ρ|H の可約性は無問題).
  線形ケースは `restrict_add`/`restrict_smul` (ℤ-smul は `Int.cast_smul_eq_zsmul` 経由).
- `inner_mem_ZIrr_int` — `φ, ψ ∈ ZIrr G ⇒ ⟨φ, ψ⟩_G ∈ ℤ`.  ψ で span induction、base は
  `mem_ZIrr_inner_int` (ZIrrFourier)、右引数の共役線形性 (`inner_smul_right` + `star_intCast`).
- **`induce_mem_ZIrr`** `(H : Subgroup G) [Fintype G] [Invertible (Nat.card G:ℂ)] [Fintype H]
  [Invertible (Nat.card H:ℂ)] {θ} (hθ : θ ∈ ZIrr H) : induce H θ ∈ ZIrr G`.  (2.6.b) の本体.
  θ で span induction.  base case (θ ∈ Irr H): 各 χ ∈ Irr G に対し numerical Frobenius
  reciprocity `inner_induce_eq_inner_restrict` で `⟨Ind θ, χ⟩_G = ⟨θ, Res H χ⟩_H`、
  `restrict_mem_ZIrr` で `Res H χ ∈ ZIrr H` ⇒ `inner_mem_ZIrr_int` で整数係数 `f χ`.
  `Φ := ∑_{χ∈Irr G} (f χ) • χ ∈ ZIrr G` を作り、`Ind θ - Φ` が全 irreducible と直交
  (対角 Fourier 係数一致 by `irreducibleCharacter_inner_eq_ite`) ⇒ completeness
  `classFunction_eq_zero_of_orthogonal` で `Ind θ = Φ`.  線形ケースは `induce_add`/`induce_smul`.

これで上記「残作業プラン」の**項目 (1) (critical, 唯一最大の前提) が解決**.  AxiomsCheck.lean に
両定理を登録済み.  残る (2.6.b) 構成タスクは (2) M(B)=H(B)⋊N_L(B) / (3) α_B pullback /
(4) Möbius 相殺 / (5) 接続 のみ (これらは依然 ~350-450 LOC、別 sub-issue 推奨).

実装:
- `restrict_mem_ZIrr`, `induce_mem_ZIrr` ともに `ClassFunction` namespace
  (`OddOrder.RepresentationTheory.ClassFunction.{restrict,induce}_mem_ZIrr`).
- InducedCharacter.lean が ZIrrFourier + CharacterCompleteness を import するよう変更
  (循環なし; 下流 S02/S03/Clifford ビルド確認済み).

## 進捗 2026-05-30 (3) — (2.8) M(B)=H(B)⋊N_L(B) + (2.9) f_B/α_B 完成 (sorry-free, axiom-clean)

上記「残作業プラン」の **項目 (2) M(B)=H(B)⋊N_L(B) と (3) α_B pullback が解決**.
3 コミット (commits 527053b, 527d486, a6dd522), `lake build OddOrder` + `OddOrder.AxiomsCheck`
ともに green, 新規 sorry/admit/axiom 無し.

### ZIrr pullback (項目 (3) の核, 先行調査の「ブロッカー」評価は誤り)

`OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean` + `InducedCharacter.lean`:
- `ClassFunction.compHom (f : H →* G) (φ : ClassFunction G k) : ClassFunction H k` := `φ ∘ f`
  (= `restrict` の `f = H.subtype` 一般化), + `compHom_{zero,add,neg,sub,smul}`.
- **`ClassFunction.compHom_mem_ZIrr`** `[Finite H] (f : H →* G) (hφ : φ ∈ ZIrr G) : compHom f φ ∈ ZIrr H`.
  証明は `restrict_mem_ZIrr` と同型の span induction; base case で
  `compHom f (χ_ρ) = χ_{ρ.comp f}` と書換え `character_mem_ZIrr (ρ.comp f)` を適用.

**先行調査の誤り訂正**: 「(2.9) の `α_B ∈ ZIrr M(B)` は `Representation.IsIrreducible` の
inflation/precompose-surjective 保存 (~30-50 LOC, mathlib/repo に無い) を要しブロック」と
されていたが**誤り**.  `character_mem_ZIrr` (同 session landed, **任意の**有限次元複素表現の
指標 ∈ ℤ[Irr], 既約性不要) のおかげで, `ρ.comp f` の既約性は不要で span induction の
base case が直接片付く.  `f` の全射性も不要 (N_L(B) は L の真部分群でよい).

### (2.8) `OddOrder/Peterfalvi/S04_DadeIsometry.lean` `section SemidirectStructure`

`Hypothesis` namespace 内, `end Hypothesis` の直前:
- `conjA l a` = `⟨l·a·l⁻¹, _⟩ : {a//a∈A}` (L の A 上共役作用), `conjA_{one,mul,inv_conjA,…}`.
- `hIntersection B hB = H(B) = ⨅_{a∈B} H(a)` (`Finset.inf'`), `hIntersection_le`, `mem_hIntersection`.
- `setLStabilizer B : Subgroup L = N_L(B)` (B の L-set-stabilizer, 手書き).  `inv_mem'` は
  「ℓ 共役が finite set B の単射自己写像 ⇒ 全射」(`Finset.surjOn_of_injOn_of_card_le`).
  `Subgroup.setNormalizer` は `Subgroup.normalizer` の alias で **subgroup 用 (Finset 不可)** を実機で確認.
- `nLStabilizerIn B = N_L(B)` を G の subgroup として (`.map L.subtype`), `nLStabilizerIn_le_L`.
- `mem_H_conjA_iff` — (2.4.a) HConjInvariant 経由: `y ∈ H(conjA l a) ↔ l⁻¹yl ∈ H(a)`.
- `nLStabilizerIn_le_normalizer` — N_L(B) ◁ 正規化 (ℓ が B を置換 ⇒ H(B) 保つ).
- `hIntersection_disjoint_nLStabilizerIn` — H(B) ∩ N_L(B) = 1
  (`commute_of_mem_H` + `centralizer_disjoint`).
- `mBSubgroup B = M(B) = H(B) ⊔ N_L(B)`, `coe_mBSubgroup` (台 = H(B)·N_L(B)),
  **`card_mBSubgroup`** = |M(B)| = |H(B)|·|N_L(B)| (`card_centralizer_eq` と同じ bijection 論法).

### (2.9) 同ファイル, (2.8) の後

- `hIntersection_subgroupOf_normal` — H(B) ◁ M(B) (`normal_subgroupOf_iff_le_normalizer` + `sup_le`).
- `isComplement'_subgroupOf` — ↥M(B) 内で N_L(B) と H(B) が complementary
  (`isComplement'_of_card_mul_and_disjoint`; card は `subgroupOfEquivOfLe` + `card_mBSubgroup`).
- **`dadeQuotientHom = f_B : M(B) →* L`** = 合成 `M(B) → M(B)/H(B) ≅ N_L(B) ↪ L`
  (`IsComplement'.QuotientMulEquiv [H(B).Normal]` + `Subgroup.inclusion`).
- **`ker_dadeQuotientHom`** = `ker f_B = H(B).subgroupOf M(B)` (mk' 以降単射 ⇒ ker = ker mk';
  教科書「核 H(B) の自然準同型」を faithful に裏付け).
- `alphaB B α = α ∘ f_B` (`ClassFunction.compHom`), **`alphaB_mem_ZIrr`** = α∈ℤ[Irr L] ⇒
  α_B∈ℤ[Irr M(B)] (`compHom_mem_ZIrr`).

`card_mBSubgroup` / `ker_dadeQuotientHom` / `alphaB_mem_ZIrr` / `compHom_mem_ZIrr` を
AxiomsCheck.lean に登録 (各 3 axioms allowlist 内; AxiomsCheck が S04 を import).

### 残作業 (Dade 写像 τ 明示構成の最終段, 別 sub-issue 推奨)

依存プランの残りは **(4) (2.10) inclusion-exclusion (Möbius 相殺) と (5) 接続** のみ:
- (2.10.1) `Ind_{M(B^x)} α_{B^x} = Ind_{M(B)} α_B` (L-共役不変).
- (2.10.2) `C_{H(B)}(a) = H(B∪{a})` (a∈A).  H(B∪{a}) ⊆ H(a) ⊆ C_G(a) ⇒ ⊆ C_{H(B)}(a);
  逆は C_{H(B)}(a) が |C_L(a)| と互いに素な C_G(a) の部分群 ⇒ ⊆ H(a).
- (2.10.3) Ind 値公式 (g∉⋃(aH(a))^G なら 0; g∈(aH(a))^G なら明示式).
- (2.10) 本体: `γ := -∑_{B∈ℬ} (-1)^|B| Ind α_B`, g で場合分け, B と B∪{a} が
  (2.10.2) 経由でペア相殺, B={a} のみ残し `𝒜(g,H(a)a)=xC_G(a)` (issue 0039 `card_conj_fiber`)
  で `γ(g)=α(a)=α^τ(g)`.  組合せ engine = `Finset.sum_powerset_*` 系. 最難 ~150-200 LOC.
- (5) `dadeSumMap` を (2.10) 公式で定義 → `IsDadeMap` を (2.10.3) から → (2.6.a) は既存
  `isDadeIsometry_of_isDadeMap` で自動 → (2.6.b) は (2.10) の Ind 交代和 + `induce_mem_ZIrr`/
  `alphaB_mem_ZIrr` → `FullDadeIsometryData` 完成.
- 誘導指標**値**公式 (Ind の点別値, (2.10.1)/(2.10.3) 用) は未実装で要追加
  (InducedCharacter.lean の `induce` 定義から点別値を出す補題).

## 進捗 2026-05-30 (4) — pointwise 構成で DadeIsometryData 実体化 + (2.10.2)/(2.9) keystone

3 コミット (9a81831 (2.10.2), 2a7133c 構成, 64a546c (2.9)定義方程式), `lake build OddOrder`
+ `OddOrder.AxiomsCheck` green, 新規 sorry/axiom 無し.

**アーキテクチャ転換 (重要)**: 旧プランは「(2.10) 公式で `dadeSumMap` を定義 → そこから
IsDadeMap を導出」だった.  本セッションで **τ を (2.5) 点別定義で直接構成** する方が
IsDadeMap+isometry に対して遥かに簡明と判明し、そちらに切替えた:

- `Hypothesis.dadeValue α g` / `dadeMapCF` / `dadeMap` — (2.5) 点別: g∈(aH(a))^G なら α(a),
  else 0.  well-defined は (2.4.b) `isConj_in_L_of_mul_H` 経由 (`dadeValue_eq`).
- `Hypothesis.isDadeMap_dadeMap` — 構成から IsDadeMap を**証明** (もはや仮定でない).
- `Hypothesis.dadeIsometryData hconj` — (2.5)+(2.6.a) を束ねた**実 `DadeIsometryData`**
  (`ofIsDadeMap` 経由, isometry は既存 `isDadeIsometry_of_isDadeMap` で自動).

**この結果 (2.10) inclusion-exclusion が必要なのは (2.6.b) virtual-char 保存だけ** に縮小.
IsDadeMap/isometry はもう (2.10) 非依存で構成済.

(2.10.2) と (2.9) keystone も完了:
- `mem_H_of_mem_centralizer_coprime` + `centralizer_inf_hIntersection` = **(2.10.2)**
  `C_G(a)⊓H(B)=H(insert a B)` (O_{π'}-containment: pow_index_mem + CRT).
- `dadeQuotientHom_coe_of_mem_nLStabilizerIn` + `alphaB_apply_mul` = **(2.9) 定義方程式**
  `α_B(h·b)=α(b)` (f_B が N_L(B) を retract; QuotientMulEquiv の補元 retraction 経由).
  Möbius (2.10.3) で α_B 点別値を扱う必須 keystone.

### 残作業 (2.6.b 専用、現フロンティア)

目標: `PreservesVirtualCharacters (hyp.dadeMap)` を示し `FullDadeIsometryData` 化.
唯一の道は (2.10) 恒等式 `hyp.dadeMap α = -∑_{B∈ℬ}(-1)^|B| Ind_{M(B)} α_B` を点別証明
(RHS は `induce_mem_ZIrr`+`alphaB_mem_ZIrr` で manifest に ZIrr G).  依存:

1. **代表系 ℬ の Lean 表現** (構造的ブロッカー): 非空部分集合の L-共役類代表系.
   推奨 = `conjA` を `Finset {a//a∈A}` 上の `MulAction L` に持ち上げ、orbit 商
   `MulAction.orbitRel.Quotient` 上で `Quotient.out` 代表をとる (or 非空部分集合の subtype).
   ℬ-和は整数交代和なので (2.6.b) は manifest.
2. **(2.10.1)** `Ind_{M(B^x)} α_{B^x} = Ind_{M(B)} α_B` (ℬ→𝒫 切替 / 商 well-def に必須).
   要: `M(B^x)=x·M(B)·x⁻¹` membership (H(B^x)=x H(B)x⁻¹, N_L(B^x)=x N_L(B)x⁻¹) +
   induceSum の reindex (t↦tx).  `alphaB_apply_mul` で transport α_{B^x}(xmx⁻¹)=α_B(m).
3. **(2.10.3)** Ind 点別値: `induce_apply` (既存) + α_B 値 (`alphaB_apply_mul`) +
   `card_conj_fiber` (issue 0039) で `𝒜(g,H(B)b)` 集計.
4. **(2.10) Möbius 相殺** (最難 ~150-200 LOC): `Finset.sum_involution` で toggle-a 対合
   B↔B△{a}, (2.10.2) で C_{H(B)}(a)=C_{H(B∪a)}(a) 経由 sign 相殺、survivor B={a}.
5. **接続**: 上の恒等式 → `PreservesVirtualCharacters` → `FullDadeIsometryData` 完成.

着手順: 1 (transversal infra) → 2 → 3 → 4 → 5.  全体 ~250-400 LOC、別 focused session 推奨.

## 進捗 2026-05-30 (5) — (2.10.1)/(2.10.3) generic 誘導指標インフラ完成 (sorry-free, axiom-clean)

`OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean` に, 上記「依存」
項目 2 (2.10.1) / 項目 3 (2.10.3) の **generic (任意 subgroup `H` / class function `θ`) 形**
を landed.  `lake build OddOrder` + `OddOrder.AxiomsCheck` green, 新規 sorry/axiom 無し
(4 定理とも 3 axioms 全 allowlist 内).

- **(2.10.3) transversal value**:
  - `induceSum_apply_eq_sum_filter` `(H θ g) : induceSum H θ g = ∑ x∈univ.filter (x⁻¹gx∈H), induceTerm H θ x g`.
  - `induce_apply_eq_sum_filter` (normalized, `⅟|H| * ∑_filter`).
  証明は `induceTerm_of_not_mem` で off-filter 項消去 → `Finset.sum_subset (filter_subset)`.
  decidability は `open scoped Classical in` で供給 (両定理同一 `Classical.propDecidable` ⇒ `rw` 整合).
- **(2.10.1) L-conjugacy invariance**:
  - `transportConj ℓ θ : ClassFunction ↥(H.map (MulAut.conj ℓ)) k` — `θ` を共役同型
    `MulEquiv.subgroupMap (MulAut.conj ℓ) H : H ≃* H^ℓ` の逆で precompose (`compHom`).
    値: `transportConj ℓ θ ⟨y,_⟩ = θ ⟨ℓ⁻¹yℓ,_⟩`.
  - `induceTerm_transportConj` (keystone summand 恒等式): `induceTerm (H^ℓ) (transportConj ℓ θ) (x*ℓ⁻¹) g = induceTerm H θ x g`.
    `Subgroup.mem_map_equiv` + `MulAut.conj_symm_apply` で条件・値とも `e.symm(...)=x⁻¹gx` に collapse.
  - **`induceSum_map_conj`** `: induceSum (H^ℓ) (transportConj ℓ θ) = induceSum H θ`.
    `Fintype.sum_equiv (Equiv.mulRight ℓ)` で reindex (t↦t·ℓ), 各項 `induceTerm_transportConj` で一致.
  - **`induce_map_conj`** (normalized): `induce (H^ℓ) (transportConj ℓ θ) = induce H θ`.
    `|H^ℓ|=|H|` (`Subgroup.card_map_of_injective`) ⇒ 2 つの `⅟(|·|:k)` が `invertible_unique` で一致.

**残 (Dade 適用)**: 上記は generic.  (2.6.b) 用には `H↦M(B)`, `θ↦α_B` を適用し,
(2.10.1) は `M(B^x)=x M(B) x⁻¹` membership + `alphaB_apply_mul` で α_{B^x} transport を,
(2.10.3) は `card_conj_fiber` (issue 0039) で `𝒜(g,H(B)b)` を集計する段が残る (項目 4 Möbius も).

## 進捗 2026-05-30 (6) — (2.10.1) Dade-specific 共役インフラ `M(B^x)=M(B)^x` (sorry-free, axiom-clean)

`OddOrder/Peterfalvi/S04_DadeIsometry.lean` `section SemidirectStructure` 内
`section ConjugacyInvariance` に, 上記「残作業」項目 2 (2.10.1) の **subgroup 共役側**を landed
(`lake build OddOrder` + `OddOrder.AxiomsCheck` green, 新規 sorry/axiom 無し; 3 定理とも 3 axioms 全 allowlist 内).

- `conjFinset l B = B.image (conjA l)` (= `B^l`), `mem_conjFinset`, `conjFinset_nonempty`.
- `conjA_conj` — `(conjA l)⁻¹∘conjA ℓ∘conjA l = conjA (l⁻¹ℓl)` (`conjA_mul` 2 回).
- **`hIntersection_conjFinset`** = **(2.10.1) `H(B^x)=H(B)^x`**: `H(B^l) = conj l • H(B)`.
  membership: `mem_hIntersection` + `mem_pointwise_smul_iff_inv_smul_mem` + (2.4.a) `mem_H_conjA_iff`.
- `mem_setLStabilizer_conjFinset` — `ℓ∈N_L(B^l) ↔ l⁻¹ℓl∈N_L(B)` (`conjA_conj` で stabilizer 条件を untwist).
- **`nLStabilizerIn_conjFinset`** = **(2.10.1) `N_L(B^x)=N_L(B)^x`**: `N_L(B^l) = conj l • N_L(B)`
  (L 内 set-stabilizer 共役を G の pointwise smul に移送; `push_cast`+`group` で coercion 整合).
- **`mBSubgroup_conjFinset`** = **(2.10.1) `M(B^x)=M(B)^x`**: `M(B^l) = conj l • M(B)`
  (`mBSubgroup = H(B)⊔N_L(B)` + `Subgroup.smul_sup` で 2 因子から合成).
- `mBSubgroup_conjFinset_eq_map` — `M(B^l) = M(B).map(conj l)` (= generic `induce_map_conj` が
  生成する subgroup 形; `pointwise_smul_def`+`rfl`).
- `induce_congr_of_subgroup_eq` — subgroup 等式越しの `induce` 合同 (`subst`+`Subsingleton.elim`
  で Invertible instance も一致).
- **`alphaB_conjFinset_eq_transportConj`** = **(2.9)/(2.10.1) class function transport**:
  `M(B^l)` 上の `α_{B^l}` が `transportConj l α_B` (M(B)^l 上へ移送した α_B) に一致.  両辺を
  `alphaB_apply_mul` で計算: `m=l⁻¹yl=h·b` 分解 ⇒ LHS `α(lbl⁻¹)` (y=(lhl⁻¹)(lbl⁻¹)), RHS `α(b)`,
  α の L-class 不変性 `α(lbl⁻¹)=α(b)` (`of_isConj`, 共役子 l⁻¹) で bridge.
- **`induce_alphaB_conjFinset`** = **(2.10.1) Dade-specific 本体**:
  `Ind_{M(B^x)} α_{B^x} = Ind_{M(B)} α_B`.  `induce_congr_of_subgroup_eq` +
  `alphaB_conjFinset_eq_transportConj` + generic `induce_map_conj` で合成.  Invertible instance は
  `invertibleOfNonzero (card_pos.ne')` で局所供給.

なお ℬ 代表系 / Möbius 用に `conjA` の Finset 作用律も landed:
`conjFinset_one` (B^1=B), `conjFinset_mul` (B^{l₁l₂}=(B^{l₂})^{l₁}), `conjFinset_card`
(|B^l|=|B|, Möbius sign `(-1)^|B|` 用).  これで `MulAction L (Finset {a//a∈A})` (orbit 商で
ℬ を取る) は equational には準備済 (instance 化は未, 将来 transversal step で).

**残 ((2.6.b) まで)**: (2.10.1) Dade-specific は**完了**.  残るは
(2.10.3) Dade 点別値 (`card_conj_fiber` で `𝒜(g,H(B)b)` 集計) → ℬ 代表系 (項目 1, 構造的) →
Möbius 相殺 (項目 4, `Finset.sum_involution`) → `PreservesVirtualCharacters` → `FullDadeIsometryData`.

## 進捗 2026-05-30 (7) — (2.10.3) transversal half 完成 (sorry-free, axiom-clean)

`OddOrder/Peterfalvi/S04_DadeIsometry.lean` `section SemidirectStructure` 内
`section PointwiseValue` に, (2.10.3) の **transversal value 半分** を landed
(`lake build OddOrder` + `OddOrder.AxiomsCheck` green, 新規 sorry/axiom 無し; 2 定理とも 3 axioms 全 allowlist 内).

- `conjFiber g X` = **`𝒜(g,X) = {x∈G | x⁻¹gx∈X}`** (Finset, `[Fintype G]`), `mem_conjFiber`.
- **`induce_alphaB_apply_eq_sum_conjFiber`** = (2.10.3) **第 1 式**:
  `(Ind_{M(B)} α_B)(g) = ⅟|M(B)| · ∑_{x∈𝒜(g,M(B))} induceTerm M(B) α_B x g`.
  証明 = generic `induce_apply_eq_sum_filter` + `rfl` (filter = conjFiber, subgroup↔Set coercion defeq).
- `alphaB_induceTerm_of_mem` — filter 上で `induceTerm M(B) α_B x g = α_B⟨x⁻¹gx,_⟩` (`induceTerm_of_mem`).
- **`exists_nLStabilizerIn_alphaB_induceTerm`** = (2.10.3) **per-term collapse** `α_B(x⁻¹gx)=α(b)`:
  `x⁻¹gx∈M(B)` を `coe_mBSubgroup` で `h·b` (h∈H(B), b∈N_L(B)) に分解し, (2.9) keystone
  `alphaB_apply_mul` で `induceTerm = α(b)` を取り出す. これが Möbius 計算で各項を `α(b)` 化する核.

### 残ブロッカー (precise): coprime-action 共役 primitive

(2.10.3) の **残り 2 つ** — (i) vanishing `g∉⋃_a(aH(a))^G ⇒ (Ind α_B)(g)=0`,
(ii) `card_conj_fiber` 集計 `∑_{b∈N_L(B)∩a^L}|𝒜(g,H(B)b)|` — は共に, 教科書の

> "_hb_ is conjugate to an element of `C_{H(B)}(b)·b`" (proof of (2.10.3))

すなわち **coprime-action 共役**:
`K=H(B)` 有限部分群, `b` が `K` を正規化 (b∈N_L(B)) し `gcd(|K|,ord b)=1` (= (2.2.c)) のとき,
`h·b` (h∈K) は `K`-共役で `c·b` (c∈C_K(b)) に移る (Glauberman/coprime action の特殊形),
を必要とする.  これは **mathlib の `Mathlib/GroupTheory/` にも本 repo にも無い** (確認済:
coprime + IsConj/centralizer-coset の補題は皆無; mathlib にあるのは `orderOf_mul_..._coprime` 系のみ).

`c∈C_{H(B)}(b)=H(B∪{b})⊆H(b)` ((2.10.2)+`b∈A`) かつ `c·b=b·c` なので
`h·b ~ c·b = b·c ∈ b·H(b)`, すなわち `g∈(bH(b))^G⊆dadeSupport`.  これさえ立てば vanishing は
`exists_nLStabilizerIn_alphaB_induceTerm` + 対偶で即, 集計は `card_conj_fiber` (issue 0039) で完了.

→ **次の sub-issue 候補**: `Mathlib`-style の coprime-action conjugacy-to-centralizer-coset 補題
(`OddOrder/GroupTheory/CoprimeConjugacy.lean` に追加)  これは (2.10.3) 完成と Möbius (2.10) の前提.

## 進捗 2026-05-30 (8) — (2.10) 代表系 ℬ infra (MulAction + orbit transversal + 軌道公式) 完成 (sorry-free, axiom-clean)

`OddOrder/Peterfalvi/S04_DadeIsometry.lean` `section SemidirectStructure` 内
`section Transversal` に, 上記「残作業 (2.6.b)」**項目 1 (代表系 ℬ の Lean 表現, 構造的ブロッカー)**
を landed (`lake build OddOrder` + `OddOrder.AxiomsCheck` green, 新規 sorry/axiom 無し;
3 定理とも 3 axioms 全 allowlist 内).  Round 3 commit 7477966 の `conjFinset_{one,mul,card}` は
**既に現コードに統合済み** (planner の「未統合」評価は誤り; L1216-1236) だったので, その上に構築:

- **`conjFinsetAction`** = `MulAction L (Finset {a//a∈A})`: `smul := conjFinset`, 法則は
  `conjFinset_one`/`conjFinset_mul` そのまま.  `hyp` 依存のため global instance でなく
  `@[reducible] noncomputable def` (downstream は `letI := hyp.conjFinsetAction` で起動).
  `@[simp] conjFinsetAction_smul` で `l • B = conjFinset l B`.
- **`stabilizer_conjFinsetAction`** = **(2.10) stabilizer = N_L(B)**:
  `MulAction.stabilizer L B = setLStabilizer hyp B`.  `l • B = B ↔ B.image (conjA l) = B`
  を `conjA l` 単射 + `Finset.eq_of_subset_of_card_le` (`conjFinset_card`) で `∀ a∈B, conjA l a∈B`
  に collapse.  これで軌道重み `|orbit B| = [L:N_L(B)]` が既存 N_L(B) infra に接続.
- `conjClassQuotient` = `MulAction.orbitRel.Quotient L (Finset {a//a∈A})` (L-共役類商),
  **`transversalRep`** = `Quotient.out` 代表 (= ℬ の 1 元).
- **`transversalRep_conj`**: 代表は自分のクラスと L-共役 `transversalRep ⟦B⟧ = B^l` (∃l∈L).
  `Quotient.out_eq'` + `Quotient.exact'` (orbitRel) で.  ℬ→𝒫 well-def の橋
  (項目 2 `induce_alphaB_conjFinset` (2.10.1) の双対側).
- **`card_orbit_mul_card_setLStabilizer`** = **(2.10) 軌道公式** `|orbit B|·|N_L(B)| = |L|`
  (= (2.10.3) 和の正規化重み).  `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` +
  `stabilizer_conjFinsetAction`.  `Nat.card` で述べ (`Fintype.ofFinite` で局所供給, 環境 Fintype 不要).

これで上記「残作業 (2.6.b)」**項目 1 完了**.  残るは項目 3 (2.10.3) 残ブロッカー
(coprime-action 共役 primitive, 進捗(7)末尾) → 項目 4 Möbius 相殺 (`Finset.sum_involution`,
ℬ-和の sign 相殺) → 項目 5 接続 (`PreservesVirtualCharacters` → `FullDadeIsometryData`).
ℬ-和は整数交代和なので (2.6.b) は項目 4-5 が立てば manifest (RHS は `induce_mem_ZIrr` +
`alphaB_mem_ZIrr` で ZIrr G).

## 進捗 2026-05-30 (9) — (2.10) part (d) RHS∈ℤ[Irr G] + (2.10)→(2.6.b) bridge 完成 (sorry-free, axiom-clean)

commit 6196d09, `lake build OddOrder` + `OddOrder.AxiomsCheck` green, 新規 sorry/admit/axiom 無し
(4 定理とも 3 axioms 全 allowlist 内).  教科書 (2.10) 証明を 2 つに分解した:
**part (c)** = Möbius 相殺で点別恒等式 `α^τ = γ` を立てる段, **part (d)** = RHS
`γ = -∑_{B∈ℬ}(-1)^|B| Ind_{M(B)} α_B` が virtual character である段.  **part (d) を完成**:

`OddOrder/Peterfalvi/S04_DadeIsometry.lean` `section VirtualCharacterRHS` (Hypothesis 内,
`end SemidirectStructure` 直前):
- **`induce_alphaB_mem_ZIrr`** — `α∈ℤ[Irr L]`, 非空 B ⟹ `Ind_{M(B)}^G α_B ∈ ℤ[Irr G]`.
  (2.9) pullback `alphaB_mem_ZIrr` + `ClassFunction.induce_mem_ZIrr` の合成.  `[Invertible(|G|:ℂ)]`
  + `[Invertible(|M(B)|:ℂ)]` 要 (induce_mem_ZIrr の section 変数).
- **`induceAlphaBTerm`** — 上の summand を **`Invertible(|M(B)|:ℂ)` instance を内包した**
  `ClassFunction G ℂ` として package (B は `{B//B.Nonempty}` subtype で nonempty 証明同伴).
  これで (2.10) RHS を通常の `Finset` 和として書ける (各 binder に invertibility を通さず済む;
  生 `letI` を binder 内に置くと `isDefEq` timeout する問題を回避).
- **`induceAlphaBTerm_mem_ZIrr`** / **`zsmul_induceAlphaBTerm_sum_mem_ZIrr`** — package 版の
  ℤ[Irr G] 帰属 + 任意 ℤ-結合 `∑_{p∈s} c p • induceAlphaBTerm ∈ ℤ[Irr G]`
  (`Submodule.sum_mem`/`smul_mem`).  (2.10) RHS は `c B = -(-1)^|B|`, `s = ℬ` の特殊形.

`PreservesVirtualCharacters` namespace 直後 (DadeMap section):
- **`preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum`** = **bridge**.
  「全 supported `α∈ℤ[Irr L]` で `hyp.dadeMap α` が *ある* induceAlphaBTerm の ℤ-結合に等しい」
  ⟹ `PreservesVirtualCharacters (hyp.dadeMap)` (= (2.6.b)).  これで **(2.6.b) は (2.10) 点別恒等式
  (part (c)) だけに縮小**.  恒等式さえ立てば bridge で即 `FullDadeIsometryData` 化.

### 残ブロッカー (precise, part (c) 専用): Peterfalvi (2.1) coprime-action primitive

part (c) Möbius 本体は **(2.10.3)** を要し, (2.10.3) は教科書 **(2.1)** を要する:

> **(2.1)** `K` 有限, `b` が `K` を正規化し `gcd(|K|, ord b)=1` ⟹ コセット `Kb` は
> `C_K(b)b` の `K`-共役 `[K:C_K(b)]` 個の disjoint union.

これは **mathlib にも本 repo にも無い** (進捗(7)末尾で確認済; mathlib の coprime 系は
`orderOf_mul_..._coprime` のみで centralizer-coset 構造の共役は皆無).  (2.1) は (2.10.3) の
- vanishing case `α_B(x⁻¹gx)≠0 ⟹ g∈(bH(b))^G` (hb~cb, c∈C_K(b))
- fiber 集計 `|𝒜(g,H(B)a)| = |𝒜(g,C_{H(B)}(a)a)|·[H(B):C_{H(B)}(a)]`
の両方を駆動する.  証明は `π=primes(ord b)` の π-part 引数 (既存 `conj_fixes_of_commute` の
役割交換版; ~100-150 LOC).  **本 issue の TARGET FILE 制約 (S04 のみ touch) 外** —
`OddOrder/GroupTheory/CoprimeConjugacy.lean` に置くべき独立 primitive ゆえ別 sub-issue.

(2.1) landed 後の part (c) 残工程: (2.10.3) Dade 点別値 (`induce_alphaB_apply_eq_sum_conjFiber`
+ per-term collapse `exists_nLStabilizerIn_alphaB_induceTerm` は landed 済; 集計のみ) →
Möbius 相殺 `Finset.sum_involution` で `B↔B∪{a}` pair (sign 反転, summand は
`centralizer_inf_hIntersection` = (2.10.2) `C_{H(B)}(a)=C_{H(B∪a)}(a)` で同一 ⟹ 相殺,
survivor `B={a}`) → `card_conj_fiber` (issue 0039) で `𝒜(g,H(a)a)=xC_G(a)` →
点別恒等式 → bridge `preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum` で (2.6.b).

## 進捗 2026-05-30 (10) — (2.1) keystone をブランチへ取り込み + (2.10.3) vanishing case 完成 (sorry-free, axiom-clean)

2 段階で landed.  `lake build OddOrder` + `OddOrder.AxiomsCheck` green, 新規 sorry/admit/axiom 無し.

### (a) (2.1) coset-conjugacy keystone を本ブランチへ cherry-pick

進捗 (9) 末尾で「part (c) 専用ブロッカー」とした **Peterfalvi (2.1)** は `main` 上 (commits
`6c4ff90`/`32b81df`, `OddOrder/GroupTheory/CoprimeConjugacy.lean`) に landed 済だったが,
**本ブランチ (claude/naughty-nash-…) は merge-base `f911d3a` で分岐しており未取り込み**だった
(branch sync gap; planner の「keystone landed this round」前提を満たすため取り込みが必要).
2 commit を cherry-pick (AxiomsCheck の conflict は `thompson_critical_omega` 行 — 本ブランチ未存在 —
を落として解決).  使える (2.1) 公開定理:
- `exists_mem_centralizer_conj` — g normalizing H, (|H|,orderOf g)=1 ⇒ 任意 hg∈Hg は H-共役で cg
  (c∈H⊓C_G(g)) に移る (**existence form**; (2.10.3) で消費する主系).
- `coset_eq_cosetConjImage` — Hg = ⋃_{x∈H}(C_H(g)g)^x (**set form**).
- rigidity core `conj_centralizes_of_coset_conj_eq`/`mem_centralizer_of_coset_conj_eq`.

### (b) (2.10.3) vanishing case (`section PointwiseValue`)

- **`coprime_orderOf_card_hIntersection`** — b∈A ⇒ `gcd(orderOf b, |H(B)|)=1` ((2.2.c) の (2.1) 入力).
  |H(B)| ∣ |H(b₀)| (b₀∈B) ⊥ |C_L(b)| (`centralizer_coprime`), orderOf b ∣ |C_L(b)| (b∈C_L(b)).
- **`induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport`** = **(2.10.3) vanishing case**:
  g∉dadeSupport=⋃_a(aH(a))^G ⇒ `(Ind_{M(B)} α_B)(g)=0`.  各 summand `induceTerm M(B) α_B x g`
  (x∈𝒜(g,M(B))) が ≠0 なら x⁻¹gx=h·b (h∈H(B), b∈N_L(B)), α(b)≠0 ⇒ b∈A (α の support).
  (2.1) `exists_mem_centralizer_conj` (b が coprime H(B) を正規化, `nLStabilizerIn_le_normalizer` 経由)
  で hb は H(B)-共役 cb (c∈C_{H(B)}(b)=H(B∪{b})⊆H(b), (2.10.2) `centralizer_inf_hIntersection`);
  c·b=b·c∈hCoset b ⇒ g∈(bH(b))^G⊆dadeSupport — 矛盾.

**意義**: vanishing case は **(2.10) 最終恒等式の `g∉dadeSupport` 半分そのもの** (s=ℬ 選択時, RHS 各項が
この lemma で 0, LHS は `dadeValue_of_not_mem_dadeSupport` で 0).  これで bridge の点別証明のうち
non-support side が片付いた.

### (c) (2.10.3) value case (N_L(B)-集計形) (`section PointwiseValue`, 進捗 (10) 追加分)

- **`dadeQuotientHom_eq_iff_mem_hIntersection_mul`** — m∈M(B), b∈N_L(B) で `f_B(m)=b ↔ (m:G)∈H(B)·b`.
  f_B=dadeQuotientHom が M(B)=H(B)⋊N_L(B) を N_L(B)-因子へ射影 (fiber=H(B)-coset).
  (⇐) m=h·b (h∈ker f_B=H(B), b は f_B が retract); (⇒) m·b⁻¹↦1 ⇒ m·b⁻¹∈ker=H(B).
- **`dadeQuotientHom_mem_nLStabilizerIn`** — `f_B(m)∈N_L(B)` (構造的; f_B は inclusion N_L(B)≤L を経由).
- **`induce_alphaB_apply_eq_sum_nLStabilizerIn`** = **(2.10.3) value case (specialization 前)**:
  `(Ind_{M(B)} α_B)(g) = ⅟|M(B)|·∑_{b∈N_L(B)} α(b)·|𝒜(g,H(B)·b)|`.  conjFiber 和を
  `Finset.sum_fiberwise_of_maps_to` で成分 b=f_B(x⁻¹gx) で再編成: fiber `{x: comp=b}` が
  `𝒜(g,H(B)·b)` (上 helper), summand は定数 α(b) ((2.9) `alphaB_apply_mul`).

### 残ブロッカー (precise): Möbius 相殺本体 (support side) — 純粋に組合せ的集計

bridge `preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum` の点別恒等式
`dadeMap α = -∑_{B∈ℬ}(-1)^|B| Ind_{M(B)} α_B` のうち, **残るのは `g∈(aH(a))^G` の support side のみ**.
**(2.10.3) は (集計形まで) 完了**したので, 残りは (2.10) 教科書証明の組合せ engine だけ
(mmd `04.4_*` の "Proof of (2.10)"):
1. **value case の a^L 特殊化** (容易, ~20-30 LOC): `induce_alphaB_apply_eq_sum_nLStabilizerIn` の
   `∑_{b∈N_L(B)}` から `α(b)≠0 ⟹ b∈A` かつ (2.4.b) `b∈a^L` で `∑_{b∈N_L(B)∩a^L}` へ, α(b)=α(a) 定数化.
2. **fiber 因子分解** (~50-80 LOC): `|𝒜(g,H(B)a)| = |𝒜(g,C_{H(B)}(a)a)|·[H(B):C_{H(B)}(a)]`.  (2.1)
   `coset_eq_cosetConjImage` (H(B)a = ⋃(C_{H(B)}(a)a)^x disjoint union, [H(B):C_{H(B)}(a)] 枚) を
   conjFiber cardinality に翻訳 (各 x-conjugate coset の preimage が等濃度).
3. **Möbius 相殺** (~80-120 LOC): 𝒫(a) (a∋ の非空部分集合) 上 `Finset.sum_involution` toggle-a (B↔B∪{a}),
   (2.10.2) `C_{H(B)}(a)=C_{H(B∪a)}(a)=H(B∪{a})` で summand 同一 ⟹ sign 相殺, survivor B={a}.
   ℬ↔𝒫 reindex (orbit weight [L:N_L(B)], `card_orbit_mul_card_setLStabilizer`),
   b↔a^L reindex (`induce_alphaB_conjFinset` (2.10.1)).
4. survivor `B={a}` 評価: `card_conj_fiber` (= |𝒜(g,H(a)a)|=|C_G(a)|) → γ(g)=α(a)=dadeValue α g.
   非-support side は `induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport` (= 進捗 (10)(b)) で即.

合計 ~150-230 LOC; 別 focused session 推奨.  infra は全て present (keystone (2.1) 取り込み済,
(2.10.1)/(2.10.2)/(2.9)/(2.10.3) [transversal+vanishing+value 集計形]/ℬ-transversal/bridge すべて
landed) — 残るは純粋に組合せ的集計 (involution + reindex + cardinality 翻訳) の組み上げのみ.

## 進捗 2026-05-30 (11) — (2.10.3) value case の support-restricted 形 (sorry-free, axiom-clean)

上記「残ブロッカー」**項目 1 (value case の a^L 特殊化) の前半 (support による台外項の脱落)** を landing.
`lake build OddOrder` + `OddOrder.AxiomsCheck` green, 新規 sorry/admit/axiom 無し (3 axioms 全 allowlist 内).

- **`induce_alphaB_apply_eq_sum_nLStabilizerIn_inA`** (`section PointwiseValue`) — α∈CF(L,A) (台 A) のとき
  `(Ind_{M(B)} α_B)(g) = ⅟|M(B)|·∑_{b∈N_L(B), b∈A} α(b)·|𝒜(g,H(B)·b)|`.  進捗 (10)(c) の
  `induce_alphaB_apply_eq_sum_nLStabilizerIn` (∑ over all N_L(B)) から, `(b:G)∉A ⟹ α(b)=0`
  (α の `SupportedClassFunctions.property`) で `Finset.sum_subset` により台外項を捨てるだけ.
  教科書 value 式 `(α(a)/|M(B)|)·∑_{b∈N_L(B)∩a^L}|𝒜(g,H(B)b)|` への第 1 還元
  (∑ 範囲を N_L(B) から N_L(B)∩A へ縮小; これが「`α(b)≠0 ⟹ b∈A`」段).

**残 (項目 1 の後半)**: support 代表 `a` (g∈(aH(a))^G) を固定し, 生き残った `b∈N_L(B)∩A` が
(2.4.b) `isConj_in_L_of_mul_H` で `b∈a^L` ((2.10.3) value case の `a^L` 制約) かつ α(b)=α(a) 定数化
する段 (`∑_{b∈N_L(B)∩A}` → `α(a)·∑_{b∈N_L(B)∩a^L}`).  以降は項目 2-4 (fiber 因子分解 + Möbius 相殺).

## 進捗 2026-05-30 (12) — STEP 1 (a^L 特殊化) + STEP 2 (fiber 因子分解) + cancellation identity 完成 (sorry-free, axiom-clean)

issue 0040 part (c) (Möbius) の **代数的 spine を全て landing** (6 commits;
`S04_DadeIsometry.lean` `section MobiusAssembly`; `lake build OddOrder` + `OddOrder.AxiomsCheck`
green, 新規 sorry/admit/axiom 無し).  残るは純粋に組合せ的な **STEP 3 (involution + ℬ→𝒫 reindex)
+ STEP 4 (FullDadeIsometryData 配線)** のみ.

### landed (依存順)

1. **survivor cardinality** `card_conjFiber_coset_eq_card_centralizer` (commit d7b10ef) —
   a が K を*中心化* (K⊆C_G(a)), C_G(a) が K を正規化, ⟨a⟩⊥K coprime, g~a·x₀ で
   `|𝒜(g,K·a)|=|C_G(a)|`.  (2.1) `card_conj_fiber` の pair set と全単射.
   survivor B={a} (H({a})=H(a)⊆C_G(a)) 評価用.
2. **conjugacy witness / support test** `exists_mem_H_isConj_of_mem_conjFiber_coset`
   (+ 系 `mem_dadeSupport_of_mem_conjFiber_coset`, commit d7b10ef/7893599) —
   `y⁻¹gy∈H(B)·b` (b∈N_L(B)∩A) ⇒ ∃c∈H(b), (b·c)~g.  vanishing/value case の核.
3. **STEP 1** `induce_alphaB_apply_eq_alpha_mul_sum_conjL` (commit 7893599) —
   g∈(aH(a))^G で `(Ind α_B)(g)=(α(a)/|M(B)|)·∑_{b∈N_L(B)∩a^L}|𝒜(g,H(B)b)|`.
   `_inA` 版から b∉a^L 項脱落 (項目 2 の conjugacy witness + (2.4.b)) + α(b)=α(a) 定数化.
4. **conjugation invariance** `card_conjFiber_conj_eq` (commit 2146af5) —
   `|𝒜(g,c·X·c⁻¹)|=|𝒜(g,X)|` (右 c-平行移動).  教科書 reindex
   `|𝒜(g,H(B^x)b)|=|𝒜(g,H(B)a)|` (b=a^x) 用.
5. **STEP 2 fiber 因子分解** `card_cosetConjFiber_eq_card_centralizerInf` (fiber count) +
   **`card_conjFiber_coset_mul_card_centralizerInf`** (commit fcb5d34) —
   `|𝒜(g,K·a)|·|C| = |𝒜(g,C·a)|·|K|` (C=K⊓C_G(a)).  bridge set
   `S={(y,c,x)|y⁻¹gy=x⁻¹(c·a)x}` を 2 通り (y へ射影 + fiber count |C| via
   `coset_eq_cosetConjImage`/`mem_centralizer_of_coset_conj_eq`; `(y,c,x)↦(yx⁻¹,c,x)` で x 自由化).
   **これが planner の「long pole」STEP 2 本体**.
6. **cancellation identity** `card_conjFiber_hIntersection_mul_eq` (commit c843e9d) —
   a∈N_L(B) で `|𝒜(g,H(B)·a)|·|H(B∪{a})| = |𝒜(g,H(B∪{a})·a)|·|H(B)|`.
   STEP 2 を K=H(B), C=C_{H(B)}(a)=H(B∪{a}) ((2.10.2)) に特殊化.  toggle-a 相殺の代数核.

### 残ブロッカー (precise): STEP 3 (組合せ assembly) + STEP 4 (配線) のみ

代数的事実 (全 cardinality 恒等式, value 公式, cancellation) は **すべて landed**.  残るは:

- **STEP 3a (ℬ→𝒫 orbit-weight reindex)**: bridge は整数係数 `c_B=-(-1)^|B|`, `s=ℬ` (transversal)
  を要求するので, 点別恒等式 `dadeMap α g = -∑_{B∈ℬ}(-1)^|B| Ind_{M(B)}α_B(g)` を直接評価する.
  教科書は ℬ-和を 𝒫-和 `-∑_{B∈𝒫}((-1)^|B|/[L:N_L(B)])Ind(g)` に変換 ((2.10.1) orbit 不変 +
  軌道重み `card_orbit_mul_card_setLStabilizer`).  Lean では `conjClassQuotient` 上の
  `Finset.univ` + `transversalRep` で ℬ-和を作り, orbit averaging
  (`∑_ℬ f = ∑_O f(rep) = ∑_𝒫 f/|O_B|`, f=induceAlphaBTerm は (2.10.1) `induceAlphaBTerm_conjFinset`
  で orbit 不変) で 𝒫-和へ.  **最大の構造的リスク** (quotient/Finset 操作 ~80-120 LOC).
- **STEP 3b (𝒫(b)/a^L 二重和 + involution)**: STEP 1 で各 Ind 値を `α(a)·∑_{b∈N_L(B)∩a^L}|𝒜(g,H(B)b)|`
  に, `card_conjFiber_conj_eq` で b↔a の reindex (|𝒜(g,H(B^x)b)|=|𝒜(g,H(B)a)|) し
  𝒫(a) 上の単和へ.  `Finset.sum_involution` toggle-a (B↔B∪{a}) で
  `card_conjFiber_hIntersection_mul_eq` (cancellation identity) により符号相殺, survivor B={a}.
  survivor は `card_conjFiber_coset_eq_card_centralizer` (=|C_G(a)|) + `card_centralizer_eq`
  (|C_G(a)|=|H(a)||C_L(a)|) で `γ(g)=α(a)`.  (~80-120 LOC)
- **STEP 4 (配線)**: 点別恒等式 → `preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum`
  → `PreservesVirtualCharacters (hyp.dadeMap)` → `FullDadeIsometryData` (`dadeIsometryData` +
  この preservation).  (~20-30 LOC)

合計 ~180-270 LOC, **純粋に組合せ的** (代数 primitive は全 present).  別 focused session 推奨.
non-support side (g∉dadeSupport) は `induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport` +
`dadeValue_of_not_mem_dadeSupport` で即 (恒等式の半分は landed 済).
