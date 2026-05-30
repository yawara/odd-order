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
- [ ] 誘導指標値公式: `induce_apply` (既存) で足りる見込み; 集計は (2.10.3) 内
- [ ] (2.10.1) Ind L-共役不変 / (2.10.3) Ind 点別値
- [ ] (2.10) inclusion-exclusion 本体 (Möbius 相殺) — **(2.6.b) 専用、現フロンティア**
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
