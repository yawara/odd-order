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
