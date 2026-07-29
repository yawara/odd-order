# `exists_field_realization_K` の実装 draft (issue 0164, 2026-07-29 セッション末に退避)

> **状態: 未ビルド draft**。leaf を green に保つため `HilbertNinetyOnQ.lean` から
> 剥がして退避した。次セッションはここから再開する。

## 位置づけ

issue 0164 の残ギャップ (case (3) / PSL 分岐 / `p ∣ q₀−1`) を閉じる最後の配線。
engine は **landing 済**:

* `OddOrder.GroupTheory.exists_ne_one_fixed_of_free_orbit_semilinear`
  (`GroupTheory/SemilinearOrbitFixedPoint.lean`) — 自由軌道上の Hilbert 90。
  必要な入力は `μ : K ≃* Fˣ` と非自明な体自己同型 `σ` で `μ ∘ α = σ ∘ μ`。

この draft はその `(F, μ, σ)` を **`Q₀` から取り出す**部分。
`K` は `Q₀` (基本可換, 位数 `q`) 上 fpf で `|K| = q−1` ⟹ `Q₀∖{1}` 上推移的 ⟹ 既約
⟹ Appendix I Prop 2 (`exists_field_semilinear_with_scalar`) が `F` (`|F| = q`) と
スカラー `μ₀ : K →* Fˣ` を与える。`μ₀` は単射 (fpf) かつ `|K| = q−1 = |Fˣ|` ⟹ 全単射。
`x ∈ V` による共役は `σ`-半線形で `μ ∘ α = σ ∘ μ`、`σ ≠ 1` は `W = C_V(K) = ⊥` から。

## 既知の未解決点

* 宣言の型に `Type uG` を使っているが `HilbertNinetyOnQ.lean` は
  `universe uG` を宣言していない (`{G Ω : Type*}`)。`universe uG uΩ` を足して
  `variable {G : Type uG} {Ω : Type uΩ}` にするか、別 leaf に置く。
* `letI : CommGroup ↥hyp.K := IsCyclic.commGroup` の下で作った `μ : ↥hyp.K ≃* Fˣ` を
  canonical な `Group ↥hyp.K` の下の型として返せるか (defeq のはずだが未検証)。
* `Nat.bijective_iff_injective_and_card` の名前・形は未検証。
* `hcompat` の `change` 中の `x⁻¹⁻¹` の扱いは未検証。

## 残りの手順 (draft が通った後)

1. `HilbertNinetyOnQ.lean` に `exists_mem_inf_centralizer_not_mem_Q0_of_orbit` を追加:
   `M := ↥Q ⧸ Z(↥Q)` (位数 `q²`) に engine を当て、`C_M(X) ≠ 1` を得て
   coprime 持ち上げ (既存の `exists_mem_inf_centralizer_not_mem_Q0` の後半と同じ) で
   `C_Q(X) ⊄ Q₀`。`hnd` は `(q²−1)/(q−1) = q+1` と `¬ p ∣ q+1`。
2. `WNeBot.lean` の case 2 をこれに差し替え ⟹
   `exists_kSubgroupSquare_invariant_of_card_cube` の type B sorry が**不要になり削除**。
3. `Trichotomy.lean` の `trichotomy` から `hWcube` を除去して
   `W_ne_bot_of_card_cube` を配線 ⟹ issue 0163 へ。

## draft 本体

```lean
/-- **The field realization of `K`, with the twist induced by an element of `V`.**

Peterfalvi Part II, Ch. I §2 (Propositions 2 and 3) in the form Appendix I,
Proposition 2 delivers it: `K` acts on the elementary abelian `Q₀` freely
(Ch. I §2 Proposition 1(a)) and `|K| = |Q₀| − 1`, so the action is transitive on
`Q₀ ∖ {1}` and in particular irreducible.  Hence `Q₀` is a line over a field `F`
with `|F| = |Q₀|` on which `K` acts by scalars — and `μ : K → Fˣ` is then a
bijection, since both sides have `|Q₀| − 1` elements.

Conjugation by `x ∈ V` normalizes `K` (`K ⊴ D`) and acts `σ`-semilinearly on
`Q₀`, and the two are related by `μ ∘ α = σ ∘ μ`.  The twist `σ` is non-trivial
exactly because `W = C_V(K) = 1`: an `x` centralizing `K` would lie in `W`. -/
theorem exists_field_realization_K (hW : hyp.W = ⊥)
    {x : G} (hxV : x ∈ hyp.V) (hxne : x ≠ 1)
    (α : ↥hyp.K ≃* ↥hyp.K)
    (hα : ∀ k : ↥hyp.K, ((α k : ↥hyp.K) : G) = x * (k : G) * x⁻¹) :
    ∃ (F : Type uG) (_ : Field F) (_ : Finite F)
      (μ : ↥hyp.K ≃* Fˣ) (σ : RingAut F), σ ≠ 1 ∧
        Nat.card F = Nat.card ↥hyp.Q0 ∧
        ∀ k : ↥hyp.K, ((μ (α k) : Fˣ) : F) = σ ((μ k : Fˣ) : F) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
  have hxD : x ∈ hyp.D := hyp.V_le_D hxV
  -- the conjugation action of `K` on `Q₀`
  set ψ₀ : ↥hyp.K →* MulAut ↥hyp.Q0 :=
    hyp.conjQ0.comp (Subgroup.inclusion hyp.K_le_D) with hψ₀def
  have hψ₀val : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0),
      ((ψ₀ k y : ↥hyp.Q0) : G) = (k : G) * (y : G) * (k : G)⁻¹ := fun _ _ => rfl
  -- `K` acts freely off the identity (Ch. I §2 Proposition 1(a))
  have hfree : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0), y ≠ 1 → ψ₀ k y = y → k = 1 := by
    intro k y hy hfix
    by_contra hk
    have hkKSet : (k : G) ∈ hyp.KSet := by rw [← SetLike.mem_coe, hyp.coe_K]; exact k.2
    have hk1 : (k : G) ≠ 1 := fun h => hk (Subtype.ext h)
    have hval : (k : G) * (y : G) * (k : G)⁻¹ = (y : G) := by
      rw [← hψ₀val k y, hfix]
    have hmem : (y : G) ∈ hyp.Q ⊓ Subgroup.centralizer ({(k : G)} : Set G) := by
      refine ⟨hyp.Q0_le_Q y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (y : G) * (k : G) = ((k : G) * (y : G) * (k : G)⁻¹) * (k : G) := by rw [hval]
        _ = (k : G) * (y : G) := by group
    rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet hkKSet hk1, Subgroup.mem_bot] at hmem
    exact hy (Subtype.ext hmem)
  -- irreducibility, from freeness and `|K| = |Q₀| − 1`
  have hKcard : Nat.card ↥hyp.K = Nat.card ↥hyp.Q0 - 1 := hyp.card_K_eq_card_Q0_sub_one
  have hQ0two : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  have hirr : ∀ B : Subgroup ↥hyp.Q0, IsAInvariant ψ₀ B → B = ⊥ ∨ B = ⊤ := by
    intro B hB
    by_cases hBbot : B = ⊥
    · exact Or.inl hBbot
    right
    obtain ⟨b, hbB, hb1⟩ : ∃ b : ↥hyp.Q0, b ∈ B ∧ b ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hBbot (le_bot_iff.mp fun y hy => Subgroup.mem_bot.mpr (hcon y hy))
    have hbne : ∀ k : ↥hyp.K, ψ₀ k b ≠ 1 := by
      intro k h
      exact hb1 (by simpa using congrArg (ψ₀ k)⁻¹ h)
    set f : Option ↥hyp.K → ↥B := fun o =>
      o.rec (⟨1, B.one_mem⟩) (fun k => ⟨ψ₀ k b, hB.smul_mem k hbB⟩) with hfdef
    have hfinj : Function.Injective f := by
      rintro (_ | k) (_ | l) h
      · rfl
      · exact absurd (congrArg (Subtype.val (p := fun z => z ∈ B)) h).symm (hbne l)
      · exact absurd (congrArg (Subtype.val (p := fun z => z ∈ B)) h) (hbne k)
      · have hval : ψ₀ k b = ψ₀ l b := congrArg (Subtype.val (p := fun z => z ∈ B)) h
        have hfix : ψ₀ (l⁻¹ * k) b = b := by
          rw [map_mul, map_inv]
          change (ψ₀ l)⁻¹ ((ψ₀ k) b) = b
          rw [hval]
          simp
        exact congrArg some (by
          have h2 : l⁻¹ * k = 1 := hfree _ b hb1 hfix
          exact (inv_mul_eq_one.mp h2).symm)
    have hcard : Nat.card ↥hyp.K + 1 ≤ Nat.card ↥B := by
      have := Nat.card_le_card_of_injective f hfinj
      rwa [Finite.card_option] at this
    have hBle : Nat.card ↥B ≤ Nat.card ↥hyp.Q0 := Subgroup.card_le_card_group B
    refine Subgroup.eq_top_of_card_eq B ?_
    omega
  -- Appendix I, Proposition 2
  obtain ⟨F, instF, instMod, instFin, -, hcardF, ⟨μ₀, hμ₀⟩, hsemi⟩ :=
    Huppert.exists_field_semilinear_with_scalar hyp.isElementaryAbelian_Q0 ψ₀ hirr
  letI : Field F := instF
  letI : Module F (Additive ↥hyp.Q0) := instMod
  letI : Finite F := instFin
  have hμ₀' : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0), ((μ₀ k : Fˣ) : F) • (Additive.ofMul y)
      = Additive.ofMul (ψ₀ k y) := fun k y => hμ₀ k (Additive.ofMul y)
  -- `μ₀` is injective, hence bijective
  have hμinj : Function.Injective μ₀ := by
    refine (injective_iff_map_eq_one μ₀).mpr fun k hk1 => ?_
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥hyp.Q0)
    refine hfree k y hy ?_
    have h := hμ₀' k y
    rw [hk1, Units.val_one, one_smul] at h
    exact (Additive.ofMul.injective h).symm
  have hunits : Nat.card Fˣ = Nat.card ↥hyp.Q0 - 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcardF]
  have hμbij : Function.Bijective μ₀ := by
    refine ⟨hμinj, ?_⟩
    have hcards : Nat.card ↥hyp.K = Nat.card Fˣ := by rw [hKcard, hunits]
    exact (Nat.bijective_iff_injective_and_card μ₀).mpr ⟨hμinj, hcards⟩ |>.2
  set μ : ↥hyp.K ≃* Fˣ := MulEquiv.ofBijective μ₀ hμbij with hμdef
  have hμval : ∀ k : ↥hyp.K, (μ k : Fˣ) = μ₀ k := fun _ => rfl
  -- the twist
  have hcompat : ∀ k : ↥hyp.K,
      ψ₀ (α k) = hyp.conjQ0 ⟨x, hxD⟩ * ψ₀ k * (hyp.conjQ0 ⟨x, hxD⟩)⁻¹ := by
    intro k
    ext y
    apply Subtype.ext
    rw [hψ₀val]
    change (α k : G) * (y : G) * ((α k : G))⁻¹ =
      x * ((k : G) * (x⁻¹ * (y : G) * x⁻¹⁻¹) * (k : G)⁻¹) * x⁻¹
    rw [hα k]
    group
  obtain ⟨σ, hσ⟩ := hsemi (hyp.conjQ0 ⟨x, hxD⟩) α hcompat
  -- `μ ∘ α = σ ∘ μ`
  obtain ⟨y₀, hy₀⟩ := exists_ne (1 : ↥hyp.Q0)
  have he₀ : (Additive.ofMul y₀ : Additive ↥hyp.Q0) ≠ 0 := fun h =>
    hy₀ (by simpa using congrArg Additive.toMul h)
  have hinjsmul : Function.Injective
      (fun a : F => a • (Additive.ofMul y₀ : Additive ↥hyp.Q0)) :=
    smul_left_injective F he₀
  set g₀ : MulAut ↥hyp.Q0 := hyp.conjQ0 ⟨x, hxD⟩ with hg₀def
  have hμσ : ∀ k : ↥hyp.K, ((μ (α k) : Fˣ) : F) = σ ((μ k : Fˣ) : F) := by
    intro k
    refine hinjsmul ?_
    have hlhs : ((μ (α k) : Fˣ) : F) • (Additive.ofMul y₀ : Additive ↥hyp.Q0)
        = Additive.ofMul (g₀ (ψ₀ k (g₀⁻¹ y₀))) := by
      rw [hμval, hμ₀' (α k) y₀, hcompat k]
      rfl
    have hrhs : (σ ((μ k : Fˣ) : F)) • (Additive.ofMul y₀ : Additive ↥hyp.Q0)
        = Additive.ofMul (g₀ (ψ₀ k (g₀⁻¹ y₀))) := by
      have h1 := hσ ((μ k : Fˣ) : F) (Additive.ofMul (g₀⁻¹ y₀))
      have h2 : (MulEquiv.toAdditive g₀) (Additive.ofMul (g₀⁻¹ y₀))
          = (Additive.ofMul y₀ : Additive ↥hyp.Q0) := by
        change Additive.ofMul (g₀ (g₀⁻¹ y₀)) = Additive.ofMul y₀
        rw [MulAut.apply_inv_self]
      rw [hμval, hμ₀' k (g₀⁻¹ y₀), h2] at h1
      exact h1.symm
    exact hlhs.trans hrhs.symm
  -- non-triviality of the twist: `x` does not centralize `K`, since `W = 1`
  have hσne : σ ≠ 1 := by
    intro h1
    obtain ⟨k₀, hk₀K, hk₀ne⟩ : ∃ k ∈ hyp.K, x * k * x⁻¹ ≠ k := by
      by_contra hcon
      push Not at hcon
      have hxW : x ∈ hyp.W := by
        refine ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have hkK : k ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk
        have h := hcon k hkK
        calc k * x = (x * k * x⁻¹) * x := by rw [h]
          _ = x * k := by group
      rw [hW, Subgroup.mem_bot] at hxW
      exact hxne hxW
    refine hk₀ne ?_
    have h2 : μ (α ⟨k₀, hk₀K⟩) = μ (⟨k₀, hk₀K⟩ : ↥hyp.K) := by
      refine Units.ext ?_
      rw [hμσ ⟨k₀, hk₀K⟩, h1]
      rfl
    have h3 : α (⟨k₀, hk₀K⟩ : ↥hyp.K) = ⟨k₀, hk₀K⟩ := μ.injective h2
    have h4 := hα (⟨k₀, hk₀K⟩ : ↥hyp.K)
    rw [h3] at h4
    exact h4.symm
  exact ⟨F, instF, instFin, μ, σ, hσne, hcardF, hμσ⟩

```
