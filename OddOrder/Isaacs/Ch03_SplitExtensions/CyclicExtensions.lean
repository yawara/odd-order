/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315
import OddOrder.Mathlib.SemidirectProduct

/-!
# Isaacs §3F: cyclic quotient extensions (pp. 105-112)

Thm 3.35 (extension uniqueness) と Thm 3.36 (cyclic extension existence,
`(N ⋊_σ ℤ)/⟨(a⁻¹, m)⟩` 構成) のクラスタ. `Main.lean` (issue 0103 の tail hub) から
2026-07-17 に分割 (Main が 1500 行に接近したため; 下流は Main を import して不変).
-/

namespace OddOrder.Isaacs.Ch03

section /- 3F: 巡回商 lift (pp. 105-112) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3F (Cyclic quotient lift)

3.35-3.36: `H ⊴ G` で `G/H` 巡回 (位数 n) のとき, `H ≤ K ≤ G` で `G = HK` かつ
`|K/H| = n` となる `K` が存在 (3.35 lift, 3.36 specialization).

FT 経路では優先度低 (Peterfalvi で散発使用).

**形式化状態**: stub. 全 lifted 結果は SemidirectProduct (mathlib) との接続で得られる
可能性が高い. -/

/-- **Isaacs Thm 3.35 (cyclic lift; generator)**: `H ⊴ G`, `G/H` cyclic ⇒ ある `g ∈ G` が
`G/H` の生成元の lift で, `⟨g⟩ ⊔ H = G`. (Thm 3.35 強版の uniqueness の前提.) -/
theorem cyclic_quotient_lift [Finite G] {H : Subgroup G} [H.Normal]
    (hCyclic : IsCyclic (G ⧸ H)) :
    ∃ g : G, Subgroup.zpowers g ⊔ H = ⊤ := by
  obtain ⟨gbar, hgbar⟩ := hCyclic.exists_generator
  -- gbar : G ⧸ H, hgbar : ∀ x, x ∈ Subgroup.zpowers gbar.
  -- Lift to g ∈ G.
  obtain ⟨g, hg_proj⟩ := QuotientGroup.mk_surjective gbar
  refine ⟨g, ?_⟩
  rw [eq_top_iff]
  intro x _
  -- ⟦x⟧ ∈ ⟨gbar⟩, so ⟦x⟧ = gbar^n for some n. So x = g^n · h for some h ∈ H.
  have hx : (x : G ⧸ H) ∈ Subgroup.zpowers gbar := hgbar _
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, hn⟩ := hx
  -- hn : gbar ^ n = (x : G ⧸ H). Substituting gbar = ⟦g⟧: ⟦g⟧^n = ⟦g^n⟧ = ⟦x⟧.
  have h_in_H : x * (g ^ n)⁻¹ ∈ H := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← hg_proj] at hn
    -- hn : (↑g : G ⧸ H) ^ n = ↑x
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, ← hn]
    group
  -- x = (x · (g^n)⁻¹) · g^n with first factor in H and second in ⟨g⟩.
  rw [show x = (x * (g ^ n)⁻¹) * g ^ n by group, sup_comm]
  exact Subgroup.mul_mem_sup h_in_H (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n)

/-- **Isaacs Thm 3.35 (uniqueness)** ⭐: `N ⊴ G` で `gN` が `G/N` の生成元のとき,
`G →* G₀` の準同型は `N` 上での値と `g ↦ g₀` から **一意に決定**.

Isaacs §3F の主結果 (extension uniqueness). 任意 `u ∈ G` は `u = (u·(g^i)⁻¹) · g^i` の
形に一意分解 (`u·(g^i)⁻¹ ∈ N`, `i` は `gN` の zpowers での representation).
両 θ, θ' が同じ extension を与えるなら値が一致.

**注**: existence (Thm 3.36 cyclic extension) は別途 (Sym(Ω) realization), Phase 4 予定. -/
theorem cyclic_quotient_extension_unique
    {G G₀ : Type*} [Group G] [Group G₀]
    {N : Subgroup G} [N.Normal]
    (g : G) (g₀ : G₀)
    (hg_gen : Subgroup.zpowers ((g : G ⧸ N)) = ⊤)
    {θ θ' : G →* G₀}
    (hθ_ext : ∀ x ∈ N, θ x = θ' x) (hθ_g : θ g = g₀) (hθ'_g : θ' g = g₀) :
    θ = θ' := by
  ext u
  -- ⟦u⟧ ∈ ⟨⟦g⟧⟩, so ⟦u⟧ = ⟦g⟧^i for some i ∈ ℤ.
  have hu_mem : (u : G ⧸ N) ∈ Subgroup.zpowers ((g : G ⧸ N)) := hg_gen ▸ Subgroup.mem_top _
  rw [Subgroup.mem_zpowers_iff] at hu_mem
  obtain ⟨i, hi⟩ := hu_mem
  -- hi : (↑g)^i = ↑u in G ⧸ N, i.e., x := u * (g^i)⁻¹ ∈ N.
  set x : G := u * (g^i)⁻¹ with hxdef
  have hx_mem : x ∈ N := by
    rw [hxdef, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow, ← hi]
    group
  -- u = x * g^i.
  have hu_decomp : u = x * g^i := by rw [hxdef]; group
  rw [hu_decomp, map_mul θ, map_mul θ', map_zpow θ, map_zpow θ', hθ_g, hθ'_g, hθ_ext _ hx_mem]

/-! ### Isaacs Thm 3.36 (cyclic extension existence)

`N` 群, `m > 0`, `a ∈ N`, `σ ∈ Aut(N)` で `σ a = a` かつ `σ^m = MulAut.conj a` を満たすとき,
`N ⊴ G` で `G/N` cyclic of order `m`, generator `g` で `g^m = a` かつ `x^g = σ x`
となる群 `G` が存在.

構成: `preG := N ⋊_σ (Multiplicative ℤ)` を quotient by `K := ⟨(a⁻¹, m)⟩`.
`hσa, hσm` から `(a⁻¹, m)` が `preG` の中心元 ⇒ `K ⊴ preG`. 各性質は商計算. -/
/-- Twist hom: `Multiplicative ℤ →* MulAut N` sending `ofAdd k ↦ σ^k`. -/
private noncomputable def cyclicExtPhi {N : Type*} [Group N] (σ : MulAut N) :
    Multiplicative ℤ →* MulAut N :=
  zpowersHom (MulAut N) σ

@[simp] private lemma cyclicExtPhi_apply {N : Type*} [Group N] (σ : MulAut N)
    (k : Multiplicative ℤ) : cyclicExtPhi σ k = σ ^ k.toAdd := rfl

/-- The pre-quotient group `N ⋊_σ ℤ`. -/
private abbrev CyclicExtPreG (N : Type*) [Group N] (σ : MulAut N) : Type _ :=
  SemidirectProduct N (Multiplicative ℤ) (cyclicExtPhi σ)

/-- The "central" element `(a⁻¹, m)` in `preG`. -/
private noncomputable def cyclicExtK {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N) : CyclicExtPreG N σ :=
  SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))

/-- Under `hσa` and `hσm`, the element `(a⁻¹, m)` is fixed by conjugation. -/
private lemma cyclicExtK_centralized {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N)
    (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    ∀ y : CyclicExtPreG N σ, y * cyclicExtK m a σ * y⁻¹ = cyclicExtK m a σ := by
  intro y
  -- σ^k fixes a (and a⁻¹) for any k : ℤ (since σ ∈ stabilizer a).
  have hσka : ∀ k : ℤ, (σ ^ k) a = a := fun k =>
    (Subgroup.zpow_mem (MulAction.stabilizer (MulAut N) a)
      (MulAction.mem_stabilizer_iff.mpr hσa) k : _)
  have hσka_inv : ∀ k : ℤ, (σ ^ k) a⁻¹ = a⁻¹ := fun k => by rw [map_inv, hσka k]
  -- σ^m sends x to a * x * a⁻¹ (from hσm).
  have hσm_apply : ∀ x : N, ((σ ^ m : MulAut N)) x = a * x * a⁻¹ := fun x => by
    rw [hσm]; rfl
  -- (cyclicExtK).left = a⁻¹, .right = ofAdd m.
  have h_K_left : (cyclicExtK m a σ).left = a⁻¹ := by
    change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).left = _
    simp [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
          SemidirectProduct.left_inr]
  have h_K_right : (cyclicExtK m a σ).right = Multiplicative.ofAdd (m : ℤ) := by
    change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).right = _
    simp [SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr]
  ext
  · -- Left component.
    change ((y * cyclicExtK m a σ) * y⁻¹).left = (cyclicExtK m a σ).left
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
               SemidirectProduct.inv_left,
               h_K_left, h_K_right, cyclicExtPhi_apply]
    -- Goal (approx): y.left * (σ^l.toAdd) a⁻¹ * (σ^(l.toAdd+m)) ((σ^(-l.toAdd)) y.left⁻¹) = a⁻¹.
    rw [hσka_inv]
    -- Compose σ chain.
    have hcompose : (σ ^ ((y.right * Multiplicative.ofAdd (m : ℤ)).toAdd))
        ((σ ^ ((y.right⁻¹ : Multiplicative ℤ).toAdd)) y.left⁻¹) =
          ((σ : MulAut N) ^ m) y.left⁻¹ := by
      change (σ ^ ((y.right.toAdd + (m : ℤ)) : ℤ))
            ((σ ^ ((-y.right.toAdd) : ℤ)) y.left⁻¹) = _
      rw [← MulAut.mul_apply, ← zpow_add,
          show (y.right.toAdd + (m : ℤ)) + (-y.right.toAdd) = (m : ℤ) by ring,
          zpow_natCast]
    rw [hcompose, hσm_apply]
    group
  · -- Right component (Multiplicative ℤ abelian).
    change ((y * cyclicExtK m a σ) * y⁻¹).right = (cyclicExtK m a σ).right
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    rw [mul_comm y.right _, mul_assoc, mul_inv_cancel, mul_one]

/-- The kernel subgroup `K = ⟨(a⁻¹, m)⟩`. -/
private noncomputable abbrev cyclicExtKSubgroup {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N) : Subgroup (CyclicExtPreG N σ) :=
  Subgroup.zpowers (cyclicExtK m a σ)

private lemma cyclicExtKSubgroup_normal {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N)
    (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    (cyclicExtKSubgroup m a σ).Normal := by
  refine ⟨fun n hn y => ?_⟩
  rw [Subgroup.mem_zpowers_iff] at hn
  obtain ⟨j, hj⟩ := hn
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [← hj]
  have h_conj_zpow : y * (cyclicExtK m a σ)^j * y⁻¹ = (y * cyclicExtK m a σ * y⁻¹)^j := by
    have h : (MulAut.conj y) ((cyclicExtK m a σ)^j) = ((MulAut.conj y) (cyclicExtK m a σ))^j :=
      map_zpow (MulAut.conj y) _ _
    simpa only [MulAut.conj_apply] using h
  rw [h_conj_zpow, cyclicExtK_centralized m a σ hσa hσm]

/-- **Isaacs Thm 3.36 (cyclic extension existence)** ⭐:
given `N`, `m > 0`, `a ∈ N`, `σ ∈ Aut(N)` with `σ a = a` and `σ^m = MulAut.conj a`,
there exists a group `G` with `N ⊴ G` (via iso `ι`), `G/N` cyclic **of order exactly `m`**
(clauses `zpowers ḡ = ⊤` and `Nat.card (G ⧸ N₀) = m`), generator `g`,
`g^m = ι a` and `g · ι x · g⁻¹ = ι (σ x)`.

Construction: `G := (N ⋊_σ ℤ) / ⟨(a⁻¹, m)⟩`. The element `(a⁻¹, m)` is central (proven in
`cyclicExtK_centralized` using `σ a = a` and `σ^m = MulAut.conj a`), so its zpowers form
a normal subgroup. Quotienting gives `G` with the desired cyclic-extension structure. -/
theorem cyclic_extension_exists.{u} {N : Type u} [Group N] {m : ℕ} (_hm : 0 < m)
    (a : N) (σ : MulAut N) (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    ∃ (G : Type u) (_ : Group G) (N₀ : Subgroup G) (_ : N₀.Normal)
      (ι : N ≃* ↥N₀) (g : G),
      Subgroup.zpowers ((g : G ⧸ N₀)) = ⊤ ∧
      Nat.card (G ⧸ N₀) = m ∧
      g ^ m = (ι a : G) ∧
      ∀ x : N, g * (ι x : G) * g⁻¹ = (ι (σ x) : G) := by
  haveI hK_norm : (cyclicExtKSubgroup m a σ).Normal :=
    cyclicExtKSubgroup_normal m a σ hσa hσm
  -- G := preG ⧸ K with the natural Group instance.
  let G := CyclicExtPreG N σ ⧸ cyclicExtKSubgroup m a σ
  -- inl_to_G : N →* G via inl then quotient.
  let inl_to_G : N →* G :=
    (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)).comp SemidirectProduct.inl
  -- inl_to_G is injective: ker = inl⁻¹(K) = ⊥.
  have h_inj : Function.Injective inl_to_G := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h_in_K : (SemidirectProduct.inl x : CyclicExtPreG N σ) ∈ cyclicExtKSubgroup m a σ := by
      have heq : inl_to_G x = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
          (SemidirectProduct.inl x) := rfl
      rw [heq] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_zpowers_iff] at h_in_K
    obtain ⟨j, hj⟩ := h_in_K
    have h_K_right : (cyclicExtK m a σ).right = Multiplicative.ofAdd (m : ℤ) := by
      change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).right = _
      simp
    have h_jm_eq_zero : (j • (m : ℤ)) = 0 := by
      have h_right_of_inl : (SemidirectProduct.inl x : CyclicExtPreG N σ).right = 1 :=
        SemidirectProduct.right_inl x
      have h_zpow_right : ((cyclicExtK m a σ) ^ j : CyclicExtPreG N σ).right =
          (Multiplicative.ofAdd (m : ℤ)) ^ j := by
        have hmap : SemidirectProduct.rightHom ((cyclicExtK m a σ) ^ j) =
            SemidirectProduct.rightHom (cyclicExtK m a σ) ^ j := map_zpow _ _ _
        change SemidirectProduct.rightHom ((cyclicExtK m a σ) ^ j) = _
        rw [hmap]; congr 1
      have h_one : ((cyclicExtK m a σ) ^ j : CyclicExtPreG N σ).right = 1 := by
        rw [hj]; exact h_right_of_inl
      rw [h_zpow_right] at h_one
      rw [← ofAdd_zsmul, ofAdd_eq_one] at h_one
      exact h_one
    have hj_zero : j = 0 := by
      rw [smul_eq_mul] at h_jm_eq_zero
      rcases mul_eq_zero.mp h_jm_eq_zero with h | h
      · exact h
      · exfalso
        have hm_pos : (m : ℤ) > 0 := Int.natCast_pos.mpr _hm
        exact (ne_of_gt hm_pos) h
    subst hj_zero
    rw [zpow_zero] at hj
    have h_inl_one : (SemidirectProduct.inl x : CyclicExtPreG N σ) = 1 := hj.symm
    have : SemidirectProduct.inl x = (SemidirectProduct.inl (1 : N) : CyclicExtPreG N σ) := by
      rw [(SemidirectProduct.inl : N →* CyclicExtPreG N σ).map_one]; exact h_inl_one
    exact SemidirectProduct.inl_injective this
  -- N₀ := range of inl_to_G.
  let N₀ : Subgroup G := inl_to_G.range
  haveI hN₀_norm : N₀.Normal := by
    have h_range_eq : (inl_to_G.range : Subgroup G) =
        (SemidirectProduct.inl : N →* CyclicExtPreG N σ).range.map
          (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)) :=
      MonoidHom.range_comp _ _
    change N₀.Normal
    rw [show N₀ = inl_to_G.range from rfl, h_range_eq]
    have h_inl_range_normal :
        (SemidirectProduct.inl : N →* CyclicExtPreG N σ).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact (SemidirectProduct.rightHom : CyclicExtPreG N σ →* Multiplicative ℤ).normal_ker
    exact h_inl_range_normal.map _ (QuotientGroup.mk'_surjective _)
  -- ι := N ≃* N₀.
  let ι : N ≃* ↥N₀ := MonoidHom.ofInjective h_inj
  -- g := ⟦inr (ofAdd 1)⟧.
  let g : G := QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))
  have hz : Subgroup.zpowers ((g : G ⧸ N₀)) = ⊤ := by
    -- every G/N₀ element lifts to preG, decompose y = inl·inr;
    -- inl part vanishes in G/N₀, inr part is ⟦g⟧^(y.right.toAdd).
    rw [Subgroup.eq_top_iff']
    intro z
    obtain ⟨zG, rfl⟩ : ∃ zG : G, QuotientGroup.mk' N₀ zG = z :=
      QuotientGroup.mk'_surjective _ z
    obtain ⟨y, rfl⟩ : ∃ y : CyclicExtPreG N σ,
        QuotientGroup.mk' (cyclicExtKSubgroup m a σ) y = zG :=
      QuotientGroup.mk'_surjective _ zG
    rw [show y = SemidirectProduct.inl y.left * SemidirectProduct.inr y.right from
      (SemidirectProduct.inl_left_mul_inr_right y).symm,
      map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
      map_mul (QuotientGroup.mk' N₀)]
    have h_in_N₀ : (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl y.left)) ∈ N₀ := ⟨y.left, rfl⟩
    have h_first_one : (QuotientGroup.mk' N₀ : G →* G ⧸ N₀)
        ((QuotientGroup.mk' (cyclicExtKSubgroup m a σ)) (SemidirectProduct.inl y.left)) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact h_in_N₀
    rw [h_first_one, one_mul]
    have h_right_eq : y.right = (Multiplicative.ofAdd (1 : ℤ)) ^ y.right.toAdd := by
      conv_lhs => rw [← ofAdd_toAdd y.right]
      rw [← ofAdd_zsmul]; congr 1; simp
    rw [h_right_eq, map_zpow (SemidirectProduct.inr : Multiplicative ℤ →* CyclicExtPreG N σ),
      map_zpow (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
      map_zpow (QuotientGroup.mk' N₀)]
    exact Subgroup.zpow_mem_zpowers _ _
  have hgm : g ^ m = (ι a : G) := by
    -- g^m = mk' K (inr (ofAdd m)). (ι a : G) = mk' K (inl a).
    -- (inr (ofAdd m))⁻¹ * inl a = (a, ofAdd(-m)) = cExt⁻¹ ∈ K (using σ^k a = a ∀ k).
    have h_iota_a : (ι a : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl a) := rfl
    rw [h_iota_a]
    have h_g_pow : (g ^ m : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))) := by
      change (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))) ^ m = _
      rw [← map_pow]; congr 1
      rw [← map_pow]; congr 1
      rw [← ofAdd_nsmul]; congr 1; simp
    rw [h_g_pow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hσa_zpow : ∀ k : ℤ, (σ ^ k) a = a := fun k =>
      Subgroup.zpow_mem (MulAction.stabilizer (MulAut N) a)
        (MulAction.mem_stabilizer_iff.mpr hσa) k
    have h_eq_inv : (SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))
        : CyclicExtPreG N σ)⁻¹ * SemidirectProduct.inl a = (cyclicExtK m a σ)⁻¹ := by
      apply SemidirectProduct.ext
      · change ((SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ)))⁻¹ *
            SemidirectProduct.inl a : CyclicExtPreG N σ).left = (cyclicExtK m a σ)⁻¹.left
        unfold cyclicExtK
        simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
          SemidirectProduct.inv_right, cyclicExtPhi_apply]
      · change ((SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ)))⁻¹ *
            SemidirectProduct.inl a : CyclicExtPreG N σ).right = (cyclicExtK m a σ)⁻¹.right
        unfold cyclicExtK
        simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
          SemidirectProduct.right_inl, SemidirectProduct.right_inr, one_mul, mul_one]
    rw [h_eq_inv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  refine ⟨G, inferInstance, N₀, hN₀_norm, ι, g, hz, ?_, hgm, ?_⟩
  · -- |G/N₀| = m: ḡ の位数が m (両側整除) で, zpowers ḡ = ⊤ と Nat.card_zpowers.
    have hgbar_pow_m : ((g : G ⧸ N₀)) ^ m = 1 := by
      have h1 : ((g : G ⧸ N₀)) ^ m = ((g ^ m : G) : G ⧸ N₀) := by
        rw [← QuotientGroup.mk'_apply, ← map_pow, QuotientGroup.mk'_apply]
      rw [h1, hgm, QuotientGroup.eq_one_iff]
      exact SetLike.coe_mem (ι a)
    have hdvd_m : orderOf ((g : G ⧸ N₀)) ∣ m := orderOf_dvd_of_pow_eq_one hgbar_pow_m
    have h_ord_ne : orderOf ((g : G ⧸ N₀)) ≠ 0 := by
      intro h0
      rw [h0] at hdvd_m
      exact Nat.pos_iff_ne_zero.mp _hm (Nat.eq_zero_of_zero_dvd hdvd_m)
    have hm_dvd : m ∣ orderOf ((g : G ⧸ N₀)) := by
      -- ḡ^k = 1 → g^k ∈ N₀ → inr(ofAdd k) ≡_K inl x → 右成分比較で m ∣ k.
      have hk := pow_orderOf_eq_one ((g : G ⧸ N₀))
      set k : ℕ := orderOf ((g : G ⧸ N₀)) with hk_def
      have h1 : ((g ^ k : G) : G ⧸ N₀) = 1 := by
        rw [← QuotientGroup.mk'_apply, map_pow, QuotientGroup.mk'_apply]
        exact hk
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨x, hx⟩ := h1
      have h_g_pow_k : (g ^ k : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
          (SemidirectProduct.inr (Multiplicative.ofAdd (k : ℤ))) := by
        change (QuotientGroup.mk' _
          (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))) ^ k = _
        rw [← map_pow]; congr 1
        rw [← map_pow]; congr 1
        rw [← ofAdd_nsmul]; congr 1; simp
      have hx' : QuotientGroup.mk' (cyclicExtKSubgroup m a σ) (SemidirectProduct.inl x) =
          QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
            (SemidirectProduct.inr (Multiplicative.ofAdd (k : ℤ))) := by
        rw [← h_g_pow_k]; exact hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hx'
      rw [Subgroup.mem_zpowers_iff] at hx'
      obtain ⟨j, hj⟩ := hx'
      -- 右成分: ofAdd k = ofAdd (j * m).
      have h_right := congrArg
        (SemidirectProduct.rightHom : CyclicExtPreG N σ →* Multiplicative ℤ) hj
      have h_K_right : SemidirectProduct.rightHom (cyclicExtK m a σ) =
          Multiplicative.ofAdd (m : ℤ) := by
        change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _ :
          CyclicExtPreG N σ).right = _
        simp
      rw [map_zpow, h_K_right, map_mul, map_inv] at h_right
      have h_lhs : (SemidirectProduct.rightHom
            ((SemidirectProduct.inl x : CyclicExtPreG N σ)))⁻¹ *
          SemidirectProduct.rightHom
            (SemidirectProduct.inr (Multiplicative.ofAdd (k : ℤ)) : CyclicExtPreG N σ) =
          Multiplicative.ofAdd (k : ℤ) := by
        simp
      rw [h_lhs, ← ofAdd_zsmul] at h_right
      have h_int : (k : ℤ) = j * m := by
        have := congrArg Multiplicative.toAdd h_right
        simpa [smul_eq_mul] using this.symm
      have : (m : ℤ) ∣ (k : ℤ) := ⟨j, by rw [h_int]; ring⟩
      exact_mod_cast this
    have h_ord : orderOf ((g : G ⧸ N₀)) = m := Nat.dvd_antisymm hdvd_m hm_dvd
    calc Nat.card (G ⧸ N₀)
        = Nat.card ↥(⊤ : Subgroup (G ⧸ N₀)) := Subgroup.card_top.symm
      _ = Nat.card ↥(Subgroup.zpowers ((g : G ⧸ N₀))) := by rw [hz]
      _ = orderOf ((g : G ⧸ N₀)) := Nat.card_zpowers _
      _ = m := h_ord
  · -- Conjugation: g · ι x · g⁻¹ = ι (σ x) via SemidirectProduct.inl_aut.
    intro x
    have h_iota_x : (ι x : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl x) := rfl
    have h_iota_σx : (ι (σ x) : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl (σ x)) := rfl
    rw [h_iota_x, h_iota_σx]
    change (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))) *
        (QuotientGroup.mk' _ (SemidirectProduct.inl x)) *
        (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))))⁻¹ =
      QuotientGroup.mk' _ (SemidirectProduct.inl (σ x))
    rw [← map_inv (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
        ← map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
        ← map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ))]
    congr 1
    -- Goal: inr (ofAdd 1) * inl x * (inr (ofAdd 1))⁻¹ = inl (σ x)
    have h_phi : (cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) = σ := by
      change σ ^ (Multiplicative.ofAdd (1 : ℤ)).toAdd = σ
      exact zpow_one σ
    have h_inl_aut : (SemidirectProduct.inl ((cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) x)
        : CyclicExtPreG N σ) =
        SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) * SemidirectProduct.inl x *
          SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))⁻¹ :=
      SemidirectProduct.inl_aut (φ := cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) x
    rw [h_phi] at h_inl_aut
    rw [← (SemidirectProduct.inr : Multiplicative ℤ →* CyclicExtPreG N σ).map_inv] at *
    exact h_inl_aut.symm

end -- 3F

end OddOrder.Isaacs.Ch03
