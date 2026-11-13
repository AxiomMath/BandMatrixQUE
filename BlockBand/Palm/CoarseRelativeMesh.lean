module

public import BlockBand.Palm.CoarseRelativeDyson

/-!
# Coarse relative local law: interpolation between mesh points

A sufficiently fine polynomial mesh controls interpolation in `z`, even in directions where
`q* Im M_s q` is small. With the fixed constants `A, c₀, r₀, s₀, v₀` chosen first,
there is `N₁` such that for `N ≥ N₁`, every `F` in the fresh class, every `s` in the
variance window, every Hermitian `G`, and all `z, z'` in the coarse domain with
`|z - z'| ≤ N^{-K}` (`K = meshExp A`), the trace bound and every directional relative
bound at `z'` with constant `N^{-1/3}/2` imply the same bounds at `z` with `N^{-1/3}`.
The statement is deterministic. It uses the regularity bounds, the directional Ward identity, the
directional lower bound and the Lipschitz bounds from `CoarseRelativeDyson`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open scoped ComplexConjugate

variable {N : ℕ}

/-- The coarse domain `|x - E| ≤ r₀/2`, `N^{-1/100} ≤ η ≤ 1` of the coarse relative local law. -/
def CoarseDomain (N : ℕ) (E r₀ : ℝ) (z : ℂ) : Prop :=
  |z.re - E| ≤ r₀ / 2 ∧ (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ z.im ∧ z.im ≤ 1

/-- `G_s(z) = (F + √s G - z)⁻¹`. -/
def coarseResolvent (F G : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- Trace error `|⟨G_s(z)⟩ - m_s(z)|`. -/
def traceErr (F G : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : ℝ :=
  ‖(N : ℂ)⁻¹ * (coarseResolvent F G s z).trace - freshDyson F s z‖

/-- Directional error `|q*(G_s(z) - M_s(z))q|`. -/
def quadErr (F G : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (q : Fin N → ℂ) : ℝ :=
  ‖star q ⬝ᵥ ((coarseResolvent F G s z - freshM F s z) *ᵥ q)‖

/-- Deterministic directional scale `q* Im M_s(z) q = Im(q* M_s(z) q)`. -/
def quadIm (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (q : Fin N → ℂ) : ℝ :=
  (star q ⬝ᵥ (freshM F s z *ᵥ q)).im

/-- Mesh exponent `K = 2 max(A,1) + 1 + 1/3 + 1/50`. -/
def meshExp (A : ℝ) : ℝ := 2 * max A 1 + 1 + 1 / 3 + 1 / 50

theorem coarse_hermitian {F G : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hG : G.IsHermitian) (s : ℝ) : (F + (Real.sqrt s : ℂ) • G).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, hF.eq, hG.eq, Complex.star_def, Complex.conj_ofReal]

theorem coarse_height_pos (N : ℕ) : 0 < (N : ℝ) ^ (-(1 / 100 : ℝ)) ∨ N = 0 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exact Or.inr h
  · exact Or.inl (Real.rpow_pos_of_pos (by exact_mod_cast h) _)

/-- Facts at a point of the coarse domain: the fresh regularity bounds and lower bounds on
`Im w` and `q* Im M_s q`. -/
theorem coarse_domain_facts {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ s : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀)
    (hC : FreshClass F A c₀ E r₀ s₀ v₀) (hs : s ∈ Set.Icc (c₀ - s₀) c₀) {z : ℂ}
    (hz : CoarseDomain N E r₀ z) :
    0 < s ∧ |z.re - E| ≤ r₀ ∧ 0 < z.im ∧ 0 < (freshDyson F s z).im ∧
      (c₀ - s₀) * v₀ ≤ (freshW F s z).im ∧
      (N : ℝ) ^ (-(1 / 100 : ℝ)) / (1 + v₀⁻¹) ≤
        z.im / (z.im + s * (freshDyson F s z).im) := by
  obtain ⟨hx, hη0, hη1⟩ := hz
  obtain ⟨hs0, hss, hs1⟩ := fresh_s_bounds hK hs
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  have hr0 : 0 < r₀ := hK.2.2.1
  have hh : 0 < (N : ℝ) ^ (-(1 / 100 : ℝ)) := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hηpos : 0 < z.im := hh.trans_le hη0
  have hx' : |z.re - E| ≤ r₀ := hx.trans (by linarith)
  obtain ⟨hv, hv'⟩ := fresh_regular_bounds hC.2.2 hs hx' hηpos.le hη1
  have hspos : 0 < s := lt_of_lt_of_le hs0 hss
  have hm : 0 < (freshDyson F s z).im := lt_of_lt_of_le hv0 hv
  refine ⟨hspos, hx', hηpos, hm, ?_, ?_⟩
  · rw [freshW_im]
    have : (c₀ - s₀) * v₀ ≤ s * (freshDyson F s z).im := mul_le_mul hss hv hv0.le hspos.le
    linarith
  · have hsm : s * (freshDyson F s z).im ≤ v₀⁻¹ := by
      calc s * (freshDyson F s z).im ≤ 1 * v₀⁻¹ := mul_le_mul hs1.le hv' hm.le zero_le_one
        _ = v₀⁻¹ := one_mul _
    have hden : 0 < z.im + s * (freshDyson F s z).im := by positivity
    rw [div_le_div_iff₀ (by positivity) hden]
    have h1 : z.im + s * (freshDyson F s z).im ≤ 1 + v₀⁻¹ := by linarith
    calc (N : ℝ) ^ (-(1 / 100 : ℝ)) * (z.im + s * (freshDyson F s z).im)
        ≤ z.im * (z.im + s * (freshDyson F s z).im) :=
          mul_le_mul_of_nonneg_right hη0 hden.le
      _ ≤ z.im * (1 + v₀⁻¹) := mul_le_mul_of_nonneg_left h1 hηpos.le

/-- Three-term triangle inequality used for interpolation. -/
theorem norm_sub_interp (t t' m m' : ℂ) :
    ‖t - m‖ ≤ ‖t' - m'‖ + ‖t - t'‖ + ‖m - m'‖ := by
  have : t - m = (t' - m') + (t - t') - (m - m') := by ring
  rw [this]
  exact (norm_sub_le _ _).trans (by linarith [norm_add_le (t' - m') (t - t')])

/-!
Small real-arithmetic helpers (kept separate so that each proof has a small context).
-/

theorem aux_div_le {d s s_ δ₀ B P : ℝ} (hd : 0 ≤ d) (hs_ : 0 < s_) (hss : s_ ≤ s)
    (hδ₀ : 0 < δ₀) (hδinv : δ₀⁻¹ ≤ B * P) : d / (s * δ₀) ≤ d * P * (B / s_) := by
  have hs : 0 < s := lt_of_lt_of_le hs_ hss
  have h1 : d / (s * δ₀) = d * δ₀⁻¹ * s⁻¹ := by field_simp
  have h2 : s⁻¹ ≤ s_⁻¹ := inv_anti₀ hs_ hss
  rw [h1]
  calc d * δ₀⁻¹ * s⁻¹ ≤ d * (B * P) * s_⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hδinv hd) h2 (by positivity)
          (mul_nonneg hd (le_trans (by positivity) hδinv))
    _ = d * P * (B / s_) := by ring

theorem aux_const_M {B P k Cst : ℝ} (hP : 1 ≤ P) (hk : 0 ≤ k)
    (hC : 1 + (1 + B) * k ≤ Cst) : (1 + B * P) * k ≤ P * Cst := by
  have h1 : (1 + B * P) * k ≤ P * ((1 + B) * k) := by
    have : 1 + B * P ≤ P * (1 + B) := by linarith
    calc (1 + B * P) * k ≤ P * (1 + B) * k := mul_le_mul_of_nonneg_right this hk
      _ = P * ((1 + B) * k) := by ring
  have h2 : P * ((1 + B) * k) ≤ P * Cst := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  linarith

theorem aux_const_D {B P k Cst : ℝ} (hP : 1 ≤ P) (hk : 0 ≤ k)
    (hC : 1 + (1 + B) * k ≤ Cst) : P + (1 + B * P) * k ≤ P * Cst := by
  have h1 : (1 + B * P) * k ≤ P * ((1 + B) * k) := by
    have : 1 + B * P ≤ P * (1 + B) := by linarith
    calc (1 + B * P) * k ≤ P * (1 + B) * k := mul_le_mul_of_nonneg_right this hk
      _ = P * ((1 + B) * k) := by ring
  have h2 : P * (1 + (1 + B) * k) ≤ P * Cst := mul_le_mul_of_nonneg_left hC (by linarith)
  linarith

theorem aux_half {ε g c : ℝ} (hε : 0 ≤ ε) (hg1 : g ≤ 1) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 / 2) : ε * g * c ≤ ε / 2 := by
  calc ε * g * c ≤ ε * 1 * (1 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg1 hε) hc hc0 (by linarith)
    _ = ε / 2 := by ring

/-- **Mesh interpolation**, with the constants chosen first. -/
theorem coarse_interpolation {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) :
    ∃ N₁ : ℕ, 0 < N₁ ∧ ∀ N : ℕ, N₁ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ G : Matrix (Fin N) (Fin N) ℂ, G.IsHermitian →
      ∀ z z' : ℂ, CoarseDomain N E r₀ z → CoarseDomain N E r₀ z' →
        ‖z - z'‖ ≤ (N : ℝ) ^ (-meshExp A) →
        (traceErr F G s z' ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 →
            traceErr F G s z ≤ (N : ℝ) ^ (-(1 / 3 : ℝ))) ∧
        ∀ q : Fin N → ℂ, (quadErr F G s z' q ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z' q →
            quadErr F G s z q ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) * quadIm F s z q) := by
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  have hs_ : 0 < c₀ - s₀ := by have := hK.2.2.2.2.1; have := hK.1; linarith
  set B := 1 + v₀⁻¹ with hBdef
  have hB : 0 < B := by positivity
  set κ := (c₀ - s₀) * v₀ with hκdef
  have hκ : 0 < κ := mul_pos hs_ hv0
  set k := κ⁻¹ ^ 2 with hkdef
  have hk : 0 < k := by positivity
  set Cst := 1 + B / (c₀ - s₀) + (1 + B) * k with hCdef
  have hCst : 0 < Cst := by positivity
  have hlow : 0 < lowConst c₀ s₀ v₀ := by unfold lowConst; positivity
  refine ⟨⌈2 * Cst + 4 * Cst / lowConst c₀ s₀ v₀⌉₊ + 1, Nat.succ_pos _, ?_⟩
  intro N hN₁ F E hC s hs G hG z z' hz hz' hzz
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos _) hN₁
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNbig : 2 * Cst + 4 * Cst / lowConst c₀ s₀ v₀ ≤ N := by
    have h1 := Nat.le_ceil (2 * Cst + 4 * Cst / lowConst c₀ s₀ v₀)
    have h2 : ((⌈2 * Cst + 4 * Cst / lowConst c₀ s₀ v₀⌉₊ + 1 : ℕ) : ℝ) ≤ N := by
      exact_mod_cast hN₁
    push_cast at h2
    linarith
  have hF := hC.1
  have hH := coarse_hermitian hF hG s
  -- facts at both points
  obtain ⟨hspos, hx, hηpos, hm, hκw, hδ⟩ := coarse_domain_facts hNpos hK hC hs hz
  obtain ⟨-, hx', hηpos', hm', hκw', hδ'⟩ := coarse_domain_facts hNpos hK hC hs hz'
  obtain ⟨hss, hsc⟩ := hs
  set h := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos hNr _
  have hhz : h ≤ z.im := hz.2.1
  have hhz' : h ≤ z'.im := hz'.2.1
  set δ₀ := h / B with hδ₀def
  have hδ₀ : 0 < δ₀ := div_pos hh hB
  set P := (N : ℝ) ^ (1 / 50 : ℝ) with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 (by norm_num)
  have hhP : h⁻¹ ^ 2 = P := by
    rw [hhdef, hPdef, ← Real.rpow_neg hNr.le, neg_neg, ← Real.rpow_natCast,
      ← Real.rpow_mul hNr.le]
    norm_num
  have hhP' : h⁻¹ ≤ P := by
    have h1 : 1 ≤ h⁻¹ := by
      rw [hhdef, ← Real.rpow_neg hNr.le, neg_neg]
      exact Real.one_le_rpow hN1 (by norm_num)
    rw [← hhP]
    calc h⁻¹ = h⁻¹ * 1 := (mul_one _).symm
      _ ≤ h⁻¹ * h⁻¹ := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = h⁻¹ ^ 2 := (pow_two _).symm
  have hδinv : δ₀⁻¹ ≤ B * P := by
    rw [hδ₀def, inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hhP' hB.le
  set d := ‖z - z'‖ with hddef
  have hd0 : 0 ≤ d := norm_nonneg _
  -- Lipschitz bounds
  have hLm : ‖freshDyson F s z - freshDyson F s z'‖ ≤ d / (s * δ₀) :=
    freshDyson_lipschitz hF hNpos hspos hηpos.le hηpos'.le hm hm' hδ₀ hδ hδ'
  have hLm' : s * ‖freshDyson F s z - freshDyson F s z'‖ ≤ d * δ₀⁻¹ := by
    have := mul_le_mul_of_nonneg_left hLm hspos.le
    calc s * ‖freshDyson F s z - freshDyson F s z'‖ ≤ s * (d / (s * δ₀)) := this
      _ = d * δ₀⁻¹ := by field_simp
  have hLw : ‖freshW F s z - freshW F s z'‖ ≤ d * (1 + B * P) := by
    have heq : freshW F s z - freshW F s z' =
        (z - z') + (s : ℂ) * (freshDyson F s z - freshDyson F s z') := by
      unfold freshW; ring
    rw [heq]
    have h1 := norm_add_le (z - z') ((s : ℂ) * (freshDyson F s z - freshDyson F s z'))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos] at h1
    have h2 : d * δ₀⁻¹ ≤ d * (B * P) := mul_le_mul_of_nonneg_left hδinv hd0
    calc _ ≤ ‖z - z'‖ + s * ‖freshDyson F s z - freshDyson F s z'‖ := h1
      _ ≤ d + d * (B * P) := by rw [← hddef]; linarith
      _ = d * (1 + B * P) := by ring
  have hLt : ‖(N : ℂ)⁻¹ * (coarseResolvent F G s z).trace -
      (N : ℂ)⁻¹ * (coarseResolvent F G s z').trace‖ ≤ d * P := by
    have := resolvent_trace_lipschitz hH hNpos hh hhz hhz'
    rw [hhP] at this
    exact this
  have hLR : ∀ q : Fin N → ℂ, ‖star q ⬝ᵥ ((coarseResolvent F G s z -
      coarseResolvent F G s z') *ᵥ q)‖ ≤ d * P * nsq q := by
    intro q
    have := resolvent_quad_lipschitz hH hh hhz hhz' q
    rw [hhP] at this
    exact this
  have hLM : ∀ q : Fin N → ℂ, ‖star q ⬝ᵥ ((freshM F s z - freshM F s z') *ᵥ q)‖ ≤
      d * (1 + B * P) * k * nsq q := by
    intro q
    have := resolvent_quad_lipschitz hF hκ hκw hκw' q
    rw [← freshM_eq, ← freshM_eq] at this
    refine this.trans ?_
    have hq := nsq_nonneg q
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLw hk.le) hq
  -- the mesh scale: N^{-K} P = ε g N⁻¹
  set ε := (N : ℝ) ^ (-(1 / 3 : ℝ)) with hεdef
  set g := (N : ℝ) ^ (-(2 * max A 1)) with hgdef
  have hε : 0 < ε := Real.rpow_pos_of_pos hNr _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hg : 0 < g := Real.rpow_pos_of_pos hNr _
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1
    (by have := le_max_right A 1; linarith)
  have hscale : (N : ℝ) ^ (-meshExp A) * P = ε * g * (N : ℝ)⁻¹ := by
    rw [hPdef, hεdef, hgdef, ← Real.rpow_add hNr, ← Real.rpow_neg_one, ← Real.rpow_add hNr,
      ← Real.rpow_add hNr, meshExp]
    congr 1
    ring
  have hdP : d * P ≤ ε * g * (N : ℝ)⁻¹ := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_right hzz (by linarith)
  have hNC : Cst * (N : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [mul_inv_le_iff₀ hNr]
    have : 0 ≤ 4 * Cst / lowConst c₀ s₀ v₀ := by positivity
    linarith
  have hNC' : 4 * Cst * (N : ℝ)⁻¹ ≤ lowConst c₀ s₀ v₀ := by
    rw [mul_inv_le_iff₀ hNr]
    have : 4 * Cst / lowConst c₀ s₀ v₀ ≤ N := by linarith
    rw [div_le_iff₀ hlow] at this
    linarith
  -- each Lipschitz constant is at most P * Cst
  have hX : 0 ≤ d * P * Cst := by positivity
  have hXε : d * P * Cst ≤ ε * g * (Cst * (N : ℝ)⁻¹) := by
    calc d * P * Cst ≤ ε * g * (N : ℝ)⁻¹ * Cst := mul_le_mul_of_nonneg_right hdP hCst.le
      _ = _ := by ring
  have hCt : 1 + B / (c₀ - s₀) ≤ Cst := by
    have : 0 ≤ (1 + B) * k := by positivity
    rw [hCdef]; linarith
  have hCk : 1 + (1 + B) * k ≤ Cst := by
    have : 0 ≤ B / (c₀ - s₀) := by positivity
    rw [hCdef]; linarith
  have hCst0 : 0 ≤ Cst * (N : ℝ)⁻¹ := by positivity
  constructor
  · intro ht'
    have hsδ : d / (s * δ₀) ≤ d * P * (B / (c₀ - s₀)) := aux_div_le hd0 hs_ hss hδ₀ hδinv
    have htri := norm_sub_interp ((N : ℂ)⁻¹ * (coarseResolvent F G s z).trace)
      ((N : ℂ)⁻¹ * (coarseResolvent F G s z').trace) (freshDyson F s z) (freshDyson F s z')
    unfold traceErr at ht' ⊢
    have hsum : d * P + d * P * (B / (c₀ - s₀)) ≤ d * P * Cst := by
      calc d * P + d * P * (B / (c₀ - s₀)) = d * P * (1 + B / (c₀ - s₀)) := by ring
        _ ≤ d * P * Cst := mul_le_mul_of_nonneg_left hCt (by positivity)
    have hfin : ε * g * (Cst * (N : ℝ)⁻¹) ≤ ε / 2 := aux_half hε.le hg1 hCst0 hNC
    linarith
  · intro q hq'
    have hnq := nsq_nonneg q
    have hlb := freshM_quad_im_lower hNpos hK hC ⟨hss, hsc⟩ hx hηpos.le hz.2.2 q
    unfold quadErr quadIm at hq' ⊢
    -- D(z) - D(z') splits into resolvent and deterministic differences
    have hD : ‖star q ⬝ᵥ ((coarseResolvent F G s z - freshM F s z) *ᵥ q)‖ ≤
        ‖star q ⬝ᵥ ((coarseResolvent F G s z' - freshM F s z') *ᵥ q)‖ +
          d * P * Cst * nsq q := by
      have hdiff : star q ⬝ᵥ ((coarseResolvent F G s z - freshM F s z) *ᵥ q) =
          star q ⬝ᵥ ((coarseResolvent F G s z' - freshM F s z') *ᵥ q) +
            (star q ⬝ᵥ ((coarseResolvent F G s z - coarseResolvent F G s z') *ᵥ q) -
              star q ⬝ᵥ ((freshM F s z - freshM F s z') *ᵥ q)) := by
        simp only [sub_mulVec, dotProduct_sub]
        ring
      rw [hdiff]
      have h1 := norm_add_le (star q ⬝ᵥ ((coarseResolvent F G s z' - freshM F s z') *ᵥ q))
        (star q ⬝ᵥ ((coarseResolvent F G s z - coarseResolvent F G s z') *ᵥ q) -
          star q ⬝ᵥ ((freshM F s z - freshM F s z') *ᵥ q))
      have h2 := norm_sub_le (star q ⬝ᵥ ((coarseResolvent F G s z - coarseResolvent F G s z') *ᵥ q))
        (star q ⬝ᵥ ((freshM F s z - freshM F s z') *ᵥ q))
      have h3 := hLR q
      have h4 := hLM q
      have h5 : d * P * nsq q + d * (1 + B * P) * k * nsq q ≤ d * P * Cst * nsq q := by
        have := mul_le_mul_of_nonneg_left (aux_const_D hP1 hk.le hCk) (mul_nonneg hd0 hnq)
        calc d * P * nsq q + d * (1 + B * P) * k * nsq q =
            d * nsq q * (P + (1 + B * P) * k) := by ring
          _ ≤ d * nsq q * (P * Cst) := this
          _ = d * P * Cst * nsq q := by ring
      linarith
    have hI : (star q ⬝ᵥ (freshM F s z' *ᵥ q)).im ≤ (star q ⬝ᵥ (freshM F s z *ᵥ q)).im +
        d * P * Cst * nsq q := by
      have h1 : (star q ⬝ᵥ (freshM F s z' *ᵥ q)).im - (star q ⬝ᵥ (freshM F s z *ᵥ q)).im ≤
          ‖star q ⬝ᵥ ((freshM F s z - freshM F s z') *ᵥ q)‖ := by
        rw [sub_mulVec, dotProduct_sub]
        have := Complex.abs_im_le_norm (star q ⬝ᵥ (freshM F s z *ᵥ q) -
          star q ⬝ᵥ (freshM F s z' *ᵥ q))
        rw [Complex.sub_im] at this
        have := neg_abs_le ((star q ⬝ᵥ (freshM F s z *ᵥ q)).im -
          (star q ⬝ᵥ (freshM F s z' *ᵥ q)).im)
        linarith
      have h2 := hLM q
      have h5 : d * (1 + B * P) * k * nsq q ≤ d * P * Cst * nsq q := by
        have := mul_le_mul_of_nonneg_left (aux_const_M hP1 hk.le hCk) (mul_nonneg hd0 hnq)
        calc d * (1 + B * P) * k * nsq q = d * nsq q * ((1 + B * P) * k) := by ring
          _ ≤ d * nsq q * (P * Cst) := this
          _ = d * P * Cst * nsq q := by ring
      linarith
    -- assemble
    have hXn : d * P * Cst * nsq q ≤ ε * g * (Cst * (N : ℝ)⁻¹) * nsq q :=
      mul_le_mul_of_nonneg_right hXε hnq
    have hlow' : ε * g * (4 * Cst * (N : ℝ)⁻¹) * nsq q ≤
        ε * (lowConst c₀ s₀ v₀ * g * nsq q) := by
      have := mul_le_mul_of_nonneg_left hNC' (mul_nonneg (mul_nonneg hε.le hg.le) hnq)
      calc ε * g * (4 * Cst * (N : ℝ)⁻¹) * nsq q =
          ε * g * nsq q * (4 * Cst * (N : ℝ)⁻¹) := by ring
        _ ≤ ε * g * nsq q * lowConst c₀ s₀ v₀ := this
        _ = ε * (lowConst c₀ s₀ v₀ * g * nsq q) := by ring
    have hYn : 0 ≤ d * P * Cst * nsq q := mul_nonneg hX hnq
    set I := (star q ⬝ᵥ (freshM F s z *ᵥ q)).im
    set I' := (star q ⬝ᵥ (freshM F s z' *ᵥ q)).im
    set Y := d * P * Cst * nsq q
    have hstep : ‖star q ⬝ᵥ ((coarseResolvent F G s z - freshM F s z) *ᵥ q)‖ ≤
        ε / 2 * I + 2 * Y := by
      have h1 : ε / 2 * I' ≤ ε / 2 * (I + Y) := mul_le_mul_of_nonneg_left hI (by positivity)
      have h2 : ε / 2 * Y ≤ Y := by
        calc ε / 2 * Y ≤ 1 * Y := mul_le_mul_of_nonneg_right (by linarith) hYn
          _ = Y := one_mul Y
      linarith
    have h2Y : 2 * Y ≤ ε / 2 * I := by
      have : 4 * Y ≤ ε * I := by
        calc 4 * Y ≤ 4 * (ε * g * (Cst * (N : ℝ)⁻¹) * nsq q) := by linarith
          _ = ε * g * (4 * Cst * (N : ℝ)⁻¹) * nsq q := by ring
          _ ≤ ε * (lowConst c₀ s₀ v₀ * g * nsq q) := hlow'
          _ ≤ ε * I := mul_le_mul_of_nonneg_left hlb hε.le
      linarith
    linarith

end BlockBand.Palm.CoarseRelative
