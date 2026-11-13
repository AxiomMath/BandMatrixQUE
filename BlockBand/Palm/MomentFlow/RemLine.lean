module

public import BlockBand.Palm.MomentFlow.IsoLine
public import BlockBand.Palm.MomentFlow.RemDev
public import BlockBand.Palm.MomentFlow.Steps2Gap
public import BlockBand.Palm.MomentFlow.Steps2LongUnif
public import BlockBand.Palm.FreshPalmShift

/-!
# The removal average at one time: the resolvent-kernel average of the removed moments

`|Σ_j N⁻¹ η/((λ_j - λ_i)² + η²) E[P_i X_j | 𝓛] - Im m_s(λ_i + iη) E[P_i | 𝓛]|`
`  ≤ (Cst N^ε/√(Nη) + v₀⁻¹ slowConst (δ + η + (c₀ - s))) E[P_i | 𝓛] + B₁^r (B₁/η + v₀⁻¹) N^{-D}`,

`B₁ = max 1 (N‖q‖²)` (deterministic raw overlap bound). The main error is **relative** to
`E[P_i | 𝓛]` (no rough local bound on `P_i` is needed). Here `m_s = freshDyson F s`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.Palm.CoarseRelative
open BlockBand.Palm
open scoped ENNReal NNReal

variable {N : ℕ}

/-- The clamp `x ↦ max (min x (E + ρ)) (E - ρ)`. -/
def clampWin (E ρ x : ℝ) : ℝ := max (min x (E + ρ)) (E - ρ)

theorem clampWin_sub_le (E ρ x y : ℝ) : |clampWin E ρ x - clampWin E ρ y| ≤ |x - y| := by
  unfold clampWin
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem clampWin_mem {E ρ : ℝ} (hρ : 0 ≤ ρ) (x : ℝ) : |clampWin E ρ x - E| ≤ ρ := by
  unfold clampWin
  rw [abs_le]
  constructor
  · linarith [le_max_right (min x (E + ρ)) (E - ρ)]
  · have : max (min x (E + ρ)) (E - ρ) ≤ E + ρ :=
      max_le (min_le_right _ _) (by linarith)
    linarith

theorem clampWin_of_mem {E ρ x : ℝ} (hx : |x - E| ≤ ρ) : clampWin E ρ x = x := by
  unfold clampWin
  rw [abs_le] at hx
  rw [min_eq_left (by linarith), max_eq_left (by linarith)]

/-- `x ↦ m_s(clamp(x) + iη)` is continuous (Lipschitz) on `ℝ`. -/
theorem continuous_freshDyson_clamp (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {s : ℝ} (hs : s ∈ Icc (c₀ - s₀) c₀) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    Continuous (fun x : ℝ => freshDyson F s ⟨clampWin E (r₀ / 2) x, η⟩) := by
  have hr0 := hK.2.2.1
  set L := dysonLipConst c₀ s₀ v₀
  have hL : 0 ≤ L := dysonLipConst_nonneg c₀ s₀ v₀
  have hlip : LipschitzWith (Real.toNNReal L)
      (fun x : ℝ => freshDyson F s ⟨clampWin E (r₀ / 2) x, η⟩) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hL]
    have hx : |(⟨clampWin E (r₀ / 2) x, η⟩ : ℂ).re - E| ≤ r₀ :=
      (clampWin_mem (by linarith) x).trans (by linarith)
    have hy : |(⟨clampWin E (r₀ / 2) y, η⟩ : ℂ).re - E| ≤ r₀ :=
      (clampWin_mem (by linarith) y).trans (by linarith)
    refine (freshDyson_window_lipschitz hN hK hC hs hs hx hy hη hη1 hη hη1).trans ?_
    rw [sub_self, abs_zero, zero_div, add_zero]
    refine mul_le_mul_of_nonneg_left ?_ hL
    have e : (⟨clampWin E (r₀ / 2) x, η⟩ : ℂ) - ⟨clampWin E (r₀ / 2) y, η⟩ =
        ((clampWin E (r₀ / 2) x - clampWin E (r₀ / 2) y : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact clampWin_sub_le E (r₀ / 2) x y
  exact hlip.continuous

theorem sum_remove_le (ξ : Occ N) (i : Fin N) : ∑ k, remove ξ i k ≤ ∑ k, ξ k := by
  refine Finset.sum_le_sum fun k _ => ?_
  unfold remove
  by_cases hk : k = i
  · subst hk; simp
  · simp [Function.update_of_ne hk]

/-- **Removal average at one time** (against the resolvent kernel). -/
theorem removal_average_fixed_time (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ (r : ℕ) (D : ℝ), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
      ∀ a c : ℝ, 0 < a → a < c → c ≤ c₀ → c₀ - s₀ ≤ a → c - a ≤ 1 →
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
          flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ s ∈ Icc a c, ∀ η : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ η → η ≤ 1 →
          ∀ δ : ℝ, 0 ≤ δ → δ ≤ r₀ / 2 → ∀ ξ ∈ sector N r, ∀ i : Fin N,
          ∀ᵐ ω ∂flowLaw N a, ω ∉ B → |flowEigenvalue F a ω s i - E| ≤ δ →
            |∑ j, (N : ℝ)⁻¹ * (η / ((flowEigenvalue F a ω s j - flowEigenvalue F a ω s i) ^ 2 +
                η ^ 2)) * ((flowLaw N a)[fun ω' =>
                  momentMonomial (fun k => flowOverlap F a q s k ω') (remove ξ i) *
                    flowOverlap F a q s j ω' | pathSigma F a a c]) ω -
              (freshDyson F s ⟨flowEigenvalue F a ω s i, η⟩).im *
                ((flowLaw N a)[fun ω' => momentMonomial (fun k => flowOverlap F a q s k ω')
                  (remove ξ i) | pathSigma F a a c]) ω| ≤
              (Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) +
                  v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - s))) *
                ((flowLaw N a)[fun ω' => momentMonomial (fun k => flowOverlap F a q s k ω')
                  (remove ξ i) | pathSigma F a a c]) ω +
              max 1 ((N : ℝ) * nsq q) ^ r *
                ((N : ℝ) * ((N : ℝ)⁻¹ * η⁻¹ * max 1 ((N : ℝ) * nsq q)) + v₀⁻¹) *
                (N : ℝ) ^ (-D) := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  obtain ⟨Cst, hCst, hiso⟩ := isotropic_accuracy_uniform hELG hMDE hLp (A := A) hK' hε hε4
  refine ⟨Cst, hCst, fun r D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hiso (2 * D)
  refine ⟨max N₁ 1, fun N hN F E hC q hq a c ha hac hc hac₀ hca => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_of_max_le_right hN)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨Bad, hBadm, hPBad, hBad⟩ := hN₁ N (le_of_max_le_left hN) F E hC a (c - a) ha.le
    (by linarith) hca hac₀ (by linarith) q
  set μ := flowLaw N a
  have hm : pathSigma F a a c ≤ (inferInstance : MeasurableSpace (FlowSample N)) :=
    pathSigma_le F a a c
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  obtain ⟨B, hB, hμB, hoff⟩ := condExp_indicator_compl_small (μ := μ) hm hBadm.compl ht
  rw [compl_compl] at hμB hoff
  refine ⟨B, hB, ?_, fun s hs η hη hη1 δ hδ hδr ξ hξ i => ?_⟩
  · have h1 : μ.real Bad ≤ (N : ℝ) ^ (-(2 * D)) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hPBad
    have h2 : μ.real Bad / (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ (-D) := by
      rw [div_le_iff₀ ht, ← Real.rpow_add hNp]
      convert h1 using 2; ring
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hμB.trans h2)
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hNp _) hη
  have hsw : s ∈ Icc (c₀ - s₀) c₀ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set lam : FlowSample N → ℝ := fun ω => flowEigenvalue F a ω s i
  set X : Fin N → FlowSample N → ℝ := fun j ω => flowOverlap F a q s j ω
  set P : FlowSample N → ℝ := fun ω => momentMonomial (fun k => X k ω) (remove ξ i)
  set w : Fin N → FlowSample N → ℝ := fun j ω =>
    (N : ℝ)⁻¹ * (η / ((flowEigenvalue F a ω s j - lam ω) ^ 2 + η ^ 2))
  set Y : FlowSample N → ℝ := fun ω => ∑ j, w j ω * X j ω
  set V : FlowSample N → ℝ := fun ω => (freshDyson F s ⟨clampWin E (r₀ / 2) (lam ω), η⟩).im
  set G : Set (FlowSample N) := {ω | |lam ω - E| ≤ δ}
  set B₁ : ℝ := max 1 ((N : ℝ) * nsq q)
  have hB₁ : 1 ≤ B₁ := le_max_left _ _
  set Bw : ℝ := (N : ℝ)⁻¹ * η⁻¹
  have hBw : 0 ≤ Bw := by positivity
  -- measurability
  have hlam : Measurable[pathSigma F a a c] lam := measurable_flowEigenvalue_pathSigma F a a c hs i
  have hwm : ∀ j, StronglyMeasurable[pathSigma F a a c] (w j) := fun j =>
    (measurable_const.mul (measurable_const.div
      ((((measurable_flowEigenvalue_pathSigma F a a c hs j).sub hlam).pow_const 2).add
        measurable_const))).stronglyMeasurable
  have hXm : ∀ j, Measurable (X j) := fun j => measurable_flowOverlap F a q s j
  have hPm : Measurable P :=
    (measurable_momentMonomial (remove ξ i)).comp (Measurable.of_eval fun k => hXm k)
  have hYm : Measurable Y := Finset.measurable_sum _ fun j _ =>
    (((hwm j).mono hm).measurable).mul (hXm j)
  have hVm : StronglyMeasurable[pathSigma F a a c] V :=
    (Complex.continuous_im.comp (continuous_freshDyson_clamp hNpos hK' hC hsw hη0.le hη1)
      ).measurable.comp hlam |>.stronglyMeasurable
  have hGm : MeasurableSet[pathSigma F a a c] G :=
    ((continuous_abs.comp (continuous_sub_right E)).measurable.comp hlam) measurableSet_Iic
  -- bounds
  have hX0 : ∀ j ω, 0 ≤ X j ω := fun j ω => by simp only [X, flowOverlap]; positivity
  have hXB : ∀ j ω, X j ω ≤ B₁ := fun j ω =>
    (FreshPalmAssembly.overlap_le_nsq (flowMatrix F a ω s) q j).trans (le_max_right _ _)
  have hXabs : ∀ j ω, |X j ω| ≤ B₁ := fun j ω => by rw [abs_of_nonneg (hX0 j ω)]; exact hXB j ω
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => by
    simp only [P, momentMonomial]
    exact Finset.prod_nonneg fun k _ => div_nonneg (pow_nonneg (hX0 k ω) _) (Nat.cast_nonneg _)
  have hPB : ∀ ω, P ω ≤ B₁ ^ r := fun ω => by
    have h1 := abs_momentMonomial_le (fun k => hX0 k ω) (fun k => hXB k ω) (remove ξ i)
    have h2 : ∑ k, remove ξ i k ≤ r := (sum_remove_le ξ i).trans (mem_sector.1 hξ).le
    exact (le_abs_self _).trans (h1.trans (pow_le_pow_right₀ hB₁ h2))
  have hw0 : ∀ j ω, 0 ≤ w j ω := fun j ω => by simp only [w]; positivity
  have hwB : ∀ j ω, w j ω ≤ Bw := fun j ω => by
    simp only [w, Bw]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hη0]
    nlinarith [sq_nonneg (flowEigenvalue F a ω s j - lam ω)]
  have hwabs : ∀ j ω, |w j ω| ≤ Bw := fun j ω => by rw [abs_of_nonneg (hw0 j ω)]; exact hwB j ω
  have hYB : ∀ ω, |Y ω| ≤ (N : ℝ) * (Bw * B₁) := fun ω => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |w j ω * X j ω| ≤ ∑ _j : Fin N, Bw * B₁ := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul (hwabs j ω) (hXabs j ω) (abs_nonneg _) hBw
      _ = (N : ℝ) * (Bw * B₁) := by simp
  have hVB : ∀ ω, |V ω| ≤ v₀⁻¹ := fun ω => by
    have hx : |(⟨clampWin E (r₀ / 2) (lam ω), η⟩ : ℂ).re - E| ≤ r₀ :=
      (clampWin_mem (by linarith) _).trans (by linarith)
    obtain ⟨h1, h2⟩ := fresh_regular_bounds hC.2.2 hsw hx hη0.le hη1
    rw [abs_of_nonneg (hv0.le.trans h1)]; exact h2
  -- the deviation on the good event
  set e : ℝ := Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) +
    v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - s))
  have hgood : ∀ᵐ ω ∂μ, ω ∈ G → ω ∉ Bad → |Y ω - V ω| ≤ e := by
    filter_upwards [ae_noCollision (hDBM N) hC.1 ha] with ω ⟨hH, hcol⟩ hωG hωB
    have hlE : |lam ω - E| ≤ r₀ / 2 := (show |lam ω - E| ≤ δ from hωG).trans hδr
    have hHs := flowMatrix_isHermitian hC.1 a hH s
    have hsimp : HasSimpleSpectrum N (flowMatrix F a ω s) :=
      hasSimpleSpectrum_of_injective hHs fun j k hjk => hcol s hs.1 j k hjk
    have hiso' := hBad ω hωB hH s ⟨hs.1, by linarith [hs.2]⟩ (lam ω) hlE η hη hη1
    rw [hq, mul_one] at hiso'
    have hY : Y ω = (star q ⬝ᵥ ((flowMatrix F a ω s - (⟨lam ω, η⟩ : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := by
      rw [← resolvent_im_spectral hHs hsimp hNpos (lam ω) hη0.ne' q, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [w, X, flowOverlap, flowEigenvalue]
      ring
    have hV : V ω = (freshDyson F s ⟨lam ω, η⟩).im := by
      simp only [V]; rw [clampWin_of_mem hlE]
    have hlE' : |(⟨lam ω, η⟩ : ℂ).re - E| ≤ r₀ := hlE.trans (by linarith)
    have hslow := gamma_relative_slow hNpos hK' hC hsw hlE' hη0.le hη1 q
    rw [hq, mul_one] at hslow
    obtain ⟨hm1, hm2⟩ := fresh_regular_bounds hC.2.2 hsw hlE' hη0.le hη1
    have hmpos : 0 < (freshDyson F s ⟨lam ω, η⟩).im := lt_of_lt_of_le hv0 hm1
    set mi := (freshDyson F s ⟨lam ω, η⟩).im
    set gi := (star q ⬝ᵥ (freshM F s ⟨lam ω, η⟩ *ᵥ q)).im
    have hS : |gi - mi| ≤ v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - s)) := by
      have e1 : gi - mi = mi * (gi / mi - 1) := by field_simp
      rw [e1, abs_mul, abs_of_pos hmpos]
      have hsc := slowConst_nonneg hK'
      have hre : (⟨lam ω, η⟩ : ℂ).re = lam ω := rfl
      have him : (⟨lam ω, η⟩ : ℂ).im = η := rfl
      rw [hre, him] at hslow
      have h3 : slowConst c₀ r₀ s₀ v₀ * (|lam ω - E| + η + (c₀ - s)) ≤
          slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - s)) :=
        mul_le_mul_of_nonneg_left (by linarith [show |lam ω - E| ≤ δ from hωG]) hsc
      have h4 : 0 ≤ slowConst c₀ r₀ s₀ v₀ * (|lam ω - E| + η + (c₀ - s)) :=
        (abs_nonneg _).trans hslow
      calc mi * |gi / mi - 1| ≤ v₀⁻¹ * (slowConst c₀ r₀ s₀ v₀ * (|lam ω - E| + η + (c₀ - s))) :=
            mul_le_mul hm2 hslow (abs_nonneg _) (by positivity)
        _ ≤ v₀⁻¹ * (slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - s))) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    have hI : |(star q ⬝ᵥ ((flowMatrix F a ω s - (⟨lam ω, η⟩ : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im - gi| ≤
        Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) := by
      refine le_trans ?_ hiso'
      have e1 : (star q ⬝ᵥ ((flowMatrix F a ω s - (⟨lam ω, η⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im - gi =
          (star q ⬝ᵥ (((flowMatrix F a ω s - (⟨lam ω, η⟩ : ℂ) •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - freshM F s ⟨lam ω, η⟩) *ᵥ q)).im := by
        simp only [gi, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im]
      rw [e1]
      exact Complex.abs_im_le_norm _
    rw [hY, hV]
    calc |(star q ⬝ᵥ ((flowMatrix F a ω s - (⟨lam ω, η⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im - mi|
        ≤ |(star q ⬝ᵥ ((flowMatrix F a ω s - (⟨lam ω, η⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im - gi| + |gi - mi| := abs_sub_le _ _ _
      _ ≤ e := add_le_add hI hS
  have he : 0 ≤ e := by
    have : 0 ≤ Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) := by positivity
    have := slowConst_nonneg hK'
    have : 0 ≤ c₀ - s := by linarith [hs.2]
    positivity
  have hdev := condExp_mul_sub_le (μ := μ) hm hPm hP0 hPB hYm hYB hVm hVB hGm hBadm he hgood
  have hsum : μ[fun ω => P ω * Y ω | pathSigma F a a c] =ᵐ[μ]
      fun ω => ∑ j, w j ω * (μ[fun ω => P ω * X j ω | pathSigma F a a c]) ω :=
    condExp_mul_wsum (μ := μ) hm w X hPm (fun ω => by rw [abs_of_nonneg (hP0 ω)]; exact hPB ω)
      hwm hwabs hXm hXabs
  filter_upwards [hdev, hsum] with ω h1 h2 hωB hωG
  have h3 := hoff ω hωB
  have hlE : |lam ω - E| ≤ r₀ / 2 := (show |lam ω - E| ≤ δ from hωG).trans hδr
  have hVω : V ω = (freshDyson F s ⟨lam ω, η⟩).im := by
    simp only [V]; rw [clampWin_of_mem hlE]
  have key := h1 hωG
  rw [h2, hVω] at key
  have hc : 0 ≤ B₁ ^ r * ((N : ℝ) * (Bw * B₁) + v₀⁻¹) := by positivity
  refine key.trans ?_
  have := mul_le_mul_of_nonneg_left h3.le hc
  linarith only [this]

end BlockBand.Palm.MomentFlow
