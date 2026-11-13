module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbFluct
public import BlockBand.Endpoints.Clock.ZeroEntranceProbChain

/-!
# The zero-entrance lemma: the mean of the normalized trace and the finite chain

Law: `oneEndedLaw W b J` with the zero boundary `X_0 = 0`. `MeanBound κ J`: for every domain
`Im z' ≥ η`, `|z'| ≤ M` there is `C` such that for all `W ≥ 1`, `(b, e)` in the compact set and
every solution `m` of the chain with `J` physical sites and port parameter `z'`
(`IsPortChain b e J z' m`, the finite Dyson equation with `z` replaced by `z'`):
`|E h_J(z') - m_{J+1}| ≤ C / W`.

Proof (induction on `J`, nesting the cavity maps). The chain values `(m_{J+1}, m_{J+2})` are an
approximate solution of the cavity equations of the last layer for the old input `X_J`: the port
equation holds exactly, and `m_{J+1}` is the port value of the sub-chain with port parameter
`ζ* = -e - c m_{J+1} - b m_{J+2}`, so by induction `|m_{J+1} - E f_{X_J}(ζ*)| ≤ C/W`, while
`E|f_{X_J}(ζ*) - E f_{X_J}(ζ*)| ≤ C√2/W` (`FluctBound`). The deterministic stability
(`cavityStability_uniform`) and `|E(h₊|X) - u(X)| ≤ C/W²` (`CavityLayerUniform`) close the step.
A by-product: chain solutions have a unique port value
(`portChain_port_unique`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Metric
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements (freshSchur freshLaw)
open scoped ENNReal NNReal Real

namespace ZeroEntranceProb

/-- Mean of the normalized trace after `J` layers versus the finite chain. -/
def MeanBound (κ : ℝ) (J : ℕ) : Prop :=
  ∀ η M : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, 0 < W → ∀ b e : ℝ, zeParam κ b e →
    ∀ z' : ℂ, η ≤ z'.im → ‖z'‖ ≤ M → ∀ m : ℕ → ℂ, IsPortChain b e J z' m →
      ‖meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) J z' - m (J + 1)‖ ≤ C / W

/-- The sub-chain of a chain with `J + 1` sites. -/
theorem portChain_sub {b e : ℝ} {J : ℕ} {z' : ℂ} {m : ℕ → ℂ} (h : IsPortChain b e (J + 1) z' m) :
    IsPortChain b e J (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * m (J + 1) - b * m (J + 2)) m where
  zero := h.zero
  im_neg ℓ h1 h2 := h.im_neg ℓ h1 (by omega)
  bulk ℓ h1 h2 := h.bulk ℓ h1 (by omega)
  port := by
    have := h.bulk (J + 1) (by omega) le_rfl
    rw [this]; simp only [Nat.add_sub_cancel]; ring

theorem normalizedResolventTrace_zero {W : ℕ} (hW : 0 < W) (z : ℂ) :
    normalizedResolventTrace (0 : Matrix (Fin W) (Fin W) ℂ) z = z⁻¹ := by
  unfold normalizedResolventTrace
  rw [sub_zero]
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; simp
  · rw [ZeroEntranceScale.inv_smul_of_ne hz, inv_one, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul]
    have : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
    field_simp

theorem meanBound_zero (κ : ℝ) : MeanBound κ 0 := by
  intro η M hη
  refine ⟨1, one_pos, ?_⟩
  intro W hW b e hbe z' hz hzM m hm
  have h1 : meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) 0 z' = z'⁻¹ := by
    unfold meanTrace
    have : ∀ ω : Fin 0 → OneEndedLayer W,
        zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) 0 z' ω = z'⁻¹ := fun ω =>
      normalizedResolventTrace_zero hW z'
    simp only [this, integral_const, probReal_univ, one_smul]
  have h2 : m 1 = z'⁻¹ := by
    have := hm.port
    rw [hm.zero, mul_zero, sub_zero] at this
    rw [← this, inv_inv]
  rw [h1, h2, sub_self, norm_zero]
  positivity

set_option maxHeartbeats 1000000 in
theorem meanBound_succ (hU : CavityLayerUniform) {κ : ℝ} (hκ : 0 < κ) {J : ℕ}
    (ihM : MeanBound κ J) (ihF : FluctBound κ J) : MeanBound κ (J + 1) := by
  intro η M hη
  set Mp := max M 0 with hMpdef
  have hMp : 0 ≤ Mp := le_max_right _ _
  set ast := astarK κ Mp with hastdef
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hast : 0 < ast := by rw [hastdef]; unfold astarK; positivity
  set sbar := min κ 1 * η * ast ^ 2 with hsbar
  set R' := 2 + 1 / Real.sqrt κ + 1 / η + Mp + η with hR'
  have hs0 : 0 < sbar := by
    have : 0 < min κ 1 := lt_min hκ one_pos
    positivity
  obtain ⟨a₀, CQ, ha₀, hCQ, hUQ⟩ := hU κ hκ η Mp hη
  obtain ⟨Cs, hCs0, hCs⟩ := cavityStability_uniform hκ hη hMp hast
  obtain ⟨CM, hCM, hihM⟩ := ihM sbar R' hs0
  obtain ⟨aF, CF, haF, hCF, hihF⟩ := ihF sbar R' hs0
  refine ⟨CQ + Cs * (CM + CF * Real.sqrt 2) + 4 / (aF * η) + 1, by positivity, ?_⟩
  intro W hW b e hbe z' hz hzM m hm
  obtain ⟨hb0, hb1, hb1', hcκ, hc1, he2, he4⟩ := zeParam_facts hκ hbe
  have hc : 0 < 1 - 2 * b := by linarith
  have hzMp : ‖z'‖ ≤ Mp := hzM.trans (le_max_left _ _)
  have hz0 : 0 < z'.im := hη.trans_le hz
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set vbar := m (J + 1) with hvbar
  set ubar := m (J + 2) with hubar
  have hvim : vbar.im < 0 := hm.im_neg (J + 1) (by omega) (by omega)
  have huim : ubar.im < 0 := hm.im_neg (J + 2) (by omega) le_rfl
  have hueq : ubar = (z' - b * vbar)⁻¹ := by
    have := hm.port; rw [← this, inv_inv]
  have hward : η * ‖ubar‖ ^ 2 ≤ -ubar.im :=
    le_trans (mul_le_mul_of_nonneg_right hz (sq_nonneg _)) (portChain_port_ward hm hb0.le)
  have hu0 : 0 < ‖ubar‖ := norm_pos_iff.mpr (fun h => by rw [h] at huim; simp at huim)
  have hu1 : ‖ubar‖ ≤ 1 / η := by
    have : -ubar.im ≤ ‖ubar‖ := by
      have := Complex.abs_im_le_norm ubar; rw [abs_le] at this; linarith
    rw [le_div_iff₀ hη]; nlinarith
  have hv1 : ‖vbar‖ ≤ 1 / Real.sqrt κ := by
    have h1 := portChain_phys_bound hm hb0.le (ℓ := J + 1) (by omega) (by omega)
    have h2 : ‖vbar‖ ^ 2 ≤ 1 / κ := by
      rw [le_div_iff₀ hκ]
      calc ‖vbar‖ ^ 2 * κ ≤ ‖vbar‖ ^ 2 * (1 - 2 * b) := by gcongr
        _ ≤ 1 := by linarith
    rw [← Real.sqrt_sq (norm_nonneg vbar), one_div, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by rw [← one_div]; exact h2)
  have hua : ast ≤ ‖ubar‖ := by
    have hne : z' - b * vbar ≠ 0 := by
      intro h; have := congrArg Complex.im h
      simp at this; nlinarith
    have hnorm : ‖z' - b * vbar‖ ≤ Mp + 1 / Real.sqrt κ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      have : b * ‖vbar‖ ≤ 1 / Real.sqrt κ := by
        calc b * ‖vbar‖ ≤ 1 * ‖vbar‖ := by gcongr
          _ ≤ _ := by rw [one_mul]; exact hv1
      linarith
    rw [hueq, norm_inv, hastdef]
    unfold astarK
    rw [← one_div]
    exact one_div_le_one_div_of_le (norm_pos_iff.mpr hne) (by linarith)
  set ζs : ℂ := -(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar with hζs
  have hζim : sbar ≤ ζs.im := by
    have harg : ζs.im = (1 - 2 * b) * (-vbar.im) + b * (-ubar.im) := by
      rw [hζs]; simp; ring
    rw [harg, hsbar]
    have e1 : min κ 1 * η * ast ^ 2 ≤ b * (η * ‖ubar‖ ^ 2) := by
      have : min κ 1 ≤ b := (min_le_left _ _).trans hbe.1
      have h3 : ast ^ 2 ≤ ‖ubar‖ ^ 2 := pow_le_pow_left₀ hast.le hua 2
      calc min κ 1 * η * ast ^ 2 = min κ 1 * (η * ast ^ 2) := by ring
        _ ≤ b * (η * ‖ubar‖ ^ 2) := by gcongr
    have e2 : b * (η * ‖ubar‖ ^ 2) ≤ b * (-ubar.im) := mul_le_mul_of_nonneg_left hward hb0.le
    have e3 : 0 ≤ (1 - 2 * b) * (-vbar.im) := mul_nonneg hc.le (by linarith)
    linarith
  have hζn : ‖ζs‖ ≤ R' := by
    rw [hζs]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hb0.le]
    have e1 : (1 - 2 * b) * ‖vbar‖ ≤ 1 / Real.sqrt κ := by
      calc (1 - 2 * b) * ‖vbar‖ ≤ 1 * ‖vbar‖ := by gcongr
        _ ≤ 1 / Real.sqrt κ := by rw [one_mul]; exact hv1
    have e2 : b * ‖ubar‖ ≤ 1 / η := by
      calc b * ‖ubar‖ ≤ 1 * ‖ubar‖ := by gcongr
        _ ≤ 1 / η := by rw [one_mul]; exact hu1
    rw [hR']
    linarith
  have hζpos : 0 < ζs.im := hs0.trans_le hζim
  have hD0 : (0 : Matrix (Fin W) (Fin W) ℂ).IsHermitian := Matrix.isHermitian_zero
  have hfm : IsFiniteMeasure (oneEndedLaw W b J) := inferInstance
  -- trivial bound
  have htriv : ‖meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) (J + 1) z' - m (J + 1 + 1)‖ ≤
      2 / η := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := (norm_meanTrace_le hW b e hD0 (J + 1) hz0).trans (one_div_le_one_div_of_le hη hz)
    have h2 : ‖m (J + 1 + 1)‖ ≤ 1 / η := hu1
    have : 2 / η = 1 / η + 1 / η := by ring
    linarith
  by_cases hWa : 2 ≤ aF * W
  swap
  · refine htriv.trans ?_
    push Not at hWa
    rw [le_div_iff₀ hWr]
    have h4 : 2 / η * W ≤ 4 / (aF * η) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hη (by positivity)]
      nlinarith
    have : 0 ≤ CQ + Cs * (CM + CF * Real.sqrt 2) := by positivity
    nlinarith
  -- main case
  have hsub := portChain_sub hm
  have hMJ := hihM W hW b e hbe ζs hζim hζn m hsub
  set mJ := meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) J ζs with hmJ
  set Fz : (Fin J → OneEndedLayer W) → ℂ := fun x =>
    zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζs x - mJ with hFz
  have hFzm : Measurable Fz := (measurable_zeTrace e _ J ζs).sub_const _
  have hFint : Integrable Fz (oneEndedLaw W b J) :=
    (integrable_zeTrace hW b e hD0 J hζpos).sub (integrable_const _)
  have hEF : ∫ x, ‖Fz x‖ ∂oneEndedLaw W b J ≤ CF * Real.sqrt 2 / W := by
    have hb := hihF W hW b e hbe 0 hD0 ζs hζim hζn 2 le_rfl hWa
    exact integral_norm_le_of_eLpNorm_two hFzm.aestronglyMeasurable (by positivity) hb
  have hpt : ∀ᵐ x ∂oneEndedLaw W b J,
      ‖condMean b e (0 : Matrix (Fin W) (Fin W) ℂ) J z' x - ubar‖ ≤
        CQ / (W : ℝ) ^ 2 + Cs * ‖vbar - mJ‖ + Cs * ‖Fz x‖ := by
    filter_upwards [ae_X_isHermitian b e hD0 J] with x hx
    have hQ := (hUQ b hbe.1 hbe.2.1 W hW (oneEndedX e 0 J x) hx e z' hz hzMp).1
    have hcmp := cavity_compare hκ hη hCs hW hx hbe hz hzMp hvim.le hua hward hueq
      (ne_of_gt hζpos)
    have hsplit : ‖vbar - normalizedResolventTrace (oneEndedX e 0 J x) ζs‖ ≤
        ‖vbar - mJ‖ + ‖Fz x‖ := by
      have : vbar - normalizedResolventTrace (oneEndedX e 0 J x) ζs = (vbar - mJ) - Fz x := by
        rw [hFz]; simp only; rw [sub_sub_sub_cancel_right]
        show vbar - normalizedResolventTrace (oneEndedX e 0 J x) ζs =
          vbar - zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζs x
        rfl
      rw [this]; exact norm_sub_le _ _
    calc ‖condMean b e (0 : Matrix (Fin W) (Fin W) ℂ) J z' x - ubar‖
        ≤ ‖condMean b e (0 : Matrix (Fin W) (Fin W) ℂ) J z' x -
            cavityU (oneEndedX e 0 J x) b e z'‖ + ‖cavityU (oneEndedX e 0 J x) b e z' - ubar‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ CQ / (W : ℝ) ^ 2 + Cs * (‖vbar - mJ‖ + ‖Fz x‖) := by
          gcongr
          · exact hQ
          · exact hcmp.trans (mul_le_mul_of_nonneg_left hsplit hCs0.le)
      _ = _ := by ring
  have hmean := integral_zeTrace_succ hW b e hD0 J hz0 (z' := z')
  have hcmI := integrable_condMean hW b e hD0 J hz0 (z' := z')
  have hgoal : ‖meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) (J + 1) z' - ubar‖ ≤
      CQ / (W : ℝ) ^ 2 + Cs * ‖vbar - mJ‖ + Cs * (CF * Real.sqrt 2 / W) := by
    have h1 : meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) (J + 1) z' - ubar =
        ∫ x, (condMean b e (0 : Matrix (Fin W) (Fin W) ℂ) J z' x - ubar) ∂oneEndedLaw W b J := by
      rw [integral_sub hcmI (integrable_const _), integral_const, probReal_univ, one_smul]
      unfold meanTrace; rw [hmean]
    rw [h1]
    refine (norm_integral_le_integral_norm _).trans ?_
    set cst : ℝ := CQ / (W : ℝ) ^ 2 + Cs * ‖vbar - mJ‖ with hcst
    have hc0 : Integrable (fun _ : Fin J → OneEndedLayer W => cst) (oneEndedLaw W b J) :=
      @integrable_const _ _ _ _ _ hfm cst
    have hc1 : Integrable (fun x => Cs * ‖Fz x‖) (oneEndedLaw W b J) := hFint.norm.const_mul Cs
    have hgI := hc0.add hc1
    have hfI := (hcmI.sub (integrable_const (μ := oneEndedLaw W b J) ubar)).norm
    refine (integral_mono_ae hfI hgI ?_).trans ?_
    · filter_upwards [hpt] with x hx
      exact hx
    simp only [Pi.add_apply]
    rw [integral_add hc0 hc1, integral_const, probReal_univ, one_smul, integral_const_mul]
    gcongr
  have hfinal : CQ / (W : ℝ) ^ 2 + Cs * ‖vbar - mJ‖ + Cs * (CF * Real.sqrt 2 / W) ≤
      (CQ + Cs * (CM + CF * Real.sqrt 2) + 4 / (aF * η) + 1) / W := by
    have h1 : CQ / (W : ℝ) ^ 2 ≤ CQ / W :=
      div_le_div_of_nonneg_left hCQ.le hWr (le_self_pow₀ hW1 two_ne_zero)
    have h2 : Cs * ‖vbar - mJ‖ ≤ Cs * (CM / W) := by
      rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hMJ hCs0.le
    have h3 : 0 ≤ (4 / (aF * η) + 1) / W := by positivity
    have : (CQ + Cs * (CM + CF * Real.sqrt 2) + 4 / (aF * η) + 1) / W =
        CQ / W + Cs * (CM / W) + Cs * (CF * Real.sqrt 2 / W) + (4 / (aF * η) + 1) / W := by
      ring
    rw [this]; linarith
  exact hgoal.trans hfinal

/-- **The mean bound for every `J`**: the mean of the normalized trace is within `C/W` of the port
value of every chain solution (the finite Dyson equation with port parameter `z'`). -/
theorem meanBound_all (hU : CavityLayerUniform) {κ : ℝ} (hκ : 0 < κ) (J : ℕ) : MeanBound κ J := by
  induction J with
  | zero => exact meanBound_zero κ
  | succ J ih => exact meanBound_succ hU hκ ih (fluctBound_all hU hκ J)

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
