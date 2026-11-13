module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbContour
public import BlockBand.Endpoints.Clock.ZeroEntranceProbScale
public import BlockBand.Endpoints.Clock.ZeroEntranceProbMeasure

/-!
# The zero-entrance lemma: concentration of the normalized trace after `J` layers

Law: `oneEndedLaw W b J`; `h_J(ζ) = zeTrace e D J ζ` with an arbitrary deterministic Hermitian
initial matrix `D`.

`FluctBound κ J`: for every domain `Im ζ ≥ η`, `|ζ| ≤ M` there are `a, C > 0` such that for all
`W ≥ 1`, all `(b, e)` in the compact set `zeParam κ`, all Hermitian `D`, all `ζ` in the domain and
`2 ≤ p ≤ aW`: `‖h_J(ζ) - E h_J(ζ)‖_p ≤ C √p / W`.

`fluctBound_all`: `FluctBound κ J` for every `J` (from `CavityLayerUniform`, i.e. from
the cavity-mean lemma, and the b-uniform deterministic stability `cavityStability_uniform`).

## Method

Instead of gluing bounded scattering matrices, we induct on the layers with the global conditional
map of the cavity-mean lemma. With `Ψ(X) = E(h₊ | X)`:
`h_{J+1} - E h_{J+1} = (h_{J+1} - Ψ(X_J)) + (Ψ(X_J) - E Ψ(X_J))`. The first term is the
conditional fluctuation (`≤ C√p/W`). For the second, `|Ψ(X) - u(X)| ≤ C/W²` and the deterministic
stability of the cavity equations compares `u(X)` with `ũ = u(X̃)` for one fixed realization
`X̃ = X_J(x₀)`: `|u(X) - ũ| ≤ C_s |f_X(ζ̃) - f_{X̃}(ζ̃)|` at the deterministic point
`ζ̃ = -e - c ṽ - b ũ` (a fixed compact region of the upper half-plane). Writing
`f_X - f_{X̃} = (f_X - E f) - (f_{X̃} - E f)`, the first part is the induction hypothesis at `ζ̃`,
and the second is at most a fixed multiple of the circle average `Φ(x₀)` of `|f_{X_J} - E f|`
(Cauchy's formula on one circle enclosing the region, `norm_le_circleAvg`); `x₀` is chosen with
`Φ(x₀) ≤ E Φ ≤ 2π C√2/W` (first moment method). No constant depends on `D`.
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

/-- The concentration bound after `J` layers, uniform in the domain, the compact parameter set and
the Hermitian initial matrix. -/
def FluctBound (κ : ℝ) (J : ℕ) : Prop :=
  ∀ η M : ℝ, 0 < η → ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ W : ℕ, 0 < W → ∀ b e : ℝ, zeParam κ b e →
    ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ∀ z' : ℂ, η ≤ z'.im → ‖z'‖ ≤ M →
      ∀ p : ℝ, 2 ≤ p → p ≤ a * W →
        eLpNorm (fun ω => zeTrace e D J z' ω - ∫ ω', zeTrace e D J z' ω' ∂oneEndedLaw W b J)
          (ENNReal.ofReal p) (oneEndedLaw W b J) ≤ ENNReal.ofReal (C * Real.sqrt p / W)

/-!
## Deterministic cavity facts
-/

section Cavity

variable {W : ℕ}

theorem zeParam_facts {κ b e : ℝ} (hκ : 0 < κ) (h : zeParam κ b e) :
    0 < b ∧ b < 1 / 2 ∧ b ≤ 1 ∧ κ ≤ 1 - 2 * b ∧ 1 - 2 * b ≤ 1 ∧ |e| ≤ 2 ∧ e ^ 2 ≤ 4 := by
  obtain ⟨h1, h2, h3⟩ := h
  have he : e ^ 2 ≤ 4 := by linarith
  refine ⟨by linarith, by linarith, by linarith, h2, by linarith, ?_, he⟩
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (e + 2), sq_nonneg (e - 2)]

/-- The cavity argument `ζ = -e - c v - b u` of the exact matrix solution. -/
def cavArg {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (b e : ℝ) (z' : ℂ) : ℂ :=
  -(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * cavityV X b e z' - (b : ℂ) * cavityU X b e z'

/-- The lower bound `a_* = (M + κ^{-1/2} + 1)⁻¹` for the port value. -/
def astarK (κ M : ℝ) : ℝ := 1 / (M + 1 / Real.sqrt κ + 1)

/-- A-priori bounds of the exact cavity solution (as in `cavity_apriori_bounds`), uniform on
the compact parameter set. -/
theorem cavity_apriori {κ : ℝ} (hκ : 0 < κ) (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {b e : ℝ} (hbe : zeParam κ b e) {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    {z' : ℂ} (hz : η ≤ z'.im) (hzM : ‖z'‖ ≤ M) :
    cavityV X b e z' = normalizedResolventTrace X (cavArg X b e z') ∧
      cavityU X b e z' = (z' - b * cavityV X b e z')⁻¹ ∧
      (cavityV X b e z').im < 0 ∧ astarK κ M ≤ ‖cavityU X b e z'‖ ∧
      η * ‖cavityU X b e z'‖ ^ 2 ≤ -(cavityU X b e z').im ∧
      min κ 1 * η * astarK κ M ^ 2 ≤ (cavArg X b e z').im ∧
      ‖cavArg X b e z'‖ ≤ 2 + 1 / Real.sqrt κ + 1 / η := by
  obtain ⟨hb0, hb1, hb1', hcκ, hc1, he2, he4⟩ := zeParam_facts hκ hbe
  have hc : 0 < 1 - 2 * b := by linarith
  have hz0 : 0 < z'.im := hη.trans_le hz
  have hsol := cavitySol_spec hW hX hb0 hb1 e hz0
  have hsolW := (isCavityMatrixSolution_iff hX hb0 hc).mp hsol
  obtain ⟨hvA, hAc, hu1, hu2⟩ := cavity_apriori_bounds (isCavityWeights_uniform hW) hb0 hc hη hz
    hzM hsolW
  obtain ⟨h1, h2, hv, hu⟩ := hsol
  set v := cavityV X b e z'
  set u := cavityU X b e z'
  have hsc : Real.sqrt κ ≤ Real.sqrt (1 - 2 * b) := Real.sqrt_le_sqrt hcκ
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hv1 : ‖v‖ ≤ 1 / Real.sqrt κ := by
    have hv2 : ‖v‖ ^ 2 ≤ 1 / (1 - 2 * b) := hvA.trans hAc
    have : ‖v‖ ≤ 1 / Real.sqrt (1 - 2 * b) := by
      rw [← Real.sqrt_sq (norm_nonneg v), one_div, ← Real.sqrt_inv]
      exact Real.sqrt_le_sqrt (by rw [← one_div]; exact hv2)
    exact this.trans (one_div_le_one_div_of_le hsκ hsc)
  have hbsc : b / Real.sqrt (1 - 2 * b) ≤ 1 / Real.sqrt κ := by
    calc b / Real.sqrt (1 - 2 * b) ≤ 1 / Real.sqrt (1 - 2 * b) :=
          div_le_div_of_nonneg_right hb1' (Real.sqrt_nonneg _)
      _ ≤ 1 / Real.sqrt κ := one_div_le_one_div_of_le hsκ hsc
  have hast : astarK κ M ≤ ‖u‖ := by
    refine le_trans ?_ hu1
    unfold astarK
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hport : η * ‖u‖ ^ 2 ≤ -u.im := by
    have hpf := CavityMean.port_facts hb0.le hη hz hv.le
    have hu' : u = cavityPort b z' v := h2
    rw [hu', hpf.2.1]
    nlinarith [hpf.1, sq_nonneg ‖cavityPort b z' v‖]
  have harg : (cavArg X b e z').im = (1 - 2 * b) * (-v.im) + b * (-u.im) := by
    unfold cavArg; simp; ring
  refine ⟨h1, h2, hv, hast, hport, ?_, ?_⟩
  · rw [harg]
    have ha0 : 0 ≤ astarK κ M := by unfold astarK; positivity
    have e1 : min κ 1 * η * astarK κ M ^ 2 ≤ b * (η * ‖u‖ ^ 2) := by
      have : min κ 1 ≤ b := (min_le_left _ _).trans hbe.1
      have h3 : astarK κ M ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ ha0 hast 2
      calc min κ 1 * η * astarK κ M ^ 2 = min κ 1 * (η * astarK κ M ^ 2) := by ring
        _ ≤ b * (η * ‖u‖ ^ 2) := by
            gcongr
    have e2 : b * (η * ‖u‖ ^ 2) ≤ b * (-u.im) := mul_le_mul_of_nonneg_left hport hb0.le
    have e3 : 0 ≤ (1 - 2 * b) * (-v.im) := mul_nonneg hc.le (by linarith)
    linarith
  · unfold cavArg
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hb0.le]
    have e1 : (1 - 2 * b) * ‖v‖ ≤ 1 / Real.sqrt κ := by
      calc (1 - 2 * b) * ‖v‖ ≤ 1 * ‖v‖ := by gcongr
        _ ≤ 1 / Real.sqrt κ := by rw [one_mul]; exact hv1
    have e2 : b * ‖u‖ ≤ 1 / η := by
      calc b * ‖u‖ ≤ 1 * ‖u‖ := by gcongr
        _ ≤ 1 / η := by rw [one_mul]; exact hu2
    linarith

/-- The b-uniform stability constant, packaged. -/
def StabProp (κ η M astar C : ℝ) : Prop :=
  ∀ b : ℝ, κ ≤ b → κ ≤ 1 - 2 * b →
    ∀ (ι : Type) [Fintype ι] (p x : ι → ℝ) (e : ℝ) (z' v u vbar ubar : ℂ) (ε : ℝ),
      IsCavityWeights p → η ≤ z'.im → ‖z'‖ ≤ M →
      IsCavitySolution p x b (1 - 2 * b) e z' v u → vbar.im ≤ 0 → astar ≤ ‖ubar‖ →
      η * ‖ubar‖ ^ 2 ≤ -ubar.im →
      ‖vbar - cavityStieltjes p x (-e - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar)‖ ≤ ε →
      ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε →
      ‖vbar - v‖ + ‖ubar - u‖ ≤ C * ε

/-- Comparison of the exact cavity solution of `X` with an approximate pair `(v̄, ū)` that solves
the port equation exactly: `|u(X) - ū| ≤ C_s |v̄ - f_X(ζ̄)|`, `ζ̄ = -e - c v̄ - b ū`. -/
theorem cavity_compare {κ η M C : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hstab : StabProp κ η M (astarK κ M) C)
    (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) {b e : ℝ}
    (hbe : zeParam κ b e) {z' : ℂ} (hz : η ≤ z'.im) (hzM : ‖z'‖ ≤ M) {vbar ubar : ℂ}
    (hvb : vbar.im ≤ 0) (hua : astarK κ M ≤ ‖ubar‖) (hport : η * ‖ubar‖ ^ 2 ≤ -ubar.im)
    (hu : ubar = (z' - b * vbar)⁻¹)
    (hζ : (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar).im ≠ 0) :
    ‖cavityU X b e z' - ubar‖ ≤
      C * ‖vbar - normalizedResolventTrace X (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar)‖ := by
  obtain ⟨hb0, hb1, -, -, -, -, -⟩ := zeParam_facts hκ hbe
  have hc : 0 < 1 - 2 * b := by linarith
  have hsol := cavitySol_spec hW hX hb0 hb1 e (hη.trans_le hz)
  have hsolW := (isCavityMatrixSolution_iff hX hb0 hc).mp hsol
  have h1 : ‖vbar - cavityStieltjes (fun _ => (W : ℝ)⁻¹) hX.eigenvalues
      (-e - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar)‖ ≤
      ‖vbar - normalizedResolventTrace X (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar)‖ := by
    rw [normalizedResolventTrace_eq hX hζ]
  have h2 : ‖ubar - (z' - b * vbar)⁻¹‖ ≤
      ‖vbar - normalizedResolventTrace X (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar)‖ := by
    rw [← hu, sub_self, norm_zero]; exact norm_nonneg _
  have := hstab b hbe.1 hbe.2.1 (Fin W) _ _ e z' _ _ vbar ubar _ (isCavityWeights_uniform hW)
    hz hzM hsolW hvb hua hport h1 h2
  rw [norm_sub_rev]
  linarith [norm_nonneg (vbar - cavityV X b e z')]

end Cavity

/-!
## Layer plumbing
-/

section Plumb

variable {W : ℕ}

/-- The next normalized trace as a function of (past, fresh layer). -/
def nextG (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (z' : ℂ)
    (q : (Fin J → OneEndedLayer W) × OneEndedLayer W) : ℂ :=
  cavityHplus e (oneEndedX e D J q.1) z' q.2

theorem measurable_nextG (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (z' : ℂ) :
    Measurable (nextG e D J z') := by
  have h1 : Measurable (fun q : (Fin J → OneEndedLayer W) × OneEndedLayer W =>
      (oneEndedX e D J q.1, q.2)) :=
    ((measurable_X e D J).comp measurable_fst).prodMk measurable_snd
  have h2 := (measurable_freshSchur_joint (W := W) e).comp h1
  have h3 := (measurable_nrt_joint (W := W)).comp
    (h2.prodMk (measurable_const : Measurable (fun _ : (Fin J → OneEndedLayer W) ×
      OneEndedLayer W => z')))
  unfold nextG cavityHplus
  exact h3

theorem zeTrace_succ_eq (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (z' : ℂ) :
    zeTrace e D (J + 1) z' = fun ω => nextG e D J z' (Fin.init ω, ω (Fin.last J)) :=
  rfl

theorem ae_prod_herm (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ} (hD : D.IsHermitian) (J : ℕ) :
    ∀ᵐ q ∂((oneEndedLaw W b J).prod (freshLaw W b)),
      (oneEndedX e D J q.1).IsHermitian ∧ (freshSchur e (oneEndedX e D J q.1) q.2).IsHermitian := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := oneEndedLaw W b J)
    (ν := freshLaw W b)).ae (ae_X_isHermitian b e hD J)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := oneEndedLaw W b J)
    (ν := freshLaw W b)).ae (BlockBand.Layers.lct_ae_blocks_isHermitian W b .oneBlockOnePort)
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, CavityMeanProb.freshSchur_isHermitian e hq1 _ hq2⟩

theorem integrable_nextG (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) {z' : ℂ} (hz : 0 < z'.im) :
    Integrable (nextG e D J z') ((oneEndedLaw W b J).prod (freshLaw W b)) := by
  refine Integrable.of_bound (measurable_nextG e D J z').aestronglyMeasurable (1 / z'.im) ?_
  filter_upwards [ae_prod_herm b e hD J] with q hq
  exact CavityMeanProb.norm_cavityHplus_le hW e hq.2 hz

/-- The conditional mean `Ψ(x) = E(h_{J+1} | past = x)`. -/
def condMean (b e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (z' : ℂ)
    (x : Fin J → OneEndedLayer W) : ℂ :=
  ∫ y, cavityHplus e (oneEndedX e D J x) z' y ∂freshLaw W b

theorem stronglyMeasurable_condMean (b e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (z' : ℂ) :
    StronglyMeasurable (condMean b e D J z') :=
  (measurable_nextG e D J z').stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)

theorem integrable_condMean (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) {z' : ℂ} (hz : 0 < z'.im) :
    Integrable (condMean b e D J z') (oneEndedLaw W b J) := by
  refine Integrable.of_bound (stronglyMeasurable_condMean b e D J z').aestronglyMeasurable
    (1 / z'.im) ?_
  filter_upwards [ae_X_isHermitian b e hD J] with x hx
  refine norm_integral_le_of_norm_le_const ?_ |>.trans (by rw [probReal_univ, mul_one])
  filter_upwards [CavityMeanProb.ae_freshSchur_isHermitian W b e hx] with y hy
  exact CavityMeanProb.norm_cavityHplus_le hW e hy hz

theorem integral_zeTrace_succ (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) {z' : ℂ} (hz : 0 < z'.im) :
    ∫ ω, zeTrace e D (J + 1) z' ω ∂oneEndedLaw W b (J + 1) =
      ∫ x, condMean b e D J z' x ∂oneEndedLaw W b J := by
  rw [zeTrace_succ_eq]
  exact integral_initLast (freshLaw W b) J (integrable_nextG hW b e hD J hz)

/-- The mean `f̄(ζ) = E h_J(ζ)`. -/
def meanTrace (b e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (ζ : ℂ) : ℂ :=
  ∫ ω, zeTrace e D J ζ ω ∂oneEndedLaw W b J

/-- `f̄` is holomorphic on the upper half-plane (it is the Stieltjes transform of the expected
empirical law). -/
theorem meanTrace_differentiableOn (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) :
    DifferentiableOn ℂ (meanTrace b e D J) {ζ : ℂ | 0 < ζ.im} := by
  obtain ⟨ν, hν, hG⟩ := exists_expectedSpectral (oneEndedLaw W b J) hW (measurable_X e D J)
    (ae_X_isHermitian b e hD J)
  refine (stieltjesG_differentiableOn ν).congr fun ζ hζ => ?_
  rw [hG ζ hζ]; rfl

theorem norm_meanTrace_le (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) {ζ : ℂ} (hζ : 0 < ζ.im) : ‖meanTrace b e D J ζ‖ ≤ 1 / ζ.im := by
  unfold meanTrace
  refine norm_integral_le_of_norm_le_const ?_ |>.trans (by rw [probReal_univ, mul_one])
  exact ae_norm_zeTrace_le hW b e hD J hζ

end Plumb

/-!
## The induction
-/

theorem fluctBound_zero (κ : ℝ) : FluctBound κ 0 := by
  intro η M hη
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro W hW b e hbe D hD z' hz hzM p hp2 hpa
  have h0 : (fun ω => zeTrace e D 0 z' ω - ∫ ω', zeTrace e D 0 z' ω' ∂oneEndedLaw W b 0) =
      fun _ => 0 := by
    funext ω
    have : ∀ ω' : Fin 0 → OneEndedLayer W, zeTrace e D 0 z' ω' = normalizedResolventTrace D z' :=
      fun ω' => rfl
    simp only [this, integral_const, probReal_univ, one_smul, sub_self]
  rw [h0, eLpNorm_fun_zero]
  exact zero_le

/-- `‖F‖_{L¹} ≤ ‖F‖_{L²}` in real form. -/
theorem integral_norm_le_of_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Ω → ℂ} (hF : AEStronglyMeasurable F μ) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm F (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal B) : ∫ x, ‖F x‖ ∂μ ≤ B := by
  rw [integral_norm_eq_lintegral_enorm hF, ← eLpNorm_one_eq_lintegral_enorm]
  have h1 : eLpNorm F 1 μ ≤ eLpNorm F (ENNReal.ofReal 2) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.mpr (by norm_num))
  · have := h1.trans h
    exact (ENNReal.toReal_le_of_le_ofReal hB this)
  · exact hF

theorem fluctBound_succ (hU : CavityLayerUniform) {κ : ℝ} (hκ : 0 < κ) {J : ℕ}
    (ih : FluctBound κ J) : FluctBound κ (J + 1) := by
  intro η M hη
  set Mp := max M 0 with hMpdef
  have hMp : 0 ≤ Mp := le_max_right _ _
  set ast := astarK κ Mp with hastdef
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hast : 0 < ast := by rw [hastdef]; unfold astarK; positivity
  have hast1 : ast ≤ 1 := by
    rw [hastdef]; unfold astarK
    rw [div_le_one (by positivity)]
    have : 0 ≤ 1 / Real.sqrt κ := by positivity
    linarith
  set sbar := min κ 1 * η * ast ^ 2 with hsbar
  set R' := 2 + 1 / Real.sqrt κ + 1 / η + Mp + η with hR'
  have hs0 : 0 < sbar := by
    have : 0 < min κ 1 := lt_min hκ one_pos
    positivity
  have hsR : sbar ≤ R' := by
    have h1 : min κ 1 ≤ 1 := min_le_right _ _
    have h2 : ast ^ 2 ≤ 1 := by nlinarith
    have h3 : sbar ≤ η := by
      have : 0 ≤ min κ 1 := (lt_min hκ one_pos).le
      calc sbar = min κ 1 * (η * ast ^ 2) := by ring
        _ ≤ 1 * (η * 1) := by gcongr
        _ = η := by ring
    have : 0 ≤ 1 / Real.sqrt κ := by positivity
    have : 0 ≤ 1 / η := by positivity
    linarith
  obtain ⟨a₀, CQ, ha₀, hCQ, hUQ⟩ := hU κ hκ η Mp hη
  obtain ⟨Cs, hCs0, hCs⟩ := cavityStability_uniform hκ hη hMp hast
  obtain ⟨c₀, ρ₁, ρ, η', M', hρ₁, hρ, hη', hη's, hRM', hin, hball⟩ := exists_circle hs0 hsR
  obtain ⟨a₁, C₁, ha₁, hC₁, hih⟩ := ih η' M' hη'
  have hρ0 : 0 < ρ := hρ₁.trans_lt hρ
  set K := ρ / (ρ - ρ₁) * (2 * π)⁻¹ with hKdef
  have hK : 0 ≤ K := by
    have : 0 < ρ - ρ₁ := by linarith
    positivity
  refine ⟨min a₀ a₁, 3 * CQ + 2 * Cs * C₁ + 4 * π * Cs * K * C₁ + 1, lt_min ha₀ ha₁,
    by positivity, ?_⟩
  intro W hW b e hbe D hD z' hz hzM p hp2 hpa
  have hzMp : ‖z'‖ ≤ Mp := hzM.trans (le_max_left _ _)
  have hz0 : 0 < z'.im := hη.trans_le hz
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hpa₀ : p ≤ a₀ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le)
  have hpa₁ : p ≤ a₁ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
  have h2a₁ : (2 : ℝ) ≤ a₁ * W := hp2.trans hpa₁
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsqp : 1 ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by linarith)
  have hsq2 : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt hp2
  set P := oneEndedLaw W b J with hPdef
  set fbar := meanTrace b e D J with hfbar
  -- sphere facts
  have hsph : ∀ θ : ℝ, η' ≤ (circleMap c₀ ρ θ).im ∧ ‖circleMap c₀ ρ θ‖ ≤ M' := fun θ =>
    hball _ (sphere_subset_closedBall (circleMap_mem_sphere c₀ hρ0.le θ))
  have hball_im : ∀ w ∈ closedBall c₀ ρ, w ∈ {ζ : ℂ | 0 < ζ.im} := fun w hw =>
    hη'.trans_le (hball w hw).1
  have hfbar_d := meanTrace_differentiableOn hW b e hD J
  have hfbar_c : Continuous (fun θ : ℝ => fbar (circleMap c₀ ρ θ)) :=
    hfbar_d.continuousOn.comp_continuous (continuous_circleMap c₀ ρ) fun θ =>
      hη'.trans_le (hsph θ).1
  -- the circle integrand
  set H : (Fin J → OneEndedLayer W) × ℝ → ℝ := fun q =>
    ‖zeTrace e D J (circleMap c₀ ρ q.2) q.1 - fbar (circleMap c₀ ρ q.2)‖ with hHdef
  have hHm : Measurable H := by
    have h1 : Measurable (fun q : (Fin J → OneEndedLayer W) × ℝ =>
        zeTrace e D J (circleMap c₀ ρ q.2) q.1) := by
      have h0 := (measurable_zeTrace_joint e D J).comp
        (f := fun q : (Fin J → OneEndedLayer W) × ℝ => (circleMap c₀ ρ q.2, q.1))
        (((continuous_circleMap c₀ ρ).measurable.comp measurable_snd).prodMk measurable_fst)
      simpa only [Function.comp_def] using h0
    exact (h1.sub (hfbar_c.measurable.comp measurable_snd)).norm
  have hHb : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * π)))), ‖H q‖ ≤ 2 / η' := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := volume.restrict (Set.Ioc (0 : ℝ) (2 * π)))).ae (ae_X_isHermitian b e hD J)] with q hq
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have hw := hsph q.2
    have hwi : 0 < (circleMap c₀ ρ q.2).im := hη'.trans_le hw.1
    refine (norm_sub_le _ _).trans ?_
    have e1 := norm_zeTrace_le hW e hq hwi
    have e2 := norm_meanTrace_le hW b e hD J hwi
    have e3 : 1 / (circleMap c₀ ρ q.2).im ≤ 1 / η' := one_div_le_one_div_of_le hη' hw.1
    have : 2 / η' = 1 / η' + 1 / η' := by ring
    linarith
  have hHint : Integrable H (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * π)))) :=
    Integrable.of_bound hHm.aestronglyMeasurable (2 / η') hHb
  set Φ : (Fin J → OneEndedLayer W) → ℝ := fun x =>
    ∫ θ in Set.Ioc (0 : ℝ) (2 * π), H (x, θ) with hΦdef
  have hΦint : Integrable Φ P := hHint.integral_prod_left
  -- `E H(·, θ) ≤ C₁ √2 / W`
  have hEH : ∀ θ : ℝ, ∫ x, H (x, θ) ∂P ≤ C₁ * Real.sqrt 2 / W := by
    intro θ
    have hb := hih W hW b e hbe D hD (circleMap c₀ ρ θ) (hsph θ).1 (hsph θ).2 2 le_rfl h2a₁
    have hm : AEStronglyMeasurable (fun ω => zeTrace e D J (circleMap c₀ ρ θ) ω -
        ∫ ω', zeTrace e D J (circleMap c₀ ρ θ) ω' ∂oneEndedLaw W b J) P :=
      ((measurable_zeTrace e D J _).sub_const _).aestronglyMeasurable
    have := integral_norm_le_of_eLpNorm_two hm (by positivity) hb
    exact this
  have hEΦ : ∫ x, Φ x ∂P ≤ 2 * π * (C₁ * Real.sqrt 2 / W) := by
    rw [hΦdef, integral_integral_swap hHint]
    calc ∫ θ in Set.Ioc (0 : ℝ) (2 * π), ∫ x, H (x, θ) ∂P
        ≤ ∫ _θ in Set.Ioc (0 : ℝ) (2 * π), C₁ * Real.sqrt 2 / W := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ =>
            integral_nonneg fun x => norm_nonneg _) (integrable_const _)
            (Filter.Eventually.of_forall hEH)
      _ = 2 * π * (C₁ * Real.sqrt 2 / W) := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
            ENNReal.toReal_ofReal Real.two_pi_pos.le, smul_eq_mul]
  -- the reference realization
  have hN : P {x | ¬ (oneEndedX e D J x).IsHermitian} = 0 := by
    have := ae_X_isHermitian b e hD J (W := W)
    rwa [ae_iff] at this
  obtain ⟨x₀, hx₀N, hx₀Φ⟩ := exists_notMem_null_le_integral hΦint hN
  have hX₀ : (oneEndedX e D J x₀).IsHermitian := by
    simpa using hx₀N
  set X₀ := oneEndedX e D J x₀ with hX₀def
  obtain ⟨hv₀, hu₀, hv₀im, hu₀a, hu₀port, hζ₀im, hζ₀n⟩ :=
    cavity_apriori hκ hW hX₀ hbe hη hMp hz hzMp
  set v₀ := cavityV X₀ b e z'
  set u₀ := cavityU X₀ b e z'
  set ζ₀ := cavArg X₀ b e z' with hζ₀def
  have hζ₀R : ‖ζ₀‖ ≤ R' := by
    have : 0 ≤ Mp + η := by linarith
    linarith
  have hζ₀c : ‖ζ₀ - c₀‖ ≤ ρ₁ := hin ζ₀ hζ₀im hζ₀R
  have hζ₀pos : 0 < ζ₀.im := hs0.trans_le hζ₀im
  -- Cauchy bound at the reference realization
  set F₀ : ℂ → ℂ := fun w => zeTrace e D J w x₀ - fbar w with hF₀def
  have hF₀d : DifferentiableOn ℂ F₀ (closedBall c₀ ρ) := by
    have h1 : DifferentiableOn ℂ (fun w => zeTrace e D J w x₀) {ζ : ℂ | 0 < ζ.im} :=
      CavityMeanProb.normalizedResolventTrace_differentiableOn hX₀
    exact (h1.sub hfbar_d).mono hball_im
  have hF₀ : ‖F₀ ζ₀‖ ≤ K * Φ x₀ := by
    have := norm_le_circleAvg hρ hF₀d hζ₀c
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le] at this
    rw [hKdef, mul_assoc]
    exact this
  -- pointwise comparison
  set α : ℝ := CQ / (W : ℝ) ^ 2 + Cs * K * Φ x₀ with hαdef
  set Fz : (Fin J → OneEndedLayer W) → ℂ := fun x => zeTrace e D J ζ₀ x - fbar ζ₀ with hFzdef
  have hpt : ∀ᵐ x ∂P, ‖condMean b e D J z' x - u₀‖ ≤ α + ‖(Cs : ℂ) • Fz x‖ := by
    filter_upwards [ae_X_isHermitian b e hD J] with x hx
    have hQ := (hUQ b hbe.1 hbe.2.1 W hW (oneEndedX e D J x) hx e z' hz hzMp).1
    have hne : (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v₀ - b * u₀).im ≠ 0 := ne_of_gt hζ₀pos
    have hcmp := cavity_compare hκ hη hCs hW hx hbe hz hzMp hv₀im.le hu₀a hu₀port hu₀ hne
    have hdiff : v₀ - normalizedResolventTrace (oneEndedX e D J x)
        (-(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v₀ - b * u₀) = F₀ ζ₀ - Fz x := by
      nth_rewrite 1 [hv₀]
      show normalizedResolventTrace X₀ ζ₀ - normalizedResolventTrace (oneEndedX e D J x) ζ₀ =
        (zeTrace e D J ζ₀ x₀ - fbar ζ₀) - (zeTrace e D J ζ₀ x - fbar ζ₀)
      rw [sub_sub_sub_cancel_right]; rfl
    rw [hdiff] at hcmp
    have hFF : ‖F₀ ζ₀ - Fz x‖ ≤ K * Φ x₀ + ‖Fz x‖ :=
      by linarith [norm_sub_le (F₀ ζ₀) (Fz x)]
    have hW2 : CQ / (W : ℝ) ^ 2 = CQ / (W : ℝ) ^ 2 := rfl
    clear hW2
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hCs0.le]
    calc ‖condMean b e D J z' x - u₀‖
        ≤ ‖condMean b e D J z' x - cavityU (oneEndedX e D J x) b e z'‖ +
            ‖cavityU (oneEndedX e D J x) b e z' - u₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ CQ / (W : ℝ) ^ 2 + Cs * (K * Φ x₀ + ‖Fz x‖) := by
          gcongr
          · exact hQ
          · exact hcmp.trans (mul_le_mul_of_nonneg_left hFF hCs0.le)
      _ = α + Cs * ‖Fz x‖ := by rw [hαdef]; ring
  -- `L^p` bound for the conditional mean around `u₀`
  have hFzm : AEStronglyMeasurable Fz P :=
    ((measurable_zeTrace e D J ζ₀).sub_const _).aestronglyMeasurable
  have hB1 : eLpNorm (fun x => condMean b e D J z' x - u₀) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal |α| + ENNReal.ofReal Cs * ENNReal.ofReal (C₁ * Real.sqrt p / W) := by
    have hm : AEStronglyMeasurable (fun x => condMean b e D J z' x - u₀) P :=
      ((stronglyMeasurable_condMean b e D J z').sub stronglyMeasurable_const).aestronglyMeasurable
    refine (eLpNorm_mono_ae_real hm hpt).trans ?_
    refine (eLpNorm_add_le (f := fun _ => α) (g := fun x => ‖(Cs : ℂ) • Fz x‖) hp1).trans ?_
    rw [eLpNorm_const_prob P hp0 α]
    gcongr
    rw [eLpNorm_norm (fun x => (Cs : ℂ) • Fz x) (hFzm.const_smul (Cs : ℂ))]
    have hsm : (fun x => (Cs : ℂ) • Fz x) = (Cs : ℂ) • Fz := rfl
    have hCe : ‖(Cs : ℂ)‖ₑ = ENNReal.ofReal Cs := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hCs0.le]
    rw [hsm, eLpNorm_const_smul, hCe]
    gcongr
    have hζ₀M : ‖ζ₀‖ ≤ M' := hζ₀R.trans hRM'
    exact hih W hW b e hbe D hD ζ₀ (hη's.trans hζ₀im) hζ₀M p hp2 hpa₁
  have hB2 : eLpNorm (fun x => condMean b e D J z' x - ∫ x', condMean b e D J z' x' ∂P)
      (ENNReal.ofReal p) P ≤ 2 * eLpNorm (fun x => condMean b e D J z' x - u₀)
        (ENNReal.ofReal p) P :=
    eLpNorm_sub_integral_le_two_mul (integrable_condMean hW b e hD J hz0) (by linarith) u₀
  -- the conditional fluctuation
  have hA : eLpNorm (fun ω : Fin (J + 1) → OneEndedLayer W =>
      (fun q => nextG e D J z' q - condMean b e D J z' q.1) (Fin.init ω, ω (Fin.last J)))
      (ENNReal.ofReal p) (oneEndedLaw W b (J + 1)) ≤ ENNReal.ofReal |CQ * Real.sqrt p / W| := by
    have hGm : AEStronglyMeasurable (fun q : (Fin J → OneEndedLayer W) × OneEndedLayer W =>
        nextG e D J z' q - condMean b e D J z' q.1) (P.prod (freshLaw W b)) :=
      ((measurable_nextG e D J z').sub
        ((stronglyMeasurable_condMean b e D J z').measurable.comp measurable_fst)).aestronglyMeasurable
    refine (eLpNorm_initLast_le (freshLaw W b) J hGm hp0 (h := fun _ => CQ * Real.sqrt p / W)
      ?_).trans (le_of_eq (eLpNorm_const_prob P hp0 _))
    filter_upwards [ae_X_isHermitian b e hD J] with x hx
    exact (hUQ b hbe.1 hbe.2.1 W hW (oneEndedX e D J x) hx e z' hz hzMp).2 p hp2 hpa₀
  -- assemble
  have hmean := integral_zeTrace_succ hW b e hD J hz0
  have hsplit : (fun ω => zeTrace e D (J + 1) z' ω -
      ∫ ω', zeTrace e D (J + 1) z' ω' ∂oneEndedLaw W b (J + 1)) =
      (fun ω : Fin (J + 1) → OneEndedLayer W =>
        (fun q => nextG e D J z' q - condMean b e D J z' q.1) (Fin.init ω, ω (Fin.last J))) +
      (fun ω => condMean b e D J z' (Fin.init ω) - ∫ x', condMean b e D J z' x' ∂P) := by
    rw [hmean]; funext ω; simp only [Pi.add_apply]; rw [zeTrace_succ_eq]; ring
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans ?_
  have hBtr : eLpNorm (fun ω : Fin (J + 1) → OneEndedLayer W =>
      condMean b e D J z' (Fin.init ω) - ∫ x', condMean b e D J z' x' ∂P) (ENNReal.ofReal p)
      (oneEndedLaw W b (J + 1)) = eLpNorm (fun x => condMean b e D J z' x -
        ∫ x', condMean b e D J z' x' ∂P) (ENNReal.ofReal p) P :=
    eLpNorm_init_eq (freshLaw W b) J (g := fun x => condMean b e D J z' x -
      ∫ x', condMean b e D J z' x' ∂P)
      ((stronglyMeasurable_condMean b e D J z').sub stronglyMeasurable_const).aestronglyMeasurable _
  rw [hBtr]
  -- real arithmetic
  have hΦ0 : 0 ≤ Φ x₀ := setIntegral_nonneg measurableSet_Ioc fun θ _ => norm_nonneg _
  have hα0 : 0 ≤ α := by positivity
  have hfin : ENNReal.ofReal |CQ * Real.sqrt p / W| +
      2 * (ENNReal.ofReal |α| + ENNReal.ofReal Cs * ENNReal.ofReal (C₁ * Real.sqrt p / W)) =
      ENNReal.ofReal (CQ * Real.sqrt p / W + 2 * (α + Cs * (C₁ * Real.sqrt p / W))) := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg hα0, ← ENNReal.ofReal_mul hCs0.le,
      ← ENNReal.ofReal_add hα0 (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc _ ≤ ENNReal.ofReal |CQ * Real.sqrt p / W| +
        2 * (ENNReal.ofReal |α| + ENNReal.ofReal Cs * ENNReal.ofReal (C₁ * Real.sqrt p / W)) := by
        gcongr
        exact hB2.trans (by gcongr)
    _ = _ := hfin
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : CQ / (W : ℝ) ^ 2 ≤ CQ * Real.sqrt p / W := by
          have h1 : CQ / (W : ℝ) ^ 2 ≤ CQ / W :=
            div_le_div_of_nonneg_left hCQ.le hWr (le_self_pow₀ hW1 two_ne_zero)
          have h2 : CQ / (W : ℝ) ≤ CQ * Real.sqrt p / W :=
            div_le_div_of_nonneg_right (le_mul_of_one_le_right hCQ.le hsqp) hWr.le
          exact h1.trans h2
        have e2 : Cs * K * Φ x₀ ≤ 2 * π * Cs * K * C₁ * Real.sqrt p / W := by
          have h1 : Φ x₀ ≤ 2 * π * (C₁ * Real.sqrt 2 / W) := hx₀Φ.trans hEΦ
          have h2 : 2 * π * (C₁ * Real.sqrt 2 / W) ≤ 2 * π * (C₁ * Real.sqrt p / W) := by
            gcongr
          calc Cs * K * Φ x₀ ≤ Cs * K * (2 * π * (C₁ * Real.sqrt p / W)) := by
                gcongr; exact h1.trans h2
            _ = 2 * π * Cs * K * C₁ * Real.sqrt p / W := by ring
        have e3 : 0 ≤ Real.sqrt p / W := by positivity
        have : CQ * Real.sqrt p / W + 2 * (α + Cs * (C₁ * Real.sqrt p / W)) ≤
            (3 * CQ + 2 * Cs * C₁ + 4 * π * Cs * K * C₁) * Real.sqrt p / W := by
          rw [hαdef]
          have : (3 * CQ + 2 * Cs * C₁ + 4 * π * Cs * K * C₁) * Real.sqrt p / W =
              CQ * Real.sqrt p / W + 2 * (CQ * Real.sqrt p / W +
                2 * π * Cs * K * C₁ * Real.sqrt p / W + Cs * (C₁ * Real.sqrt p / W)) := by ring
          rw [this]; linarith
        refine this.trans ?_
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith) e3

/-- **Concentration after every fixed number of layers** (the zero-entrance lemma):
`FluctBound κ J` for every `J`, uniform in the Hermitian initial matrix `D`. -/
theorem fluctBound_all (hU : CavityLayerUniform) {κ : ℝ} (hκ : 0 < κ) (J : ℕ) :
    FluctBound κ J := by
  induction J with
  | zero => exact fluctBound_zero κ
  | succ J ih => exact fluctBound_succ hU hκ ih

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
