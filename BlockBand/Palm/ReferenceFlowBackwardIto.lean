module

public import BlockBand.Palm.ReferenceFlowBackwardComp
public import BlockBand.Palm.ReferenceFlowItoMean
public import BlockBand.Palm.ReferenceFlowKernel
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Backward equation of the reference flow: cutoff, Itô formula and the mean identity

The only hypothesis is Itô's formula `ItoFormulaFor`, used only in `isNativeItoProcess_comp`.

* Coefficients of the reflected flow (`driftC`, `noiseC`): continuity in time
  (`continuousOn_rotationDrift`, `continuousOn_rotationNoise`, `continuous_driftC`,
  `continuous_noiseC`).
* `exists_cutoff`: for `ρ₁ < 1` a smooth `χ ∈ [0,1]` with compact support in
  `{opNorm (nᴴ n) < 1}`, equal to `1` near `{opNorm (nᴴ n) ≤ ρ₁}`; `cutF χ f z = χ · Ftil f z` is
  globally `C²`, bounded and compactly supported; its Itô drift `driftFn` is uniformly bounded
  (`exists_driftFn_bound`, by compactness of the coefficient range times the support).
* `isNativeItoProcess_comp`: Itô's formula for `φ(𝓝_t)` with a time-independent `C²` test `φ`
  and a rotation flow `𝓝` (drift `Dφ(𝓝)[D𝓝] + ½ Σ_α D²φ(𝓝)[σ_α𝓝, σ_α𝓝]`).
* `hasDerivAt_mean_of_ito`: for a bounded real Itô process with bounded drift whose
  mean drift is continuous in time, `t ↦ E X_t` has derivative `E b_{t₀}` at every `t₀ > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow.Backward

open MeasureTheory Set Filter Topology Matrix BlockBand.Palm.ReferenceFlow
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow rotationNoise rotationDrift
  clampTime)
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

local instance (priority := high) frobUnifI {n : Type*} [Fintype n] :
    UniformSpace (Matrix n n ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℂ)).toUniformSpace

local instance (priority := high) frobTopI {n : Type*} [Fintype n] :
    TopologicalSpace (Matrix n n ℂ) :=
  (frobUnifI (n := n)).toTopologicalSpace

local instance bwBorelI {N : ℕ} : BorelSpace (Matrix (Fin N) (Fin N) ℂ) :=
  ⟨by exact (inferInstance : BorelSpace (Fin N → Fin N → ℂ)).measurable_eq⟩

variable {N p : ℕ}

/-!
## Coefficients
-/

theorem bwClampTime_mem {a c : ℝ} (hac : a ≤ c) (x : ℝ) : clampTime a c x ∈ Icc a c :=
  ⟨le_max_left _ _, max_le hac (min_le_right _ _)⟩

theorem bwContinuous_clampTime (a c : ℝ) : Continuous (clampTime a c) := by
  unfold clampTime; fun_prop

theorem bwClampTime_of_mem {a c x : ℝ} (hx : x ∈ Icc a c) : clampTime a c x = x := by
  unfold clampTime
  rw [min_eq_left hx.2, max_eq_right hx.1]

theorem continuousOn_rotationDrift {s : Set ℝ} {ρ : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    (hρ : ContinuousOn ρ s) (hκ : ContinuousOn κ s) :
    ContinuousOn (fun x => rotationDrift (ρ x) (κ x)) s := by
  have hρ' : ∀ k m, ContinuousOn (fun x => ρ x k m) s := fun k m =>
    (continuous_apply m).comp_continuousOn ((continuous_apply k).comp_continuousOn hρ)
  have hκ' : ∀ k, ContinuousOn (fun x => κ x k) s := fun k =>
    (continuous_apply k).comp_continuousOn hκ
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  simp only [rotationDrift, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
      ((continuousOn_finsetSum _ fun m _ => hρ' i m).add (hκ' i)))
  · simp only [hij, ite_false]
    exact continuousOn_const

theorem continuousOn_rotationNoise {s : Set ℝ} {ρ : ℝ → Fin N → Fin N → ℝ}
    (hρ : ContinuousOn ρ s) (α : RotIdx N) :
    ContinuousOn (fun x => rotationNoise (ρ x) α) s := by
  have hρ' : ∀ k m, ContinuousOn (fun x => ρ x k m) s := fun k m =>
    (continuous_apply m).comp_continuousOn ((continuous_apply k).comp_continuousOn hρ)
  unfold rotationNoise
  by_cases hα : α.1.1 < α.1.2
  · simp only [hα, ite_true]
    exact (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn
      ((hρ' _ _).div_const 2))).smul (continuousOn_const (c := if α.2 = 0 then
        BlockBand.Internal.Contracts.TransmissionFlow.rotX α.1.1 α.1.2 else
        BlockBand.Internal.Contracts.TransmissionFlow.rotY α.1.1 α.1.2))
  · simp only [hα, ite_false]
    exact continuousOn_const

/-- The drift coefficient of the reflected flow at time `t`. -/
def driftC (a c : ℝ) (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (t : ℝ≥0) :
    Matrix (Fin N) (Fin N) ℂ :=
  rotationDrift (reflectRate a c r (clampTime a c (a + t)))
    (reflectDamp a c κ (clampTime a c (a + t)))

/-- The noise coefficients of the reflected flow at time `t`. -/
def noiseC (a c : ℝ) (r : ℝ → Fin N → Fin N → ℝ) (α : RotIdx N) (t : ℝ≥0) :
    Matrix (Fin N) (Fin N) ℂ :=
  rotationNoise (reflectRate a c r (clampTime a c (a + t))) α

theorem continuous_driftC {a c : ℝ} (hac : a ≤ c) {r : ℝ → Fin N → Fin N → ℝ}
    {κ : ℝ → Fin N → ℝ} (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c)) :
    Continuous fun s : ℝ => driftC a c r κ s.toNNReal :=
  (continuousOn_rotationDrift (continuousOn_reflect hr) (continuousOn_reflect hκ)).comp_continuous
    ((bwContinuous_clampTime a c).comp (continuous_const.add
      (NNReal.continuous_coe.comp continuous_real_toNNReal))) fun _ => bwClampTime_mem hac _

theorem continuous_noiseC {a c : ℝ} (hac : a ≤ c) {r : ℝ → Fin N → Fin N → ℝ}
    (hr : ContinuousOn r (Icc a c)) (α : RotIdx N) :
    Continuous fun s : ℝ => noiseC a c r α s.toNNReal :=
  (continuousOn_rotationNoise (continuousOn_reflect hr) α).comp_continuous
    ((bwContinuous_clampTime a c).comp (continuous_const.add
      (NNReal.continuous_coe.comp continuous_real_toNNReal))) fun _ => bwClampTime_mem hac _

/-!
## The cutoff
-/

theorem opNorm_gram_eq (n : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (gram n) = ‖toOpCLM n‖ * ‖toOpCLM n‖ := by
  rw [opNorm, gram, map_mul, ← Matrix.star_eq_conjTranspose, map_star, toOpCLM_apply]
  exact CStarRing.norm_star_mul_self

theorem continuous_opNorm_gram : Continuous fun n : Matrix (Fin N) (Fin N) ℂ => opNorm (gram n) :=
  (continuous_norm.comp (toOpCLM (N := N)).continuous).comp contDiff_gram.continuous

theorem isCompact_opNorm_gram_le {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact {n : Matrix (Fin N) (Fin N) ℂ | opNorm (gram n) ≤ ρ} := by
  have hK : IsCompact ((ofOpCLM (N := N)) '' Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).image (ofOpCLM (N := N)).continuous
  refine hK.of_isClosed_subset (isClosed_le continuous_opNorm_gram continuous_const) ?_
  intro n hn
  refine ⟨toOpCLM n, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    have h := opNorm_gram_eq n
    have hn' : opNorm (gram n) ≤ ρ := hn
    nlinarith [norm_nonneg (toOpCLM n)]
  · rw [ofOpCLM_apply, toOpCLM_apply, StarAlgEquiv.symm_apply_apply]

/-- **The cutoff.** -/
theorem exists_cutoff {ρ₁ : ℝ} (hρ₁ : ρ₁ < 1) :
    ∃ χ : Matrix (Fin N) (Fin N) ℂ → ℝ, ContDiff ℝ 2 χ ∧ (∀ n, 0 ≤ χ n ∧ χ n ≤ 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ {n | opNorm (gram n) < 1} ∧
      ∀ n, opNorm (gram n) ≤ ρ₁ → χ =ᶠ[𝓝 n] fun _ => 1 := by
  set ρ₂ := (2 * ρ₁ + 1) / 3
  set ρ₃ := (ρ₁ + 2) / 3
  have h12 : ρ₁ < ρ₂ := by simp only [ρ₂]; linarith
  have h23 : ρ₂ < ρ₃ := by simp only [ρ₂, ρ₃]; linarith
  have h3 : ρ₃ < 1 := by simp only [ρ₃]; linarith
  obtain ⟨χ, hχd, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 2)
    (s := {n : Matrix (Fin N) (Fin N) ℂ | opNorm (gram n) < ρ₃})
    (t := {n : Matrix (Fin N) (Fin N) ℂ | opNorm (gram n) ≤ ρ₂})
    (isOpen_lt continuous_opNorm_gram continuous_const)
    (isClosed_le continuous_opNorm_gram continuous_const)
    (fun n (hn : opNorm (gram n) ≤ ρ₂) => show opNorm (gram n) < ρ₃ by linarith)
  have hts : tsupport χ ⊆ {n | opNorm (gram n) ≤ ρ₃} := by
    rw [tsupport, hχs]
    exact closure_minimal (fun n (hn : opNorm (gram n) < ρ₃) => le_of_lt hn)
      (isClosed_le continuous_opNorm_gram continuous_const)
  refine ⟨χ, hχd, fun n => hχr ⟨n, rfl⟩, ?_, ?_, ?_⟩
  · exact (isCompact_opNorm_gram_le h3).of_isClosed_subset (isClosed_tsupport χ) hts
  · exact fun n hn => lt_of_le_of_lt (hts hn) h3
  · intro n hn
    refine Filter.eventually_of_mem ((isOpen_lt continuous_opNorm_gram continuous_const).mem_nhds
      (show opNorm (gram n) < ρ₂ by linarith)) fun m (hm : opNorm (gram m) < ρ₂) => ?_
    exact (hχ1 m).1 (le_of_lt hm)

/-- The cut-off composite test `χ · Ftil f z`. -/
def cutF (χ : Matrix (Fin N) (Fin N) ℂ → ℝ) (f : RefState N p → ℝ) (z : RefState N p)
    (n : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  χ n * Ftil f z n

theorem contDiff_cutF {χ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hsupp : tsupport χ ⊆ {n | opNorm (gram n) < 1}) {C : ℝ} {f : RefState N p → ℝ}
    (hf : IsC2BoundedBy C f) (z : RefState N p) : ContDiff ℝ 2 (cutF χ f z) := by
  refine contDiff_iff_contDiffAt.2 fun n => ?_
  by_cases hn : opNorm (gram n) < 1
  · exact hχ.contDiffAt.mul (contDiffAt_Ftil hf z hn)
  · have h0 : χ =ᶠ[𝓝 n] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hn (hsupp h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with m hm
    simp [cutF, hm]

theorem abs_cutF_le {χ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hχ : ∀ n, 0 ≤ χ n ∧ χ n ≤ 1) {C : ℝ}
    {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) (z : RefState N p)
    (n : Matrix (Fin N) (Fin N) ℂ) : |cutF χ f z n| ≤ C := by
  rw [cutF, abs_mul, abs_of_nonneg (hχ n).1]
  have h := abs_gaussMean_le hf (g₀ z n)
  have hC : 0 ≤ C := (abs_nonneg _).trans h
  calc χ n * |Ftil f z n| ≤ 1 * C :=
        mul_le_mul (hχ n).2 h (abs_nonneg _) zero_le_one
    _ = C := one_mul C

theorem cutF_eventuallyEq {χ : Matrix (Fin N) (Fin N) ℂ → ℝ} {f : RefState N p → ℝ}
    {z : RefState N p} {n : Matrix (Fin N) (Fin N) ℂ} (h : χ =ᶠ[𝓝 n] fun _ => 1) :
    cutF χ f z =ᶠ[𝓝 n] Ftil f z := by
  filter_upwards [h] with m hm
  simp [cutF, hm]

/-- The Itô drift of `φ(𝓝)` as a function of the coefficients and the state. -/
def driftFn (φ : Matrix (Fin N) (Fin N) ℂ → ℝ) (D : Matrix (Fin N) (Fin N) ℂ)
    (σ : RotIdx N → Matrix (Fin N) (Fin N) ℂ) (n : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  fderiv ℝ φ n (D * n) + (1 / 2 : ℝ) * ∑ α : RotIdx N, fderiv ℝ (fderiv ℝ φ) n (σ α * n) (σ α * n)

theorem continuous_driftFn {φ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℂ × (RotIdx N → Matrix (Fin N) (Fin N) ℂ) ×
      Matrix (Fin N) (Fin N) ℂ => driftFn φ q.1 q.2.1 q.2.2 := by
  have h1c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have h2c : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hn : Continuous fun q : Matrix (Fin N) (Fin N) ℂ × (RotIdx N → Matrix (Fin N) (Fin N) ℂ) ×
      Matrix (Fin N) (Fin N) ℂ => q.2.2 := continuous_snd.comp continuous_snd
  have hσ : ∀ α, Continuous fun q : Matrix (Fin N) (Fin N) ℂ ×
      (RotIdx N → Matrix (Fin N) (Fin N) ℂ) × Matrix (Fin N) (Fin N) ℂ => q.2.1 α * q.2.2 :=
    fun α => by
      have h : Continuous fun q : Matrix (Fin N) (Fin N) ℂ ×
          (RotIdx N → Matrix (Fin N) (Fin N) ℂ) × Matrix (Fin N) (Fin N) ℂ => q.2.1 α :=
        (continuous_apply α).comp (continuous_fst.comp continuous_snd)
      exact h.matrix_mul hn
  have hD : Continuous fun q : Matrix (Fin N) (Fin N) ℂ ×
      (RotIdx N → Matrix (Fin N) (Fin N) ℂ) × Matrix (Fin N) (Fin N) ℂ => q.1 * q.2.2 :=
    continuous_fst.matrix_mul hn
  unfold driftFn
  exact ((h1c.comp hn).clm_apply hD).add (continuous_const.mul
    (continuous_finsetSum _ fun α _ => ((h2c.comp hn).clm_apply (hσ α)).clm_apply (hσ α)))

theorem driftFn_eq_zero {φ : Matrix (Fin N) (Fin N) ℂ → ℝ} {n : Matrix (Fin N) (Fin N) ℂ}
    (hn : n ∉ tsupport φ) (D : Matrix (Fin N) (Fin N) ℂ)
    (σ : RotIdx N → Matrix (Fin N) (Fin N) ℂ) : driftFn φ D σ n = 0 := by
  have h0 : φ =ᶠ[𝓝 n] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hn
  have h1 : fderiv ℝ φ =ᶠ[𝓝 n] fderiv ℝ (fun _ : Matrix (Fin N) (Fin N) ℂ => (0 : ℝ)) := h0.fderiv
  have h1' : fderiv ℝ φ n = 0 := by rw [h1.eq_of_nhds]; simp
  have h2 : fderiv ℝ (fderiv ℝ φ) n = 0 := by
    rw [h1.fderiv_eq]
    simp
  simp [driftFn, h1', h2]

/-- **Uniform bound on the Itô drift** of `φ(𝓝)` for compactly supported `φ`. -/
theorem exists_driftFn_bound {a c : ℝ} (hac : a ≤ c) {r : ℝ → Fin N → Fin N → ℝ}
    {κ : ℝ → Fin N → ℝ} (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    {φ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∃ M, ∀ (t : ℝ≥0) (n : Matrix (Fin N) (Fin N) ℂ),
      |driftFn φ (driftC a c r κ t) (fun α => noiseC a c r α t) n| ≤ M := by
  set cf : ℝ → Matrix (Fin N) (Fin N) ℂ × (RotIdx N → Matrix (Fin N) (Fin N) ℂ) := fun x =>
    (rotationDrift (reflectRate a c r x) (reflectDamp a c κ x),
      fun α => rotationNoise (reflectRate a c r x) α) with hcf
  have hcfc : ContinuousOn cf (Icc a c) :=
    (continuousOn_rotationDrift (continuousOn_reflect hr) (continuousOn_reflect hκ)).prodMk
      (continuousOn_pi.2 fun α => continuousOn_rotationNoise (continuousOn_reflect hr) α)
  have hK : IsCompact ((cf '' Icc a c) ×ˢ tsupport φ) :=
    (isCompact_Icc.image_of_continuousOn hcfc).prod hφc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun q => driftFn φ q.1.1 q.1.2 q.2)
    ((continuous_driftFn hφ).comp (continuous_fst.comp continuous_fst |>.prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).continuousOn
  refine ⟨max M 0, fun t n => ?_⟩
  by_cases hn : n ∈ tsupport φ
  · have hmem : ((driftC a c r κ t, fun α => noiseC a c r α t), n) ∈
        (cf '' Icc a c) ×ˢ tsupport φ :=
      ⟨⟨clampTime a c (a + t), bwClampTime_mem hac _, rfl⟩, hn⟩
    have h := hM _ hmem
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · rw [driftFn_eq_zero hn, abs_zero]
    exact le_max_right _ _

/-!
## Itô's formula for `φ(𝓝_t)`
-/

section ItoComp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_comp_snd_apply {φ : E → ℝ} (hφ : Differentiable ℝ φ) (q u : ℝ × E) :
    fderiv ℝ (fun q : ℝ × E => φ q.2) q u = fderiv ℝ φ q.2 u.2 := by
  have h := fderiv_comp_apply' (J := φ) (P := ContinuousLinearMap.snd ℝ ℝ E) (x := q) (hφ _)
    (ContinuousLinearMap.snd ℝ ℝ E).differentiableAt u
  rw [ContinuousLinearMap.fderiv] at h
  exact h

theorem timeDeriv_comp_snd [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} (hφ : Differentiable ℝ φ) (q : ℝ × E) :
    timeDeriv (fun q : ℝ × E => φ q.2) q = 0 := by
  unfold timeDeriv
  rw [fderiv_comp_snd_apply hφ]
  simp

theorem spaceDeriv_comp_snd [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} (hφ : Differentiable ℝ φ) (q : ℝ × E) (v : E) :
    spaceDeriv (fun q : ℝ × E => φ q.2) q v = fderiv ℝ φ q.2 v := by
  unfold spaceDeriv
  rw [fderiv_comp_snd_apply hφ]

theorem spaceDeriv2_comp_snd [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (q : ℝ × E) (v w : E) :
    spaceDeriv2 (fun q : ℝ × E => φ q.2) q v w = fderiv ℝ (fderiv ℝ φ) q.2 v w := by
  unfold spaceDeriv2
  have h := fderiv_fderiv_comp_apply (J := φ) (P := ContinuousLinearMap.snd ℝ ℝ E) (x := q)
    hφ.contDiffAt (ContinuousLinearMap.snd ℝ ℝ E).contDiff.contDiffAt (0, v) (0, w)
  rw [fderiv_fderiv_clm, ContinuousLinearMap.fderiv] at h
  simpa [Function.comp_def] using h

end ItoComp

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **Itô's formula for `φ(𝓝_t)`** with a time-independent `C²` test `φ`. -/
theorem isNativeItoProcess_comp
    (hIto : ItoFormulaFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ) ℝ)
    {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c : ℝ}
    {W : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}
    (hW : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a W)
    {φ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    IsNativeItoProcess μ (fun t x => φ (W t x))
      (fun t x => driftFn φ (driftC a c r κ t) (fun α => noiseC a c r α t) (W t x))
      (fun α t x => fderiv ℝ φ (W t x) (noiseC a c r α t * W t x)) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have h := hIto _ _ _ hW.1 (fun q => φ q.2) (hφ.comp contDiff_snd)
  simp only [timeDeriv_comp_snd hφ1, spaceDeriv_comp_snd hφ1, spaceDeriv2_comp_snd hφ,
    zero_add, smul_eq_mul] at h
  exact h

/-!
## The mean identity
-/

/-- For a bounded real Itô process with bounded drift and continuous mean drift,
`t ↦ E X_t` is differentiable at every `t₀ > 0` with derivative `E b_{t₀}`. -/
theorem hasDerivAt_mean_of_ito {X : ℝ≥0 → DriverSample S (RotIdx N) → ℝ}
    {b : ℝ≥0 → DriverSample S (RotIdx N) → ℝ} {σ : RotIdx N → ℝ≥0 → DriverSample S (RotIdx N) → ℝ}
    (hX : IsNativeItoProcess μ X b σ) {CX CB : ℝ} (hXb : ∀ t x, |X t x| ≤ CX)
    (hbb : ∀ t x, |b t x| ≤ CB)
    (hcont : Continuous fun s : ℝ => ∫ x, b s.toNNReal x ∂driverLaw (κ := RotIdx N) μ)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ∫ x, X t.toNNReal x ∂driverLaw (κ := RotIdx N) μ)
      (∫ x, b t₀.toNNReal x ∂driverLaw (κ := RotIdx N) μ) t₀ := by
  set g : ℝ → ℝ := fun s => ∫ x, b s.toNNReal x ∂driverLaw (κ := RotIdx N) μ
  have hF : HasDerivAt (fun t => (∫ x, X 0 x ∂driverLaw (κ := RotIdx N) μ) +
      ∫ s in (0 : ℝ)..t, g s) (g t₀) t₀ :=
    ((hcont.integral_hasStrictDerivAt 0 t₀).hasDerivAt).const_add _
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht₀] with t ht
  have h := integral_sub_integral_of_isNativeItoProcess hX hXb hbb t.toNNReal
  rw [Real.coe_toNNReal _ ht.le] at h
  rw [intervalIntegral.integral_of_le ht.le]
  linarith

end BlockBand.Palm.ReferenceFlow.Backward
