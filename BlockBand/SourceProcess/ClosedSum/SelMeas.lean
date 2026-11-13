module

public import BlockBand.SourceProcess.ClosedSum.SelGram
public import BlockBand.SourceProcess.FullSourceStops.CurrentPast

/-!
# A measurable admissible time-`s` frame from `MeasurableEigenSelection`

* `measurable_selFrame`: for a measurable selection `V`, `S ↦ selFrame V S h K` is measurable.
* `physSelFrame`: the selected frame at the physical `𝕊(n_s)`; it is `growthSigma W n_s`-measurable
  (`measurable_physSelFrame`, through Bridge's `extPast`).
* **`isTimeSFrame_physSelFrame`** (`b < 1/2`, `-2 < E < 2`, `W ≥ 1`): `physSelFrame` is an
  admissible time-`s` frame (`IsTimeSFrame`).
* **`existsTimeSFrame_of_eigenSel (hEig : EigenSel.MeasurableEigenSelection) : ExistsTimeSFrame`**:
  `ExistsTimeSFrame` follows from a measurable eigenvector selection.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Closing
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSourceStops

variable {W K : ℕ} {V : (Fin W → Fin W → ℂ) → Fin W → Fin (Fintype.card (Fin W)) → ℂ}

abbrev SMat (W : ℕ) := Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ

theorem measurable_farT : Measurable (farT : SMat W → Matrix (Fin W) (Fin W) ℂ) := by
  refine Measurable.of_eval_matrix _ fun a c => ?_
  simp only [farT, Matrix.sub_apply, mul_apply, conjTranspose_apply, portBlock, of_apply]
  exact measurable_const.sub (Finset.measurable_sum _ fun x _ =>
    (Complex.continuous_conj.measurable.comp (measurable_pi_apply _ |>.eval)).mul
      (measurable_pi_apply _ |>.eval))

theorem measurable_selVec (hVm : Measurable V) (k : ℕ) :
    Measurable fun S : SMat W => selVec V S k := by
  by_cases hk : k < Fintype.card (Fin W)
  · simp only [selVec, hk, ↓reduceDIte]
    exact Measurable.of_eval fun a => ((hVm.comp measurable_farT).eval).eval
  · simp only [selVec, hk, ↓reduceDIte]; exact measurable_const

theorem measurable_selT (hVm : Measurable V) (k : ℕ) : Measurable fun S : SMat W => selT V S k := by
  have h1 := measurable_selVec hVm k
  refine Complex.measurable_re.comp ?_
  simp only [dotProduct, mulVec, Pi.star_apply]
  exact Finset.measurable_sum _ fun a _ => (Complex.continuous_conj.measurable.comp h1.eval).mul
    (Finset.measurable_sum _ fun c _ => (measurable_farT.eval.eval).mul h1.eval)

theorem measurable_selF (hVm : Measurable V) (h : ℝ) :
    Measurable fun S : SMat W => farInj W * selFw V S h K := by
  refine measurable_matrix_mul' measurable_const (Measurable.of_eval_matrix _ fun a k => ?_)
  simp only [selFw, of_apply]
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_selT hVm k.val))
    (measurable_selVec hVm k.val).eval measurable_const

theorem measurable_xInvDiag (hVm : Measurable V) :
    Measurable fun S : SMat W => xInvDiag K (selT V S) := by
  refine Measurable.of_eval_matrix _ fun k l => ?_
  simp only [xInvDiag, diagonal_apply]
  split_ifs
  · exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      ((measurable_selT hVm _).mul (measurable_const.sub (measurable_selT hVm _)))).inv
  · exact measurable_const

theorem measurable_modeVector {f : SMat W → ℝ} (hf : Measurable f) (σ i : Fin 2) :
    Measurable fun S => modeVector (f S) σ i := by
  have hq : Measurable fun S => Real.sqrt (f S) := Real.continuous_sqrt.measurable.comp hf
  have hp : Measurable fun S => ((Real.sqrt (1 + Real.sqrt (f S)) / Real.sqrt 2 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp
      (measurable_const.add hq)).div_const _)
  have hm : Measurable fun S => ((Real.sqrt (1 - Real.sqrt (f S)) / Real.sqrt 2 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp
      (measurable_const.sub hq)).div_const _)
  have hn : Measurable fun S => ((-(Real.sqrt (1 - Real.sqrt (f S)) / Real.sqrt 2) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp
      (measurable_const.sub hq)).div_const _).neg
  fin_cases σ <;> fin_cases i
  · exact hm
  · exact hp
  · exact hp
  · exact hn

/-- **The selected frame is a measurable function of the scattering matrix.** -/
theorem measurable_selFrame (hVm : Measurable V) (h : ℝ) :
    Measurable fun S : SMat W => selFrame V S h K := by
  have hQ : Measurable fun S : SMat W => Sᴴ * nearPortProj W * S :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' measurable_id)
      measurable_const) measurable_id
  have hN : Measurable fun S : SMat W => nearPartners (nearPortProj W) (Sᴴ * nearPortProj W * S)
      (farInj W * selFw V S h K) (selT V S) :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_mul' measurable_const hQ)
      (measurable_selF hVm h)) (measurable_xInvDiag hVm)
  refine Measurable.of_eval_matrix _ fun x ⟨k, σ⟩ => ?_
  simp only [selFrame, curBlock, of_apply, curFrame_apply]
  have hT := measurable_selT (V := V) hVm k.val
  refine Measurable.ite (measurableSet_lt measurable_const hT) ?_ measurable_const
  refine (Complex.measurable_ofReal.comp (hT.pow_const _)).mul
    (((measurable_modeVector hT _ _).mul hN.eval.eval).add
      ((measurable_modeVector hT _ _).mul (measurable_selF hVm h).eval.eval))

/-- **The selected physical time-`s` frame.** -/
def physSelFrame (V : (Fin W → Fin W → ℂ) → Fin W → Fin (Fintype.card (Fin W)) → ℂ)
    (b E s h : ℝ) (K : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ :=
  selFrame V (scatteringMatrix b E W (closeLen s W) ω) h K

theorem scatteringMatrix_extPast (b E : ℝ) (n : ℕ) (ω : GrowthPath W) :
    scatteringMatrix b E W n (extPast W n (pastCoords W n ω)) = scatteringMatrix b E W n ω := by
  simp only [scatteringMatrix, boundaryResolvent, fullInverse, fullPathMatrix, pathAt_extPast]

theorem measurable_physSelFrame (hVm : Measurable V) (b E s h : ℝ) :
    Measurable[growthSigma W (closeLen s W)] (physSelFrame V b E s h K) := by
  have e : physSelFrame V b E s h K = (fun p => selFrame V (scatteringMatrix b E W (closeLen s W)
      (extPast W (closeLen s W) p)) h K) ∘ pastCoords W (closeLen s W) := by
    funext ω; simp only [Function.comp_apply, scatteringMatrix_extPast, physSelFrame]
  rw [e, growthSigma_eq_comap]
  exact ((measurable_selFrame hVm h).comp ((measurable_scatteringMatrix b E _).comp
    (measurable_extPast _))).comp (comap_measurable _)

/-- **`physSelFrame` is an admissible time-`s` frame.** -/
theorem isTimeSFrame_physSelFrame (hV : IsEigenSel V) (hVm : Measurable V) {b E s : ℝ}
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (h : ℝ) :
    IsTimeSFrame b E s h K W (physSelFrame V b E s h K) := by
  refine ⟨measurable_physSelFrame hVm b E s h, ?_⟩
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ae_hlt (s := s) hb hE1 hE2 hW] with ω hU hlt
  have hlt' : ∀ k : Fin K, h ^ 2 < selT V (scatteringMatrix b E W (closeLen s W) ω) k.val →
      selT V (scatteringMatrix b E W (closeLen s W) ω) k.val < 1 := by
    rw [selT_phys hV]; exact hlt K h
  refine ⟨?_, fun x k => ?_⟩
  · rw [physSelFrame, gramPair_selFrame hV (hU _).1 h hlt', selT_phys hV]
  · have := sub_mul_selFrame hV (hU _).1 h hlt' x k
    rw [selT_phys hV] at this
    exact this

/-- **`ExistsTimeSFrame` from the lead's interface `MeasurableEigenSelection`.** -/
theorem existsTimeSFrame_of_eigenSel (hEig : EigenSel.MeasurableEigenSelection) :
    ExistsTimeSFrame := by
  intro b _ hb E hE1 hE2 s _ h _ _ K
  filter_upwards [eventually_ge_atTop 1] with W hW
  obtain ⟨V, hVm, hV⟩ := hEig (Fin W)
  exact ⟨physSelFrame V b E s h K, isTimeSFrame_physSelFrame hV hVm hb hE1 hE2 hW h⟩

end BlockBand.SourceProcess.ClosedSum
