module

public import BlockBand.SourceProcess.Stochastic.Ito
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import BlockBand.Internal.Contracts.Transmission

/-!
# `exists_` at `p = 1`: generic calculus

Deterministic.

* Time-independent test functions `φ(t, y) = G(y)` on `ℝ × E`: their time derivative is `0`
  and their space derivatives are those of `G` (`fderiv_comp_snd_apply`,
  `fderiv_fderiv_comp_snd_apply`, local `C²` hypothesis only). Hence the contract Itô drift of
  `G` is the generator with coefficients held at the current values (`itoDrift_comp_snd`).
* Derivatives along lines: `fderiv G y v = d/dr G(y + r v)|₀` and
  `D²G(y)[v, v] = d²/dr² G(y + r v)|₀` (`fderiv_eq_deriv_line`, `fderiv_fderiv_eq_deriv_line`),
  and the componentwise form for vector-valued maps (`fderiv_fderiv_apply_eq_deriv_line`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic
open scoped NNReal

section Snd

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Precomposition with `snd : ℝ × E → E`, as a continuous linear map. -/
def precompSnd : (E →L[ℝ] F) →L[ℝ] ((ℝ × E) →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ (ℝ × E) E F).flip (ContinuousLinearMap.snd ℝ ℝ E)

theorem precompSnd_apply (L : E →L[ℝ] F) (u : ℝ × E) : precompSnd L u = L u.2 := rfl

theorem fderiv_comp_snd {G : E → F} {p : ℝ × E} (h : DifferentiableAt ℝ G p.2) :
    fderiv ℝ (fun q : ℝ × E => G q.2) p = precompSnd (fderiv ℝ G p.2) :=
  (h.hasFDerivAt.comp p hasFDerivAt_snd).fderiv

theorem fderiv_comp_snd_apply {G : E → F} {p : ℝ × E} (h : DifferentiableAt ℝ G p.2)
    (u : ℝ × E) : fderiv ℝ (fun q : ℝ × E => G q.2) p u = fderiv ℝ G p.2 u.2 := by
  rw [fderiv_comp_snd h]; rfl

theorem fderiv_fderiv_comp_snd_apply {G : E → F} {p : ℝ × E} (h : ContDiffAt ℝ 2 G p.2)
    (u v : ℝ × E) :
    fderiv ℝ (fderiv ℝ fun q : ℝ × E => G q.2) p u v = fderiv ℝ (fderiv ℝ G) p.2 u.2 v.2 := by
  have hev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 G q.2 :=
    (continuous_snd.tendsto p).eventually (h.eventually (by simp))
  have heq : (fderiv ℝ fun q : ℝ × E => G q.2) =ᶠ[𝓝 p] fun q => precompSnd (fderiv ℝ G q.2) := by
    filter_upwards [hev] with q hq
    exact fderiv_comp_snd (hq.differentiableAt (by norm_num))
  have hd : DifferentiableAt ℝ (fderiv ℝ G) p.2 :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : HasFDerivAt (fun q : ℝ × E => precompSnd (fderiv ℝ G q.2))
      (precompSnd.comp ((fderiv ℝ (fderiv ℝ G) p.2).comp (ContinuousLinearMap.snd ℝ ℝ E))) p :=
    (precompSnd (E := E) (F := F)).hasFDerivAt.comp p (hd.hasFDerivAt.comp p hasFDerivAt_snd)
  rw [heq.fderiv_eq, hD.fderiv]
  rfl

theorem fderiv_comp_snd_time {G : E → F} {p : ℝ × E} (h : DifferentiableAt ℝ G p.2) :
    fderiv ℝ (fun q : ℝ × E => G q.2) p (1, 0) = 0 := by
  rw [fderiv_comp_snd_apply h]; simp

end Snd

/-- **The contract Itô drift of a time-independent `C²` function** is the generator with the
coefficients held at the current values. -/
theorem itoDrift_comp_snd {d : ℕ} {G : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ} (h : ContDiffAt ℝ 2 G y)
    (t : ℝ≥0) (b : Fin d → ℝ) (a : Matrix (Fin d) (Fin d) ℝ) :
    itoDrift (fun q : ℝ × (Fin d → ℝ) => G q.2) y t b a =
      mpGenerator (fun _ => b) (fun _ => a) G y := by
  have hd : DifferentiableAt ℝ G y := h.differentiableAt (by norm_num)
  have h1 := fderiv_comp_snd_time (G := G) (p := ((t : ℝ), y)) hd
  have h2 := fderiv_comp_snd_apply (G := G) (p := ((t : ℝ), y)) hd
  have h3 := fderiv_fderiv_comp_snd_apply (G := G) (p := ((t : ℝ), y)) h
  simp only [itoDrift, mpGenerator, partialTime, partialSpace, partialSpace2, h1, h2, h3, zero_add]

section Line

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem hasDerivAt_line {G : E → F} {y v : E} (r : ℝ) (h : DifferentiableAt ℝ G (y + r • v)) :
    HasDerivAt (fun s : ℝ => G (y + s • v)) (fderiv ℝ G (y + r • v) v) r := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v r := by
    simpa using ((hasDerivAt_id r).smul_const v).const_add y
  exact h.hasFDerivAt.comp_hasDerivAt r hl

theorem fderiv_eq_deriv_line {G : E → F} {y : E} (v : E) (h : DifferentiableAt ℝ G y) :
    fderiv ℝ G y v = deriv (fun r : ℝ => G (y + r • v)) 0 := by
  have h' : DifferentiableAt ℝ G (y + (0 : ℝ) • v) := by simpa using h
  have := (hasDerivAt_line (v := v) 0 h').deriv
  simp only [zero_smul, add_zero] at this
  exact this.symm

/-- Near `0` the derivative along the line is `fderiv G (y + r v) v`. -/
theorem deriv_line_eventuallyEq {G : E → F} {y : E} (v : E) (h : ContDiffAt ℝ 2 G y) :
    deriv (fun r : ℝ => G (y + r • v)) =ᶠ[𝓝 0] fun r => fderiv ℝ G (y + r • v) v := by
  have hc : Continuous fun r : ℝ => y + r • v := continuous_const.add (continuous_id.smul
    continuous_const)
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 G (y + r • v) := by
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.eventually (h.eventually (by simp))
  filter_upwards [hev] with r hr
  exact (hasDerivAt_line r (hr.differentiableAt (by norm_num))).deriv

theorem hasDerivAt_fderiv_line {G : E → F} {y : E} (v : E) (h : ContDiffAt ℝ 2 G y) :
    HasDerivAt (fun r : ℝ => fderiv ℝ G (y + r • v) v) (fderiv ℝ (fderiv ℝ G) y v v) 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) (y + (0 : ℝ) • v) := by
    simpa using (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have := (hasDerivAt_line (G := fderiv ℝ G) (y := y) (v := v) 0 hd).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  simpa using this

/-- **Second derivative along a line.** -/
theorem fderiv_fderiv_eq_deriv_line {G : E → F} {y : E} (v : E) (h : ContDiffAt ℝ 2 G y) :
    fderiv ℝ (fderiv ℝ G) y v v = deriv (deriv fun r : ℝ => G (y + r • v)) 0 := by
  rw [(deriv_line_eventuallyEq v h).deriv_eq]
  exact (hasDerivAt_fderiv_line v h).deriv.symm

/-- Componentwise second derivative of a vector-valued map along a line. -/
theorem fderiv_fderiv_apply_eq_deriv_line {ι : Type*} [Fintype ι] {G : E → ι → ℝ} {y : E}
    (v : E) (h : ContDiffAt ℝ 2 G y) (i : ι) :
    fderiv ℝ (fderiv ℝ G) y v v i = deriv (deriv fun r : ℝ => G (y + r • v) i) 0 := by
  have hev : deriv (fun r : ℝ => G (y + r • v) i) =ᶠ[𝓝 0]
      fun r => fderiv ℝ G (y + r • v) v i := by
    filter_upwards [deriv_line_eventuallyEq v h, (by
      have hc : Continuous fun r : ℝ => y + r • v := continuous_const.add (continuous_id.smul
        continuous_const)
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.eventually (h.eventually (by simp)) :
        ∀ᶠ r in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 G (y + r • v))] with r _ hr
    exact ((hasDerivAt_pi.1 (hasDerivAt_line r (hr.differentiableAt (by norm_num)))) i).deriv
  rw [hev.deriv_eq]
  exact ((hasDerivAt_pi.1 (hasDerivAt_fderiv_line v h)) i).deriv.symm

/-- Componentwise first derivative of a vector-valued map along a line. -/
theorem fderiv_apply_eq_deriv_line {ι : Type*} [Fintype ι] {G : E → ι → ℝ} {y : E} (v : E)
    (h : DifferentiableAt ℝ G y) (i : ι) :
    fderiv ℝ G y v i = deriv (fun r : ℝ => G (y + r • v) i) 0 := by
  have h' : DifferentiableAt ℝ G (y + (0 : ℝ) • v) := by simpa using h
  have := ((hasDerivAt_pi.1 (hasDerivAt_line (v := v) 0 h')) i).deriv
  simp only [zero_smul, add_zero] at this
  exact this.symm

end Line

end BlockBand.Transmission.Dual.Exists
