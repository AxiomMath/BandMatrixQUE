module

public import BlockBand.Transmission.Dual.ExistsMart

/-!
# `exists_` at `p = 1`: the total `S = x + y` and the Lyapunov function `g`

On the flat chamber `𝒞₁ = {x > 0, 0 < y < 1}`:
* `L₁_tot`: `L₁ S = 0` for `S = x + y` (`𝒟₁ R = 0`);
* the second derivatives along coordinate lines, `lineX_second`, `lineY_second`.

These are used in the sibling module to prove:
* `L₁_lyapG`: `L₁ g = D₀ S` for `g = S·φ`, `φ = log(1+x) − log x − log y − log(1−y)`. Indeed
  `𝒟₁(Sφ) = S L⁰φ` (the h-transform identity) with `L_X(log(1+x) − log x) = 0` (scale
  function) and `L_Y(−log y − log(1−y)) = D₀`; here it is checked directly;
* `one_le_lyapPhi`: `φ ≥ 1`, so `S ≤ g` and `L₁ g ≤ D₀ g`;
* `lyapG_toFlat_ge`: if `‖w‖ ≥ n` (sup norm in `(u, v)`) and `ε ≤ S(toFlat w)`, `0 ≤ ε ≤ 1`,
  then `ε n ≤ g(toFlat w)`: on `{S ≥ ε}` the function `g` is large at the boundary of the
  `n`-th ball.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- `S = x + y`. -/
def tot (y : Fin 2 → ℝ) : ℝ := y 0 + y 1

/-- `φ = log(1+x) − log x − log y − log(1−y)`. -/
def lyapPhi (y : Fin 2 → ℝ) : ℝ := Real.log (1 + y 0) - Real.log (y 0) - Real.log (y 1) -
  Real.log (1 - y 1)

/-- The Lyapunov function `g = S φ`. -/
def lyapG (y : Fin 2 → ℝ) : ℝ := tot y * lyapPhi y

theorem mem_flatChamber_one {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) :
    0 < y 0 ∧ 0 < y 1 ∧ y 1 < 1 :=
  ⟨hy.2.2.1 0, (hy.2.2.2 0).1, (hy.2.2.2 0).2⟩

/-- `S` as a continuous linear map. -/
def totCLM : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem totCLM_eq : ⇑totCLM = tot := rfl

theorem contDiff_tot : ContDiff ℝ ⊤ tot := totCLM.contDiff

theorem measurable_tot : Measurable tot := totCLM.continuous.measurable

/-- The diagonal form of the flat generator. -/
theorem L₁_eq (D0 : ℝ) (G : (Fin 2 → ℝ) → ℝ) (y : Fin 2 → ℝ) :
    L₁ D0 G y = flatDrift D0 1 y 0 * fderiv ℝ G y (Pi.single 0 1) +
      flatDrift D0 1 y 1 * fderiv ℝ G y (Pi.single 1 1) +
      (1 / 2 : ℝ) * (D0 * (y 0 * (1 + y 0)) * fderiv ℝ (fderiv ℝ G) y (Pi.single 0 1)
        (Pi.single 0 1) + D0 * (y 1 * (1 - y 1)) * fderiv ℝ (fderiv ℝ G) y (Pi.single 1 1)
        (Pi.single 1 1)) := by
  simp only [L₁, mpGenerator, Fin.sum_univ_two, flatDiff, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide), zero_mul, add_zero, zero_add,
    flatDiffDiag_one_zero, flatDiffDiag_one_one]

/-- **`𝒟₁ S = 0`.** -/
theorem L₁_tot (D0 : ℝ) {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) : L₁ D0 tot y = 0 := by
  obtain ⟨h0, h1, -⟩ := mem_flatChamber_one hy
  have hd : ∀ w, fderiv ℝ tot w = totCLM := fun w => totCLM.fderiv
  have hdd : fderiv ℝ (fderiv ℝ tot) y = 0 := by
    rw [show fderiv ℝ tot = fun _ => totCLM from funext hd]; exact fderiv_const_apply _
  rw [L₁_eq, hd, hdd, flatDrift_one_zero, flatDrift_one_one]
  have hs : y 0 + y 1 ≠ 0 := by positivity
  have htot : ∀ v : Fin 2 → ℝ, totCLM v = v 0 + v 1 := fun v => rfl
  simp only [htot, Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  have h00 : ∀ u v : Fin 2 → ℝ, (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ) u v = 0 :=
    fun _ _ => rfl
  rw [h00, h00]
  field_simp
  ring

/-!
## One-dimensional derivatives
-/

/-- `deriv (deriv h) 0` from a derivative formula valid near `0`. -/
theorem deriv_deriv_of_eventually {h h1 : ℝ → ℝ} {v : ℝ}
    (h0 : ∀ᶠ r in 𝓝 (0 : ℝ), HasDerivAt h (h1 r) r) (h1' : HasDerivAt h1 v 0) :
    deriv (deriv h) 0 = v := by
  have : deriv h =ᶠ[𝓝 0] h1 := h0.mono fun r hr => hr.deriv
  rw [this.deriv_eq, h1'.deriv]

theorem hasDerivAt_log_shift {c r : ℝ} (hc : 0 < c + r) :
    HasDerivAt (fun s => Real.log (c + s)) (1 / (c + r)) r := by
  have := ((hasDerivAt_id r).const_add c).log hc.ne'
  simpa [div_eq_inv_mul] using this

theorem hasDerivAt_log_one_sub {c r : ℝ} (hc : 0 < 1 - (c + r)) :
    HasDerivAt (fun s => Real.log (1 - (c + s))) (-(1 / (1 - (c + r)))) r := by
  have h1 : HasDerivAt (fun s => 1 - (c + s)) (-1) r := by
    simpa using ((hasDerivAt_id r).const_add c).const_sub 1
  have := h1.log hc.ne'
  convert this using 1
  ring

theorem hasDerivAt_inv_shift {c r : ℝ} (hc : c + r ≠ 0) :
    HasDerivAt (fun s => 1 / (c + s)) (-(1 / (c + r) ^ 2)) r := by
  have := ((hasDerivAt_id r).const_add c).inv hc
  convert this using 1
  · funext x; simp
  · simp only [id_eq]; ring

/-- The `x`-line: `r ↦ (A + r)(log(1 + c + r) − log(c + r) + d)`. -/
theorem lineX_second {A c d : ℝ} (hc : 0 < c) :
    deriv (deriv fun r : ℝ => (A + r) * (Real.log (1 + c + r) - Real.log (c + r) + d)) 0 =
      2 * (1 / (1 + c) - 1 / c) + A * (-(1 / (1 + c) ^ 2) + 1 / c ^ 2) := by
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < c + r := by
    have : Tendsto (fun r : ℝ => c + r) (𝓝 0) (𝓝 c) := by
      simpa using (tendsto_const_nhds (x := c)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact this.eventually (lt_mem_nhds hc)
  refine deriv_deriv_of_eventually (h1 := fun r => (Real.log (1 + c + r) - Real.log (c + r) + d) +
    (A + r) * (1 / (1 + c + r) - 1 / (c + r))) (hev.mono fun r hr => ?_) ?_
  · have h1 : 0 < 1 + c + r := by linarith
    have hl1 := hasDerivAt_log_shift (c := 1 + c) (r := r) h1
    have hl2 := hasDerivAt_log_shift (c := c) (r := r) hr
    have := ((hasDerivAt_id r).const_add A).mul ((hl1.sub hl2).add_const d)
    convert this using 1
    · funext x; simp
    · simp
  · have h1 : (0 : ℝ) < 1 + c + 0 := by linarith
    have hi1 := hasDerivAt_inv_shift (c := 1 + c) (r := 0) h1.ne'
    have hi2 := hasDerivAt_inv_shift (c := c) (r := 0) (by simpa using hc.ne')
    have hl1 := hasDerivAt_log_shift (c := 1 + c) (r := 0) h1
    have hl2 := hasDerivAt_log_shift (c := c) (r := 0) (by simpa using hc)
    have := ((hl1.sub hl2).add_const d).add (((hasDerivAt_id (0 : ℝ)).const_add A).mul
      (hi1.sub hi2))
    convert this using 1
    · funext x; simp
    · simp only [add_zero, id_eq, Pi.sub_apply]; ring

/-- The `y`-line: `r ↦ (A + r)(d − log(c + r) − log(1 − (c + r)))`. -/
theorem lineY_second {A c d : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    deriv (deriv fun r : ℝ => (A + r) * (d - Real.log (c + r) - Real.log (1 - (c + r)))) 0 =
      2 * (-(1 / c) + 1 / (1 - c)) + A * (1 / c ^ 2 + 1 / (1 - c) ^ 2) := by
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < c + r ∧ 0 < 1 - (c + r) := by
    have : Tendsto (fun r : ℝ => c + r) (𝓝 0) (𝓝 c) := by
      simpa using (tendsto_const_nhds (x := c)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact (this.eventually (lt_mem_nhds hc)).and
      (this.eventually (gt_mem_nhds hc1) |>.mono fun r hr => by linarith)
  refine deriv_deriv_of_eventually (h1 := fun r => (d - Real.log (c + r) -
    Real.log (1 - (c + r))) + (A + r) * (-(1 / (c + r)) + 1 / (1 - (c + r))))
    (hev.mono fun r hr => ?_) ?_
  · have hl1 := hasDerivAt_log_shift (c := c) (r := r) hr.1
    have hl2 := hasDerivAt_log_one_sub (c := c) (r := r) hr.2
    have := ((hasDerivAt_id r).const_add A).mul (((hasDerivAt_const r d).sub hl1).sub hl2)
    convert this using 1
    · funext x; simp
    · simp only [id_eq, Pi.sub_apply]; ring
  · have h0 : (0 : ℝ) < c + 0 := by simpa using hc
    have h1 : (0 : ℝ) < 1 - (c + 0) := by linarith
    have hl1 := hasDerivAt_log_shift (c := c) (r := 0) h0
    have hl2 := hasDerivAt_log_one_sub (c := c) (r := 0) h1
    have hi1 := hasDerivAt_inv_shift (c := c) (r := 0) h0.ne'
    have hi2 : HasDerivAt (fun s => 1 / (1 - (c + s))) (1 / (1 - (c + 0)) ^ 2) 0 := by
      have hh : HasDerivAt (fun s => 1 - (c + s)) (-1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add c).const_sub 1
      have := hh.inv h1.ne'
      convert this using 1
      · funext s; simp
      · ring
    have := (((hasDerivAt_const (0 : ℝ) d).sub hl1).sub hl2).add
      (((hasDerivAt_id (0 : ℝ)).const_add A).mul (hi1.neg.add hi2))
    convert this using 1
    · funext x; simp
    · simp only [add_zero, id_eq, Pi.add_apply, Pi.neg_apply]; ring

end BlockBand.Transmission.Dual.Exists
