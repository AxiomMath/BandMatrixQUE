module
public import BlockBand.Diffusion.Duality.Entrance
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Strip coordinates for the base duality

The base duality results `IsExBaseDiffusion.duality` and `IsExBaseDiffusion.condExp_duality` are
stated in `Fin 2` coordinates, for `u : ℝ × (Fin 2 → ℝ) → ℝ` and
`stGen (baseDrift D0) (baseCov D0)`. Here they are transported to the strip form used by
the kernels: `v : ℝ × (ℝ × ℝ) → ℝ`, `v(s, (x, y))`.

* `stripEquiv : ℝ × ℝ² ≃L ℝ × (ℝ × ℝ)`, `(s, y) ↦ (s, (y 0, y 1))` (`id × finProd`).
* `stripGen D0 v q = ∂ₛv + (D₀/2)[x(1+x)∂ₓ²v + (1+2x)∂ₓv + y(1-y)∂ᵧ²v + (1-2y)∂ᵧv]` at
  `q = (s, (x, y))` (joint Fréchet derivatives; no regularity in the definition).
* `stGen_baseDrift_comp`: `stGen (baseDrift D0) (baseCov D0) (v ∘ stripEquiv) p =
  stripGen D0 v (stripEquiv p)` for **every** `v` and `p` (chain rule for a linear
  equivalence, as in `mpGenerator_stDrift_comp`).
* Transport of the regularity, continuity and bound hypotheses (`contDiffOn_comp_stripEquiv`,
  `continuousOn_comp_stripEquiv`, `continuousWithinAt_comp_stripEquiv`).

## Main results

For `Z` an `IsExBaseDiffusion P 𝓖 D0 z Z`, `0 < D0`, start `z` in the closed
strip, and `v` jointly `C²` on `(0, t) × exOpenStrip` with `stripGen D0 v = 0` there, continuous
on `(0, t] × exOpenStrip` and within it at `(0, z)`, bounded there:
* `IsExBaseDiffusion.duality_strip`: `E[v(t, Z_t)] = v(0, z)`;
* `IsExBaseDiffusion.condExp_duality_strip`: `E[v(t, Z_t) | 𝓖_s] = v(s, Z_s)` a.s. (`s < t`).
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

/-- `(s, y) ↦ (s, (y 0, y 1))`. -/
def stripEquiv : (ℝ × (Fin 2 → ℝ)) ≃L[ℝ] ℝ × (ℝ × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr finProd

@[simp] theorem stripEquiv_apply (p : ℝ × (Fin 2 → ℝ)) :
    stripEquiv p = (p.1, (p.2 0, p.2 1)) := rfl

@[simp] theorem stripEquiv_symm_apply (q : ℝ × (ℝ × ℝ)) :
    stripEquiv.symm q = (q.1, ![q.2.1, q.2.2]) := rfl

/-- The space-time base operator in strip coordinates. -/
def stripGen (D0 : ℝ) (v : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ v q (1, (0, 0)) + D0 / 2 *
    ((q.2.1 * (1 + q.2.1) * fderiv ℝ (fderiv ℝ v) q (0, (1, 0)) (0, (1, 0)) +
        (1 + 2 * q.2.1) * fderiv ℝ v q (0, (1, 0))) +
      (q.2.2 * (1 - q.2.2) * fderiv ℝ (fderiv ℝ v) q (0, (0, 1)) (0, (0, 1)) +
        (1 - 2 * q.2.2) * fderiv ℝ v q (0, (0, 1))))

theorem fderiv_comp_stripEquiv (v : ℝ × (ℝ × ℝ) → ℝ) (p w : ℝ × (Fin 2 → ℝ)) :
    fderiv ℝ (v ∘ stripEquiv) p w = fderiv ℝ v (stripEquiv p) (stripEquiv w) := by
  rw [stripEquiv.comp_right_fderiv]; rfl

theorem fderiv_fderiv_comp_stripEquiv (v : ℝ × (ℝ × ℝ) → ℝ) (p w w' : ℝ × (Fin 2 → ℝ)) :
    fderiv ℝ (fderiv ℝ (v ∘ stripEquiv)) p w w' =
      fderiv ℝ (fderiv ℝ v) (stripEquiv p) (stripEquiv w) (stripEquiv w') := by
  have h := stripEquiv.iteratedFDerivWithin_comp_right v uniqueDiffOn_univ
    (mem_univ (stripEquiv p)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have h2 := congrArg (fun L => L ![w, w']) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply] at h2
  simpa using h2

/-- **Generator transport** (every `v`, every point). -/
theorem stGen_baseDrift_comp (D0 : ℝ) (v : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (Fin 2 → ℝ)) :
    stGen (baseDrift D0) (baseCov D0) (v ∘ stripEquiv) p = stripGen D0 v (stripEquiv p) := by
  have e0 : stripEquiv ((1 : ℝ), (0 : Fin 2 → ℝ)) = (1, (0, 0)) := rfl
  have e1 : stripEquiv ((0 : ℝ), (Pi.single 0 1 : Fin 2 → ℝ)) = (0, (1, 0)) := by simp
  have e2 : stripEquiv ((0 : ℝ), (Pi.single 1 1 : Fin 2 → ℝ)) = (0, (0, 1)) := by simp
  simp only [stGen, partialTime, partialSpace, partialSpace2, fderiv_comp_stripEquiv,
    fderiv_fderiv_comp_stripEquiv, Fin.sum_univ_two, e0, e1, e2]
  simp [baseDrift, baseCov, stripGen]
  ring

/-!
### Transport of the hypotheses
-/

theorem stripEquiv_mem_iff {I : Set ℝ} {p : ℝ × (Fin 2 → ℝ)} :
    stripEquiv p ∈ I ×ˢ exOpenStrip ↔ p ∈ I ×ˢ openStripFin := Iff.rfl

theorem mapsTo_stripEquiv (I : Set ℝ) :
    MapsTo stripEquiv (I ×ˢ openStripFin) (I ×ˢ exOpenStrip) := fun _ hp => hp

theorem contDiffOn_comp_stripEquiv {v : ℝ × (ℝ × ℝ) → ℝ} {I : Set ℝ}
    (hv : ContDiffOn ℝ 2 v (I ×ˢ exOpenStrip)) :
    ContDiffOn ℝ 2 (v ∘ stripEquiv) (I ×ˢ openStripFin) :=
  hv.comp stripEquiv.contDiff.contDiffOn (mapsTo_stripEquiv I)

theorem continuousOn_comp_stripEquiv {v : ℝ × (ℝ × ℝ) → ℝ} {I : Set ℝ}
    (hv : ContinuousOn v (I ×ˢ exOpenStrip)) :
    ContinuousOn (v ∘ stripEquiv) (I ×ˢ openStripFin) :=
  hv.comp stripEquiv.continuous.continuousOn (mapsTo_stripEquiv I)

theorem continuousWithinAt_comp_stripEquiv {v : ℝ × (ℝ × ℝ) → ℝ} {I : Set ℝ} {z : ℝ × ℝ}
    {s : ℝ} (hv : ContinuousWithinAt v (I ×ˢ exOpenStrip) (s, z)) :
    ContinuousWithinAt (v ∘ stripEquiv) (I ×ˢ openStripFin) (s, finProd.symm z) :=
  ContinuousWithinAt.comp (f := stripEquiv) (x := (s, finProd.symm z)) (by simpa using hv)
    stripEquiv.continuous.continuousWithinAt (mapsTo_stripEquiv I)

/-!
### Duality in strip coordinates
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {z : ℝ × ℝ}
  {Z : ℝ≥0 → Ω → ℝ × ℝ}

section StripDuality

variable (h : IsExBaseDiffusion P 𝓖 D0 z Z) (hD0 : 0 < D0) {t : ℝ≥0}
  {v : ℝ × (ℝ × ℝ) → ℝ} (hv2 : ContDiffOn ℝ 2 v (Ioo 0 (t : ℝ) ×ˢ exOpenStrip))
  (hpde : ∀ q ∈ Ioo 0 (t : ℝ) ×ˢ exOpenStrip, stripGen D0 v q = 0)
  (hcont : ContinuousOn v (Ioc 0 (t : ℝ) ×ˢ exOpenStrip))
  (hv0 : ContinuousWithinAt v (Ioc 0 (t : ℝ) ×ˢ exOpenStrip) (0, z))
  {C : ℝ} (hC : ∀ q ∈ Ioc 0 (t : ℝ) ×ˢ exOpenStrip, |v q| ≤ C)
include h hD0 hv2 hpde hcont hv0 hC

/-- **Duality in strip coordinates.** `E[v(t, Z_t)] = v(0, z)`. -/
theorem IsExBaseDiffusion.duality_strip (ht : 0 < t) :
    ∫ ω, v ((t : ℝ), Z t ω) ∂P = v (0, z) := by
  have H := h.duality hD0 (u := v ∘ stripEquiv) (contDiffOn_comp_stripEquiv hv2)
    (fun p hp => by rw [stGen_baseDrift_comp]; exact hpde _ hp)
    (continuousOn_comp_stripEquiv hcont) (continuousWithinAt_comp_stripEquiv hv0)
    (fun p hp => hC _ hp) ht
  simpa [baseFin] using H

/-- **Conditional duality in strip coordinates.** For `s < t`,
`E[v(t, Z_t) | 𝓖_s] = v(s, Z_s)` a.s. -/
theorem IsExBaseDiffusion.condExp_duality_strip {s : ℝ≥0} (hst : s < t) :
    P[fun ω => v ((t : ℝ), Z t ω) | 𝓖 s] =ᵐ[P] fun ω => v ((s : ℝ), Z s ω) := by
  have H := h.condExp_duality hD0 (u := v ∘ stripEquiv) (contDiffOn_comp_stripEquiv hv2)
    (fun p hp => by rw [stGen_baseDrift_comp]; exact hpde _ hp)
    (continuousOn_comp_stripEquiv hcont) (continuousWithinAt_comp_stripEquiv hv0)
    (fun p hp => hC _ hp) hst
  simpa [baseFin] using H

end StripDuality

end BlockBand.Diffusion
