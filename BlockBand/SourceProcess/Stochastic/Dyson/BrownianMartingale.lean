module

public import BlockBand.SourceProcess.Stochastic.Dyson.BrownianCoords

/-!
# Dyson Brownian motion: the coordinate martingales of `G` restarted at time `s`

For `W_t^x = hermCoord (G_{s+t} - G_s) x` and the shifted filtration `u ↦ 𝓖_{s+u}`:
* `martingale_coordIncr`: `W^x` is a martingale;
* `martingale_coordIncr_mul`: `W^x W^y - t [x = y]/N` is a martingale.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ} {Ω : Type*} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}

/-- Coordinate increments `W_t^x = hermCoord (G_{s+t} - G_s) x`. -/
def coordIncr (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (x : Fin N × Fin N)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  hermCoord N (G (s + t) ω - G s ω) x

/-- The GUE coordinate covariance `[x = y]/N`. -/
def coordCov (N : ℕ) (x y : Fin N × Fin N) : ℝ := if x = y then 1 / (N : ℝ) else 0

theorem coordIncr_split (s : ℝ≥0) (x : Fin N × Fin N) (u t : ℝ≥0) (ω : Ω) :
    coordIncr G s x t ω =
      coordIncr G s x u ω + hermCoord N (G (s + t) ω - G (s + u) ω) x := by
  unfold coordIncr
  rw [← hermCoord_add]
  congr 1; abel

variable [MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem stronglyMeasurable_coordIncr (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (x : Fin N × Fin N) (t : ℝ≥0) :
    StronglyMeasurable[shiftFiltration 𝓖 s t] (coordIncr G s x t) :=
  ((continuous_hermCoord x).measurable.comp
    (measurable_increment hG (le_self_add) le_rfl)).stronglyMeasurable

theorem measurable_coordIncr (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (x : Fin N × Fin N) (t : ℝ≥0) : Measurable[𝓖 (s + t)] (coordIncr G s x t) :=
  (continuous_hermCoord x).measurable.comp (measurable_increment hG (le_self_add) le_rfl)

theorem integrable_coordIncr (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (x : Fin N × Fin N) (t : ℝ≥0) : Integrable (coordIncr G s x t) Q :=
  integrable_increment hG le_self_add (integrable_hermCoord_gue _ x)

theorem integrable_coordIncr_mul (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (x y : Fin N × Fin N) (t : ℝ≥0) :
    Integrable (fun ω => coordIncr G s x t ω * coordIncr G s y t ω) Q :=
  integrable_increment hG le_self_add (g := fun Z => hermCoord N Z x * hermCoord N Z y)
    (integrable_hermCoord_mul_gue _ x y)

theorem integrable_incr_coord (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    (x : Fin N × Fin N) : Integrable (fun ω => hermCoord N (G t ω - G r ω) x) Q :=
  integrable_increment hG hrt (integrable_hermCoord_gue _ x)

theorem integral_incr_coord (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    (x : Fin N × Fin N) : ∫ ω, hermCoord N (G t ω - G r ω) x ∂Q = 0 := by
  rw [integral_increment hG hrt (continuous_hermCoord x).measurable, integral_hermCoord_gue]

theorem integral_incr_coord_mul (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    (x y : Fin N × Fin N) :
    ∫ ω, hermCoord N (G t ω - G r ω) x * hermCoord N (G t ω - G r ω) y ∂Q =
      ((t : ℝ) - r) * coordCov N x y := by
  rw [integral_increment hG hrt (g := fun Z => hermCoord N Z x * hermCoord N Z y)
    ((continuous_hermCoord x).measurable.mul (continuous_hermCoord y).measurable),
    integral_hermCoord_mul_gue, NNReal.coe_sub hrt, coordCov]
  split_ifs <;> ring

/-- Set-integral martingale criterion in the shifted filtration. -/
theorem martingale_of_setIntegral_shift [IsProbabilityMeasure Q] {s : ℝ≥0} {f : ℝ≥0 → Ω → ℝ}
    (hadapt : ∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t] (f t))
    (hint : ∀ t, Integrable (f t) Q)
    (hset : ∀ u t, u ≤ t → ∀ A, MeasurableSet[𝓖 (s + u)] A →
      ∫ ω in A, f u ω ∂Q = ∫ ω in A, f t ω ∂Q) :
    Martingale f (shiftFiltration 𝓖 s) Q := by
  refine ⟨hadapt, fun u t hut => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((shiftFiltration 𝓖 s).le u) (hint t)
    (fun A _ _ => (hint u).integrableOn) (fun A hA _ => hset u t hut A hA)
    (hadapt u).aestronglyMeasurable).symm

/-- **Coordinate martingale**: `t ↦ hermCoord (G_{s+t} - G_s) x` is a `𝓖_{s+·}`-martingale. -/
theorem martingale_coordIncr [IsProbabilityMeasure Q] (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (x : Fin N × Fin N) : Martingale (coordIncr G s x) (shiftFiltration 𝓖 s) Q := by
  refine martingale_of_setIntegral_shift (stronglyMeasurable_coordIncr hG s x)
    (integrable_coordIncr hG s x) fun u t hut A hA => ?_
  have hst : s + u ≤ s + t := add_le_add_right hut s
  simp_rw [coordIncr_split (G := G) s x u t]
  rw [integral_add (integrable_coordIncr hG s x u).integrableOn
    (integrable_incr_coord hG hst x).integrableOn,
    setIntegral_increment hG hst hA (continuous_hermCoord x).measurable,
    integral_incr_coord hG hst x, mul_zero, add_zero]

/-- **Bracket martingale**: `W^x W^y - t [x = y]/N` is a `𝓖_{s+·}`-martingale. -/
theorem martingale_coordIncr_mul [IsProbabilityMeasure Q] (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (x y : Fin N × Fin N) :
    Martingale (fun t ω => coordIncr G s x t ω * coordIncr G s y t ω - (t : ℝ) * coordCov N x y)
      (shiftFiltration 𝓖 s) Q := by
  refine martingale_of_setIntegral_shift (fun t => ?_) (fun t => ?_) fun u t hut A hA => ?_
  · exact ((stronglyMeasurable_coordIncr hG s x t).mul
      (stronglyMeasurable_coordIncr hG s y t)).sub stronglyMeasurable_const
  · exact (integrable_coordIncr_mul hG s x y t).sub (integrable_const _)
  have hst : s + u ≤ s + t := add_le_add_right hut s
  set a := coordIncr G s x u
  set b := coordIncr G s y u
  set d : Ω → ℝ := fun ω => hermCoord N (G (s + t) ω - G (s + u) ω) x
  set e : Ω → ℝ := fun ω => hermCoord N (G (s + t) ω - G (s + u) ω) y
  have hsplit : ∀ ω, coordIncr G s x t ω * coordIncr G s y t ω - (t : ℝ) * coordCov N x y =
      (a ω * b ω - (u : ℝ) * coordCov N x y) + (a ω * e ω + b ω * d ω +
        (d ω * e ω - ((t : ℝ) - u) * coordCov N x y)) := fun ω => by
    rw [coordIncr_split s x u t, coordIncr_split s y u t]; ring
  simp_rw [hsplit]
  -- the three cross/increment terms have zero set integral over `A ∈ 𝓖_{s+u}`
  have hAm : MeasurableSet A := 𝓖.le _ A hA
  have hmd : Measurable fun Z : Matrix (Fin N) (Fin N) ℂ => hermCoord N Z x :=
    (continuous_hermCoord x).measurable
  have hme : Measurable fun Z : Matrix (Fin N) (Fin N) ℂ => hermCoord N Z y :=
    (continuous_hermCoord y).measurable
  have hcross : ∀ (c : Ω → ℝ) (z : Fin N × Fin N), Measurable[𝓖 (s + u)] c → Integrable c Q →
      ∫ ω in A, c ω * hermCoord N (G (s + t) ω - G (s + u) ω) z ∂Q = 0 := by
    intro c z hc hci
    have e1 : ∫ ω in A, c ω * hermCoord N (G (s + t) ω - G (s + u) ω) z ∂Q =
        ∫ ω, A.indicator c ω * hermCoord N (G (s + t) ω - G (s + u) ω) z ∂Q := by
      rw [← integral_indicator hAm]
      congr 1; funext ω; by_cases h : ω ∈ A <;> simp [h]
    rw [e1, integral_mul_increment hG hst (hc.indicator hA) (continuous_hermCoord z).measurable,
      integral_incr_coord hG hst z, mul_zero]
  have hia : Integrable (fun ω => a ω * e ω) Q :=
    integrable_mul_increment hG hst (measurable_coordIncr hG s x u)
      (integrable_coordIncr hG s x u) hme (integrable_incr_coord hG hst y)
  have hib : Integrable (fun ω => b ω * d ω) Q :=
    integrable_mul_increment hG hst (measurable_coordIncr hG s y u)
      (integrable_coordIncr hG s y u) hmd (integrable_incr_coord hG hst x)
  have hde : Integrable (fun ω => d ω * e ω) Q :=
    integrable_increment hG hst (g := fun Z => hermCoord N Z x * hermCoord N Z y)
      (integrable_hermCoord_mul_gue _ x y)
  have hdeA : ∫ ω in A, d ω * e ω ∂Q = Q.real A * (((t : ℝ) - u) * coordCov N x y) := by
    have h1 := setIntegral_increment hG hst hA
      (g := fun Z => hermCoord N Z x * hermCoord N Z y) (hmd.mul hme)
    have h2 := integral_incr_coord_mul hG hst x y
    rw [h1, h2]; push_cast; ring
  have h0 : ∫ ω in A, (a ω * e ω + b ω * d ω +
      (d ω * e ω - ((t : ℝ) - u) * coordCov N x y)) ∂Q = 0 := by
    rw [integral_add (f := fun ω => a ω * e ω + b ω * d ω)
      (g := fun ω => d ω * e ω - ((t : ℝ) - u) * coordCov N x y)
      (hia.add hib).integrableOn (hde.sub (integrable_const _)).integrableOn,
      integral_add (f := fun ω => a ω * e ω) (g := fun ω => b ω * d ω)
        hia.integrableOn hib.integrableOn,
      integral_sub (f := fun ω => d ω * e ω) (g := fun _ => ((t : ℝ) - u) * coordCov N x y)
        hde.integrableOn (integrable_const _).integrableOn,
      hcross a y (measurable_coordIncr hG s x u) (integrable_coordIncr hG s x u),
      hcross b x (measurable_coordIncr hG s y u) (integrable_coordIncr hG s y u),
      hdeA, setIntegral_const]
    simp only [smul_eq_mul]
    ring
  rw [integral_add (f := fun ω => a ω * b ω - (u : ℝ) * coordCov N x y)
    (g := fun ω => a ω * e ω + b ω * d ω + (d ω * e ω - ((t : ℝ) - u) * coordCov N x y))
    ((integrable_coordIncr_mul hG s x y u).sub (integrable_const _)).integrableOn
    ((hia.add hib).add (hde.sub (integrable_const _))).integrableOn, h0, add_zero]

end BlockBand.SourceProcess.Stochastic.Dyson
