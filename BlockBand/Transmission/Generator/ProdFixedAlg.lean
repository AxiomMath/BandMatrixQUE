module

public import BlockBand.Transmission.Generator.ProdTools
public import BlockBand.Transmission.Generator.ModProd
public import BlockBand.Transmission.Generator.ModPath

/-!
# The finite-`W` product: decomposition and the orthogonality identity

* `prodM`: the discrete `M^W_k = X^k_{r_t} - X^k_{r_s} - Σ_{r_s ≤ r < r_t} A_k(P_r)/W`;
  `bracketSum = Σ_{r_s ≤ r < r_t} B_{kl}(P_r)/W`; `driftSum = Σ_{u<n} driftError_{a+u}`;
* `prodM_eq`: `M^W_k = N^k_n + driftSum` pathwise (`modX_eq`);
* boundedness (`ModBdd`, defined elsewhere) of `driftError`, `bracketError`, `driftSum`
  (`modBdd_driftError`, `modBdd_bracketError`, `modBdd_driftSum`);
* **`prod_main_eq`**: `E[Φ N^kN^l] - E[Φ bracketSum] = Σ_u E[Φ bracketError] - Σ_u E[Φ d^kd^l]`
  (`integral_mul_modSum_mul_eq` + pull-out of `Φ` + the definition of `bracketError`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal

/-- The discrete drift martingale increment `M^W_k(r_s, r_t)`. -/
def prodM (b E E' : ℝ) (W k rs rt : ℕ) (ω : GrowthPath W) : ℝ :=
  pathPower b E' W k rt ω - pathPower b E' W k rs ω -
    ∑ r ∈ Ico rs rt, transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W

/-- The discrete bracket `Σ_{r_s ≤ r < r_t} B_{kl}(P_r)/W`. -/
def bracketSum (b E E' : ℝ) (W k l rs rt : ℕ) (ω : GrowthPath W) : ℝ :=
  ∑ r ∈ Ico rs rt, transmissionBracket (transportD0 b E) k l (pathPowers b E' W r ω) / W

/-- The summed drift errors `Σ_{u<n} driftError_{a+u}`. -/
def driftSum (b E E' : ℝ) (W k a n : ℕ) : GrowthPath W → ℝ :=
  ∑ u ∈ range n, driftError b E E' W k (a + u)

theorem abs_div_nat_le (x : ℝ) (W : ℕ) : |x / W| ≤ |x| := by
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp
  · rw [abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg _) (by exact_mod_cast h)

theorem modBdd_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : ℕ → Ω → ℝ}
    (hf : ∀ u, ModBdd μ (f u)) (n : ℕ) : ModBdd μ (∑ u ∈ range n, f u) := by
  induction n with
  | zero => exact ⟨aestronglyMeasurable_const, 0, ae_of_all _ fun _ => by simp⟩
  | succ n ih => rw [sum_range_succ]; exact ih.add (hf n)

section Fixed

variable {b E E' : ℝ} (hb : b < 1) (h1 : -2 < E') (h2 : E' < 2) (hD : 0 ≤ transportD0 b E)
  {W : ℕ}
include hb h1 h2 hD

omit hb h1 h2 hD in
theorem condExp_powerIncrement_eq (k r : ℕ) (ω : GrowthPath W) :
    ((growthPathLaw W b)[modInc (fun r => pathPower b E' W k r) r | growthFiltration W r]) ω =
      driftError b E E' W k r ω + transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W := by
  show ((growthPathLaw W b)[powerIncrement b E' W k r | growthSigma W r]) ω = _
  simp only [driftError, Pi.sub_apply]; ring

omit hb h1 h2 hD in
/-- **`M^W_k = N^k + Σ driftError`** pathwise. -/
theorem prodM_eq (k a n : ℕ) (ω : GrowthPath W) :
    prodM b E E' W k a (a + n) ω = modSum (growthPathLaw W b) (growthFiltration W)
      (fun r => pathPower b E' W k r) a n ω + driftSum b E E' W k a n ω := by
  have h := modX_eq (μ := growthPathLaw W b) (growthFiltration W)
    (fun r => pathPower b E' W k r) a n ω
  simp only [condExp_powerIncrement_eq (E := E)] at h
  simp only [prodM, driftSum, Finset.sum_apply, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    sum_add_distrib] at h ⊢
  linarith

omit hD in
theorem modBdd_pathPower {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    ModBdd (growthPathLaw W b) (pathPower b E' W k r) :=
  ⟨(measurable_pathPower b E' k r).aestronglyMeasurable, W, pathPower_bound hb h1 h2 hk r⟩

theorem modBdd_drift (k r : ℕ) : ModBdd (growthPathLaw W b) fun ω =>
    transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W :=
  ⟨((measurable_drift_pathPowers b E E' k r).mono (growthSigma_le W r) le_rfl).aestronglyMeasurable,
    _, drift_pathPowers_bound hb h1 h2 _ hD k r⟩

theorem modBdd_driftError {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    ModBdd (growthPathLaw W b) (driftError b E E' W k r) :=
  (modBdd_condExp_modInc (growthFiltration W) (X := fun r => pathPower b E' W k r)
    (fun r => pathPower_bound hb h1 h2 hk r) r).sub (modBdd_drift hb h1 h2 hD k r)

theorem modBdd_driftSum {k : ℕ} (hk : 1 ≤ k) (a n : ℕ) :
    ModBdd (growthPathLaw W b) (driftSum b E E' W k a n) :=
  modBdd_sum (fun u => modBdd_driftError hb h1 h2 hD hk (a + u)) n

theorem modBdd_bracket {k l : ℕ} (hk : 1 ≤ k) (r : ℕ) : ModBdd (growthPathLaw W b) fun ω =>
    transmissionBracket (transportD0 b E) k l (pathPowers b E' W r ω) / W := by
  have hm : Measurable fun ω => transmissionBracket (transportD0 b E) k l (pathPowers b E' W r ω) / W :=
    ((continuous_transmissionBracket (transportD0 b E) k l (v := fun x : ℕ → ℝ => x)
      fun j => continuous_apply j).measurable.comp
      (measurable_pi_iff.mpr fun j => measurable_pathPower b E' j r)).div_const _
  refine ⟨hm.aestronglyMeasurable, 2 * transportD0 b E * k * l * W, ?_⟩
  filter_upwards [pathPower_bound hb h1 h2 (k := k + l) (by omega) r,
    pathPower_bound hb h1 h2 (k := k + l + 1) (by omega) r] with ω hω1 hω2
  exact (abs_div_nat_le _ _).trans (abs_transmissionBracket_le hD k l hω1 hω2)

theorem modBdd_bracketError {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (r : ℕ) :
    ModBdd (growthPathLaw W b) (bracketError b E E' W k l r) := by
  have hk' := modBdd_modInc (growthFiltration W) (X := fun r => pathPower b E' W k r)
    (fun r => (measurable_pathPower_adapted b E' k r).stronglyMeasurable)
    (fun r => pathPower_bound hb h1 h2 hk r) r
  have hl' := modBdd_modInc (growthFiltration W) (X := fun r => pathPower b E' W l r)
    (fun r => (measurable_pathPower_adapted b E' l r).stronglyMeasurable)
    (fun r => pathPower_bound hb h1 h2 hl r) r
  obtain ⟨-, C, hC⟩ := hk'.mul hl'
  refine ModBdd.sub (f := (growthPathLaw W b)[fun ω => powerIncrement b E' W k r ω *
    powerIncrement b E' W l r ω | growthSigma W r]) ⟨(stronglyMeasurable_condExp.mono
      (growthSigma_le W r)).aestronglyMeasurable, C, ae_bdd_abs_condExp_of_ae_bdd_abs hC⟩
    (modBdd_bracket hb h1 h2 hD hk r)

/-- **The orthogonality identity at width `W`.** -/
theorem prod_main_eq {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (a n : ℕ) {Φ : GrowthPath W → ℝ}
    (hΦ : Measurable[growthSigma W a] Φ) {B : ℝ} (hB : ∀ ω, |Φ ω| ≤ B) :
    ∫ ω, Φ ω * (modSum (growthPathLaw W b) (growthFiltration W) (fun r => pathPower b E' W k r) a n ω *
        modSum (growthPathLaw W b) (growthFiltration W) (fun r => pathPower b E' W l r) a n ω)
        ∂growthPathLaw W b - ∫ ω, Φ ω * bracketSum b E E' W k l a (a + n) ω ∂growthPathLaw W b =
      ∑ u ∈ range n, ∫ ω, Φ ω * bracketError b E E' W k l (a + u) ω ∂growthPathLaw W b -
      ∑ u ∈ range n, ∫ ω, Φ ω * (((growthPathLaw W b)[modInc (fun r => pathPower b E' W k r)
        (a + u) | growthFiltration W (a + u)]) ω * ((growthPathLaw W b)[modInc
          (fun r => pathPower b E' W l r) (a + u) | growthFiltration W (a + u)]) ω)
        ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set F := growthFiltration W
  set Xk : ℕ → GrowthPath W → ℝ := fun r => pathPower b E' W k r
  set Xl : ℕ → GrowthPath W → ℝ := fun r => pathPower b E' W l r
  have hXk : ∀ r, StronglyMeasurable[F r] (Xk r) := fun r =>
    (measurable_pathPower_adapted b E' k r).stronglyMeasurable
  have hXl : ∀ r, StronglyMeasurable[F r] (Xl r) := fun r =>
    (measurable_pathPower_adapted b E' l r).stronglyMeasurable
  have hBk : ∀ r, ∀ᵐ ω ∂μ, |Xk r ω| ≤ W := fun r => pathPower_bound hb h1 h2 hk r
  have hBl : ∀ r, ∀ᵐ ω ∂μ, |Xl r ω| ≤ W := fun r => pathPower_bound hb h1 h2 hl r
  have hΦm : Measurable Φ := hΦ.mono (growthSigma_le W a) le_rfl
  have hΦB : ModBdd μ Φ := ⟨hΦm.aestronglyMeasurable, B, ae_of_all _ hB⟩
  have hΦb : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ B := ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hB ω
  rw [integral_mul_modSum_mul_eq F hXk hXl hBk hBl a n hΦ.stronglyMeasurable hΦB]
  -- each `E[ΦΔ^kΔ^l] = E[Φ bracketError] + E[Φ B/W]`
  have hstep : ∀ u ∈ range n, ∫ ω, Φ ω * (modInc Xk (a + u) ω * modInc Xl (a + u) ω) ∂μ =
      ∫ ω, Φ ω * bracketError b E E' W k l (a + u) ω ∂μ + ∫ ω, Φ ω *
        (transmissionBracket (transportD0 b E) k l (pathPowers b E' W (a + u) ω) / W) ∂μ := by
    intro u _
    have hΔ : Integrable (fun ω => modInc Xk (a + u) ω * modInc Xl (a + u) ω) μ :=
      ((modBdd_modInc F hXk hBk (a + u)).mul (modBdd_modInc F hXl hBl (a + u))).integrable
    rw [integral_mul_condExp_eq (growthSigma_le W (a + u))
      (hΦ.mono (growthSigma_mono (Nat.le_add_right a u)) le_rfl) hB hΔ]
    have hE := (modBdd_bracketError (W := W) hb h1 h2 hD hk hl (a + u)).integrable
    have hBr := (modBdd_bracket (W := W) (l := l) hb h1 h2 hD hk (a + u)).integrable
    rw [← integral_add (hE.bdd_mul hΦm.aestronglyMeasurable hΦb)
      (hBr.bdd_mul hΦm.aestronglyMeasurable hΦb)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    show Φ ω * (μ[fun ω => powerIncrement b E' W k (a + u) ω * powerIncrement b E' W l (a + u) ω |
      growthSigma W (a + u)]) ω = _
    simp only [bracketError, Pi.sub_apply]; ring
  rw [sum_congr rfl fun u hu => by rw [hstep u hu], sum_sub_distrib, sum_add_distrib]
  have hsumB : ∫ ω, Φ ω * bracketSum b E E' W k l a (a + n) ω ∂μ = ∑ u ∈ range n, ∫ ω, Φ ω *
      (transmissionBracket (transportD0 b E) k l (pathPowers b E' W (a + u) ω) / W) ∂μ := by
    simp only [bracketSum, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, mul_sum]
    exact integral_finsetSum _ fun u _ =>
      ((modBdd_bracket (W := W) (l := l) hb h1 h2 hD hk (a + u)).integrable.bdd_mul
        hΦm.aestronglyMeasurable hΦb)
  rw [hsumB]; ring

end Fixed

end BlockBand.Transmission.Generator
