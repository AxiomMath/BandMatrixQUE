module

public import BlockBand.Endpoints.Clock.CavityMeanProbMean

/-!
# Analyticity of the cavity solution `u(z')`

We prove that the solution of the cavity equations is holomorphic in `z'`; the argument is
deterministic. For a finite law `(p, x)` (here `p_i = 1/W`, `x` the eigenvalues of
`X`), `b, c > 0` and any choice `s(z) = (v(z), u(z))` of solutions of the cavity equations with
negative imaginary parts on the upper half-plane (unique by `cavity_solution_unique`):
* `cavitySol_lipschitz`: `|v(z) - v(z₀)| + |u(z) - u(z₀)| ≤ C |z - z₀|` on every domain
  `Im ≥ η`, `|·| ≤ M`, by the stability theorem `cavity_stability` applied to the exact
  pair at `z₀` viewed as an approximate pair at `z`;
* `cavitySol_hasDerivAt_v`: `v` is complex differentiable, with
  `v'(z₀) = -K₀ b u₀² / (1 - K₀ (c + b² u₀²))`, `K₀ = Σ_i p_i (ζ₀ - x_i)⁻²`; the denominator is
  nonzero because `|K₀ (c + b²u₀²)| ≤ A (c + b²|u₀|²) ≤ 1 - δ` (the gap bound of `cavity_gap_lower_bound`). This replaces
  the implicit function theorem by a direct difference-quotient argument (same input: the nonzero
  stability denominator and uniqueness);
* `cavityU_differentiableOn`: the matrix solution `u = cavityU X b e` (`c = 1 - 2b`) is
  holomorphic on `{Im z' > 0}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Complex Filter Topology

open Classical in
/-- The solution pair of the cavity equations for the matrix `X` (`c = 1 - 2b`), chosen when it
exists (it exists and is unique for `Im z' > 0`, `cavityMatrix_existsUnique`). -/
def cavitySol {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (b e : ℝ) (z' : ℂ) : ℂ × ℂ :=
  if h : ∃ vu : ℂ × ℂ, IsCavityMatrixSolution X b (1 - 2 * b) e z' vu.1 vu.2 then h.choose
  else 0

/-- The port value `u(z')` of the cavity-mean lemma. -/
def cavityU {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (b e : ℝ) (z' : ℂ) : ℂ :=
  (cavitySol X b e z').2

/-- The physical value `v(z')` of the cavity-mean lemma. -/
def cavityV {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (b e : ℝ) (z' : ℂ) : ℂ :=
  (cavitySol X b e z').1

theorem cavitySol_spec {W : ℕ} (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (e : ℝ) {z' : ℂ} (hz : 0 < z'.im) :
    IsCavityMatrixSolution X b (1 - 2 * b) e z' (cavityV X b e z') (cavityU X b e z') := by
  have hc : 0 < 1 - 2 * b := by linarith
  obtain ⟨vu, h, -⟩ := cavityMatrix_existsUnique (e := e) hW hX hb0 hc hz
  have hex : ∃ vu : ℂ × ℂ, IsCavityMatrixSolution X b (1 - 2 * b) e z' vu.1 vu.2 := ⟨vu, h⟩
  unfold cavityV cavityU cavitySol
  split_ifs with h'
  · exact h'.choose_spec
  · exact absurd hex h'

namespace CavityMeanProb

variable {ι : Type} [Fintype ι] {p x : ι → ℝ} {b c e : ℝ}

/-- The kernel `K(ζ, ζ') = Σ_i p_i (ζ - x_i)⁻¹ (ζ' - x_i)⁻¹`. -/
def kerK (p x : ι → ℝ) (ζ ζ' : ℂ) : ℂ := ∑ i, (p i : ℂ) * ((ζ - x i)⁻¹ * (ζ' - x i)⁻¹)

theorem stieltjes_sub_eq {ζ ζ' : ℂ} (h : 0 < ζ.im) (h' : 0 < ζ'.im) :
    cavityStieltjes p x ζ - cavityStieltjes p x ζ' = kerK p x ζ ζ' * (ζ' - ζ) := by
  unfold cavityStieltjes kerK
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := CavityMean.sub_ofReal_ne_zero h (x i)
  have h2 := CavityMean.sub_ofReal_ne_zero h' (x i)
  field_simp
  ring

theorem norm_kerK_self_le (hp : IsCavityWeights p) (ζ : ℂ) :
    ‖kerK p x ζ ζ‖ ≤ cavitySq p x ζ := by
  unfold kerK cavitySq
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp.1 i), sq]

theorem arg_im_pos (hb : 0 < b) (hc : 0 < c) {v u : ℂ} (hv : v.im < 0) (hu : u.im < 0) :
    0 < (-(e : ℂ) - c * v - b * u).im := by
  have : (-(e : ℂ) - c * v - b * u).im = c * (-v.im) + b * (-u.im) := by simp; ring
  rw [this]; nlinarith

theorem port_den_im {b : ℝ} (hb : 0 ≤ b) {z v : ℂ} (hv : v.im ≤ 0) :
    z.im ≤ (z - (b : ℂ) * v).im := by
  rw [CavityMean.im_sub_mul]; nlinarith

/-- **Lipschitz dependence on `z'`** (from `cavity_stability`): there is `C = C(b, c, η, M)` such that two
solutions at `z, z₀` in `{Im ≥ η, |·| ≤ M}` satisfy `|v₀ - v| + |u₀ - u| ≤ C |z - z₀|`. -/
theorem cavitySol_lipschitz (hb : 0 < b) (hc : 0 < c) {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] (p x : ι → ℝ) (e : ℝ) (z z₀ v u v₀ u₀ : ℂ),
      IsCavityWeights p → η ≤ z.im → ‖z‖ ≤ M → η ≤ z₀.im → ‖z₀‖ ≤ M →
      IsCavitySolution p x b c e z v u → IsCavitySolution p x b c e z₀ v₀ u₀ →
      ‖v₀ - v‖ + ‖u₀ - u‖ ≤ C * ‖z - z₀‖ := by
  have hsc := Real.sqrt_pos.mpr hc
  have hast : 0 < 1 / (M + b / Real.sqrt c) := by positivity
  obtain ⟨Cs, hCs, hstab⟩ := cavity_stability hb hc hη hM hast
  refine ⟨Cs * (1 / η) ^ 2, by positivity, ?_⟩
  intro ι _ p x e z z₀ v u v₀ u₀ hp hz hzM hz₀ hz₀M hsol hsol₀
  obtain ⟨-, -, hul, -⟩ := cavity_apriori_bounds hp hb hc hη hz₀ hz₀M hsol₀
  obtain ⟨-, hw⟩ := cavity_imaginary_identities hsol₀
  have hsol₀' := hsol₀
  obtain ⟨h1, h2, hv₀, hu₀⟩ := hsol₀'
  have hport : η * ‖u₀‖ ^ 2 ≤ -u₀.im := by
    rw [hw]
    have : η ≤ z₀.im + b * (-v₀.im) := by nlinarith
    nlinarith [sq_nonneg ‖u₀‖]
  have hr1 : ‖v₀ - cavityStieltjes p x (-e - c * v₀ - b * u₀)‖ ≤ ‖z - z₀‖ * (1 / η) ^ 2 := by
    rw [← h1, sub_self, norm_zero]; positivity
  have hr2 : ‖u₀ - (z - b * v₀)⁻¹‖ ≤ ‖z - z₀‖ * (1 / η) ^ 2 := by
    have hd₀ : η ≤ (z₀ - (b : ℂ) * v₀).im := hz₀.trans (port_den_im hb.le hv₀.le)
    have hd : η ≤ (z - (b : ℂ) * v₀).im := hz.trans (port_den_im hb.le hv₀.le)
    have hn₀ := CavityMean.ne_zero_of_im_pos (hη.trans_le hd₀)
    have hn := CavityMean.ne_zero_of_im_pos (hη.trans_le hd)
    have heq : u₀ - (z - b * v₀)⁻¹ = (z - z₀) * ((z₀ - b * v₀)⁻¹ * (z - b * v₀)⁻¹) := by
      rw [h2]; field_simp; ring
    rw [heq, norm_mul, norm_mul, sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (CavityMean.norm_inv_le_of_im hη hd₀)
      (CavityMean.norm_inv_le_of_im hη hd) (norm_nonneg _) (by positivity)) (norm_nonneg _)
  have h := hstab ι p x e z v u v₀ u₀ (‖z - z₀‖ * (1 / η) ^ 2) hp hz hzM hsol hv₀.le hul hport
    hr1 hr2
  calc ‖v₀ - v‖ + ‖u₀ - u‖ ≤ Cs * (‖z - z₀‖ * (1 / η) ^ 2) := h
    _ = Cs * (1 / η) ^ 2 * ‖z - z₀‖ := by ring

section Deriv

variable (p x)

/-- The derivative candidate `v'(z₀) = -K₀ b u₀² / (1 - K₀ (c + b² u₀²))`. -/
def vDeriv (b c e : ℝ) (v₀ u₀ : ℂ) : ℂ :=
  -(kerK p x (-(e : ℂ) - c * v₀ - b * u₀) (-(e : ℂ) - c * v₀ - b * u₀) * b * u₀ * u₀) /
    (1 - kerK p x (-(e : ℂ) - c * v₀ - b * u₀) (-(e : ℂ) - c * v₀ - b * u₀) *
      (c + b ^ 2 * u₀ * u₀))

variable {p x}

/-- **The stability denominator is nonzero**: `1 - K₀ (c + b²u₀²) ≠ 0`. -/
theorem stab_den_ne_zero (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) {z₀ v₀ u₀ : ℂ}
    (hz : 0 < z₀.im) (h : IsCavitySolution p x b c e z₀ v₀ u₀) :
    1 - kerK p x (-(e : ℂ) - c * v₀ - b * u₀) (-(e : ℂ) - c * v₀ - b * u₀) *
      (c + b ^ 2 * u₀ * u₀) ≠ 0 := by
  have hgap := cavity_gap_lower_bound hp hb hc hz le_rfl le_rfl h
  have hδ := cavityGapConst_pos hb hc hz (norm_nonneg z₀)
  set ζ₀ : ℂ := -(e : ℂ) - c * v₀ - b * u₀
  have hK := norm_kerK_self_le (x := x) hp ζ₀
  have hq : ‖(c : ℂ) + b ^ 2 * u₀ * u₀‖ ≤ c + b ^ 2 * ‖u₀‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hc.le, norm_mul, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hb.le, sq ‖u₀‖, mul_assoc]
  have hA := CavityMean.cavitySq_nonneg x hp ζ₀
  have hprod : ‖kerK p x ζ₀ ζ₀ * (c + b ^ 2 * u₀ * u₀)‖ < 1 := by
    rw [norm_mul]
    calc ‖kerK p x ζ₀ ζ₀‖ * ‖(c : ℂ) + b ^ 2 * u₀ * u₀‖
        ≤ cavitySq p x ζ₀ * (c + b ^ 2 * ‖u₀‖ ^ 2) :=
          mul_le_mul hK hq (norm_nonneg _) hA
      _ ≤ 1 - cavityGapConst b c z₀.im ‖z₀‖ := hgap
      _ < 1 := by linarith
  intro h0
  have : kerK p x ζ₀ ζ₀ * (c + b ^ 2 * u₀ * u₀) = 1 := by linear_combination -h0
  rw [this, norm_one] at hprod
  exact lt_irrefl _ hprod

/-- **`v` is complex differentiable** at every `z₀` of the upper half-plane. -/
theorem cavitySol_hasDerivAt_v (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c)
    {s : ℂ → ℂ × ℂ} (hs : ∀ z : ℂ, 0 < z.im → IsCavitySolution p x b c e z (s z).1 (s z).2)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    HasDerivAt (fun z => (s z).1) (vDeriv p x b c e (s z₀).1 (s z₀).2) z₀ := by
  set η := z₀.im / 2 with hηdef
  have hη : 0 < η := by positivity
  set M := ‖z₀‖ + η with hMdef
  have hM : 0 ≤ M := by positivity
  obtain ⟨CL, hCL, hlip⟩ := cavitySol_lipschitz hb hc hη hM
  -- the neighbourhood `ball z₀ η`
  have hnear : ∀ z ∈ Metric.ball z₀ η, η ≤ z.im ∧ ‖z‖ ≤ M := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    rw [abs_le] at h1
    refine ⟨by linarith, ?_⟩
    calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by ring_nf
      _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ M := by linarith
  have hball : Metric.ball z₀ η ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hη
  set v₀ := (s z₀).1 with hv₀def
  set u₀ := (s z₀).2 with hu₀def
  have hsol₀ : IsCavitySolution p x b c e z₀ v₀ u₀ := hs z₀ hz₀
  have hlipz : ∀ z ∈ Metric.ball z₀ η, ‖(s z).1 - v₀‖ + ‖(s z).2 - u₀‖ ≤ CL * ‖z - z₀‖ := by
    intro z hz
    obtain ⟨h1, h2⟩ := hnear z hz
    have := hlip ι p x e z₀ z v₀ u₀ (s z).1 (s z).2 hp (by
      rw [hηdef]; linarith) (by rw [hMdef]; linarith [norm_nonneg z₀]) h1 h2 hsol₀
      (hs z (hη.trans_le h1))
    rwa [← norm_neg (z₀ - z), neg_sub] at this
  -- continuity of `v, u` at `z₀`
  have hcont : ∀ g : ℂ → ℂ, (∀ z ∈ Metric.ball z₀ η, ‖g z - g z₀‖ ≤ CL * ‖z - z₀‖) →
      Tendsto g (𝓝 z₀) (𝓝 (g z₀)) := by
    intro g hg
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun z => CL * ‖z - z₀‖) (𝓝 z₀) (𝓝 0) := by
      have : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝 z₀) (𝓝 0) := tendsto_norm_sub_self z₀
      simpa using this.const_mul CL
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hball] with z hz using hg z hz
  have hV : Tendsto (fun z => (s z).1) (𝓝 z₀) (𝓝 v₀) := hcont (fun z => (s z).1) fun z hz => by
    have := hlipz z hz; have := norm_nonneg ((s z).2 - u₀); linarith
  have hU : Tendsto (fun z => (s z).2) (𝓝 z₀) (𝓝 u₀) := hcont (fun z => (s z).2) fun z hz => by
    have := hlipz z hz; have := norm_nonneg ((s z).1 - v₀); linarith
  -- the argument `ζ(z)` and the kernel
  set ζ : ℂ → ℂ := fun z => -(e : ℂ) - c * (s z).1 - b * (s z).2 with hζdef
  set ζ₀ := ζ z₀
  have hζ : Tendsto ζ (𝓝 z₀) (𝓝 ζ₀) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hV)).sub (tendsto_const_nhds.mul hU)
  have hζ₀im : 0 < ζ₀.im := arg_im_pos hb hc hsol₀.2.2.1 hsol₀.2.2.2
  have hK : Tendsto (fun z => kerK p x (ζ z) ζ₀) (𝓝 z₀) (𝓝 (kerK p x ζ₀ ζ₀)) := by
    unfold kerK
    refine tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul ?_
    refine Tendsto.mul ?_ tendsto_const_nhds
    exact (hζ.sub tendsto_const_nhds).inv₀ (CavityMean.sub_ofReal_ne_zero hζ₀im (x i))
  set D : ℂ → ℂ := fun z => 1 - kerK p x (ζ z) ζ₀ * (c + b ^ 2 * (s z).2 * u₀) with hDdef
  have hD₀ : D z₀ ≠ 0 := stab_den_ne_zero hp hb hc hz₀ hsol₀
  have hDt : Tendsto D (𝓝 z₀) (𝓝 (D z₀)) :=
    tendsto_const_nhds.sub (hK.mul (tendsto_const_nhds.add
      ((tendsto_const_nhds.mul hU).mul tendsto_const_nhds)))
  have hDev : ∀ᶠ z in 𝓝 z₀, D z ≠ 0 := hDt.eventually_ne hD₀
  -- the difference-quotient identity
  have hident : ∀ z ∈ Metric.ball z₀ η, ((s z).1 - v₀) * D z =
      -(kerK p x (ζ z) ζ₀ * b * (s z).2 * u₀) * (z - z₀) := by
    intro z hz
    obtain ⟨h1, -⟩ := hnear z hz
    have hsol := hs z (hη.trans_le h1)
    have hζim : 0 < (ζ z).im := arg_im_pos hb hc hsol.2.2.1 hsol.2.2.2
    have hf := stieltjes_sub_eq (p := p) (x := x) hζim hζ₀im
    have hv : (s z).1 = cavityStieltjes p x (ζ z) := hsol.1
    have hv₀ : v₀ = cavityStieltjes p x ζ₀ := hsol₀.1
    have hdz := CavityMean.ne_zero_of_im_pos
      (hz₀.trans_le (port_den_im (z := z₀) hb.le hsol₀.2.2.1.le))
    have hdzz := CavityMean.ne_zero_of_im_pos
      ((hη.trans_le h1).trans_le (port_den_im (z := z) hb.le hsol.2.2.1.le))
    have hu : (s z).2 * (z - b * (s z).1) = 1 := by rw [hsol.2.1]; exact inv_mul_cancel₀ hdzz
    have hu₀ : u₀ * (z₀ - b * v₀) = 1 := by rw [hsol₀.2.1]; exact inv_mul_cancel₀ hdz
    set K := kerK p x (ζ z) ζ₀
    have hΔv : (s z).1 - v₀ = K * (c * ((s z).1 - v₀) + b * ((s z).2 - u₀)) := by
      have e1 : (s z).1 - v₀ = cavityStieltjes p x (ζ z) - cavityStieltjes p x ζ₀ := by
        rw [← hv, ← hv₀]
      have e2 : ζ₀ - ζ z = c * ((s z).1 - v₀) + b * ((s z).2 - u₀) := by
        simp only [hζdef, ζ₀, hv₀def, hu₀def]; ring
      rw [← e2, ← hf, e1]
    have hΔu : (s z).2 - u₀ = (s z).2 * u₀ * (b * ((s z).1 - v₀) - (z - z₀)) := by
      linear_combination u₀ * hu - (s z).2 * hu₀
    simp only [hDdef]
    rw [hΔu] at hΔv
    linear_combination hΔv
  -- the limit of the slopes
  rw [hasDerivAt_iff_tendsto_slope]
  have hlimit : Tendsto (fun z => -(kerK p x (ζ z) ζ₀ * b * (s z).2 * u₀) / D z) (𝓝 z₀)
      (𝓝 (vDeriv p x b c e v₀ u₀)) := by
    have := ((hK.mul (tendsto_const_nhds (x := (b : ℂ)))).mul hU).mul
      (tendsto_const_nhds (x := u₀))
    have h2 := this.neg.div hDt hD₀
    exact h2
  refine (hlimit.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ η ∧ D z ≠ 0 ∧ z ≠ z₀ := by
    have h1 : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ η := nhdsWithin_le_nhds hball
    have h2 : ∀ᶠ z in 𝓝[≠] z₀, D z ≠ 0 := nhdsWithin_le_nhds hDev
    have h3 : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := self_mem_nhdsWithin
    filter_upwards [h1, h2, h3] with z h1 h2 h3 using ⟨h1, h2, h3⟩
  filter_upwards [hev] with z ⟨hz, hDz, hzz⟩
  rw [slope_def_field, eq_div_iff (sub_ne_zero.mpr hzz), div_mul_eq_mul_div, div_eq_iff hDz]
  rw [← hident z hz]

/-- **`u` is complex differentiable** at every `z₀` of the upper half-plane. -/
theorem cavitySol_differentiableAt_u (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c)
    {s : ℂ → ℂ × ℂ} (hs : ∀ z : ℂ, 0 < z.im → IsCavitySolution p x b c e z (s z).1 (s z).2)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) : DifferentiableAt ℂ (fun z => (s z).2) z₀ := by
  have hv := cavitySol_hasDerivAt_v hp hb hc hs hz₀
  have hne : z₀ - (b : ℂ) * (s z₀).1 ≠ 0 :=
    CavityMean.ne_zero_of_im_pos (hz₀.trans_le (port_den_im hb.le (hs z₀ hz₀).2.2.1.le))
  have hd : HasDerivAt (fun z => (z - (b : ℂ) * (s z).1)⁻¹) _ z₀ :=
    ((hasDerivAt_id z₀).sub (hv.const_mul (b : ℂ))).inv hne
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun z => (z - (b : ℂ) * (s z).1)⁻¹) =ᶠ[𝓝 z₀] fun z => (s z).2 := by
    filter_upwards [hopen.mem_nhds hz₀] with z hz
    exact ((hs z hz).2.1).symm
  exact (hd.congr_of_eventuallyEq hev.symm).differentiableAt

end Deriv

end CavityMeanProb

open CavityMeanProb

/-- **Analyticity**: `u = cavityU X b e` (`c = 1 - 2b`, `0 < b < 1/2`, `W ≥ 1`,
Hermitian `X`) is holomorphic on `{Im z' > 0}`. -/
theorem cavityU_differentiableOn {W : ℕ} (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (e : ℝ) :
    DifferentiableOn ℂ (cavityU X b e) {z : ℂ | 0 < z.im} := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hs : ∀ z : ℂ, 0 < z.im → IsCavitySolution (fun _ => (W : ℝ)⁻¹) hX.eigenvalues b
      (1 - 2 * b) e z (cavitySol X b e z).1 (cavitySol X b e z).2 := fun z hz =>
    (isCavityMatrixSolution_iff hX hb0 hc).mp (cavitySol_spec hW hX hb0 hb1 e hz)
  intro z hz
  exact (cavitySol_differentiableAt_u (isCavityWeights_uniform hW) hb0 hc hs hz).differentiableWithinAt

end BlockBand.Endpoints.Clock
