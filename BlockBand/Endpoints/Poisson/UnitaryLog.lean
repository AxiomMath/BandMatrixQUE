module

public import BlockBand.Endpoints.Poisson.PhaseFractional
public import BlockBand.Endpoints.Poisson.UnitaryLogMatrix

/-!
# The unitary log-comparison lemma

We compare `log|det(I - ÛV₁)|` and `log|det(I - ÛV₀)|` in expectation over the fresh collar, for
two deterministic unitaries `V₀, V₁`. Steps 1–5 are those of the proof of the unitary
log-comparison lemma in the paper.

**Law and domain.** The fresh collar `collarLaw W b`, `U = collarScattering b e s ν` on the ports
`α = Fin 2 × Fin W`, `Û = U ⊕ 0` on `α ⊕ β` (`β` an arbitrary finite complement). `V₀, V₁` are
deterministic unitaries (independent of the collar). The hypothesis is `CollarKernelContract`,
through `phase_fractional_inverse`.

**Normalization.** `σ = Tr|V₁ - V₀|^p = fracTrace (p/2) ((V₁-V₀)*(V₁-V₀))` (`schattenFrac`,
sum of the `p`-th powers of the singular values), `g₀ = Tr(I - r₀*r₀)` (`conductance`),
`r₀ = P V₀ P`; `d(r₀)` is the scalar distance of the collar-kernel theorem written through
`(z_b - X)⁻¹ = (I - r)/(2iη)` (`scatteringDistance`). The real logarithm of the modulus is
`Real.log ‖det(…)‖`.

**Main content: the radial clause.** For every radial regulator `t ∈ (τ, 1)` both determinants
`det(I - tÛV_i)` are nonzero, and the bound `C_p (1 + g₀ + σ + 2W(1 - t²)) σ` is uniform in `t`;
it is derived from the radial clause of `phase_fractional_inverse` and involves no convention.

**Boundary convention.** The boundary clause follows by Fatou along `t ↑ 1`, using Lean's
`Real.log 0 = 0`: when both boundary determinants vanish the integrand is
`|log 0 - log 0| = 0`; when exactly one vanishes, the radial `liminf` is `+∞`
(`ofReal_abs_logGap_le_liminf`), so the finite bound forces that event to be null. The event
where both vanish is not controlled by the proof; it is empty for `ν > 0` and collarLaw-null for
`ν = 0` (by real-analyticity; this is not part of the library), so the boundary clause agrees with
the paper's quantity up to that null event.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

universe u

open MeasureTheory Matrix Filter Set
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder ComplexConjugate ENNReal Topology

/-- `Tr |A|^p = Σ_i s_i(A)^p = fracTrace (p/2) (A*A)`. -/
def schattenFrac {κ : Type*} [Fintype κ] [DecidableEq κ] (p : ℝ) (A : Matrix κ κ ℂ) : ℝ :=
  fracTrace (p / 2) (Aᴴ * A)

/-- `log |det(I - t Û V)|`. -/
def logDetCollar {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (t : ℝ) (U : Matrix α α ℂ) (V : Matrix (α ⊕ β) (α ⊕ β) ℂ) : ℝ :=
  Real.log ‖(1 - (t : ℂ) • (collarHat U * V)).det‖

/-!
## Scalar and bookkeeping facts
-/

theorem le_two_mul_rpow {x p : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (hp0 : 0 < p) (hp1 : p < 1) :
    x ≤ 2 * x ^ p := by
  rcases hx0.eq_or_lt with rfl | hx
  · simp [Real.zero_rpow hp0.ne']
  have h1 : x = x ^ (1 - p) * x ^ p := by
    rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]
  have h2 : x ^ (1 - p) ≤ 2 := by
    calc x ^ (1 - p) ≤ 2 ^ (1 - p) := Real.rpow_le_rpow hx.le hx2 (by linarith)
      _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  calc x = x ^ (1 - p) * x ^ p := h1
    _ ≤ 2 * x ^ p := by gcongr

theorem sum_norm_sub_one_le {κ : Type*} [Fintype κ] [DecidableEq κ] {ζ d : κ → ℂ} (j : κ)
    (h : ∀ i, i ≠ j → ‖d i - 1‖ ≤ ‖ζ i - 1‖) (hj : ‖d j‖ = 1) :
    ∑ i, ‖d i - 1‖ ≤ ∑ i, ‖ζ i - 1‖ + 2 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ (fun i => ‖ζ i - 1‖) (Finset.mem_univ j)]
  have h1 : ‖d j - 1‖ ≤ 2 := by
    have := norm_sub_le (d j) 1; rw [hj, norm_one] at this; linarith
  have h2 : ∑ i ∈ Finset.univ.erase j, ‖d i - 1‖ ≤ ∑ i ∈ Finset.univ.erase j, ‖ζ i - 1‖ :=
    Finset.sum_le_sum fun i hi => h i (Finset.ne_of_mem_erase hi)
  have h3 := norm_nonneg (ζ j - 1)
  linarith

theorem measurable_logDetCollar {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {U : Ω → Matrix α α ℂ} (hU : Measurable U) (t : ℝ)
    (V : Matrix (α ⊕ β) (α ⊕ β) ℂ) : Measurable (fun ω => logDetCollar t (U ω) V) := by
  unfold logDetCollar
  apply Real.measurable_log.comp
  apply measurable_norm.comp
  apply (continuous_id.matrix_det).measurable.comp
  apply measurable_matrix_sub measurable_const
  apply measurable_matrix_smul
  exact measurable_matrix_mul (measurable_collarHat hU) measurable_const

/-!
## Removing the radial factor pointwise
-/

theorem continuous_norm_det_one_sub_smul {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) : Continuous (fun t : ℝ => ‖(1 - (t : ℂ) • A).det‖) :=
  continuous_norm.comp (continuous_const.sub
    (Complex.continuous_ofReal.smul continuous_const)).matrix_det

/-- Pointwise Fatou input: the boundary log-gap (with `log 0 = 0`) is at most the radial
`liminf`; it is `+∞` when exactly one determinant vanishes. -/
theorem ofReal_abs_logGap_le_liminf {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A₀ A₁ : Matrix κ κ ℂ} (h₀ : IsContraction A₀) (h₁ : IsContraction A₁) :
    ENNReal.ofReal |Real.log ‖(1 - A₁).det‖ - Real.log ‖(1 - A₀).det‖| ≤
      liminf (fun t : ℝ => ENNReal.ofReal |Real.log ‖(1 - (t : ℂ) • A₁).det‖ -
        Real.log ‖(1 - (t : ℂ) • A₀).det‖|) (𝓝[<] 1) := by
  set f₀ := fun t : ℝ => ‖(1 - (t : ℂ) • A₀).det‖ with hf₀
  set f₁ := fun t : ℝ => ‖(1 - (t : ℂ) • A₁).det‖ with hf₁
  have hc₀ := continuous_norm_det_one_sub_smul A₀
  have hc₁ := continuous_norm_det_one_sub_smul A₁
  have h1₀ : f₀ 1 = ‖(1 - A₀).det‖ := by simp [hf₀]
  have h1₁ : f₁ 1 = ‖(1 - A₁).det‖ := by simp [hf₁]
  have hpos : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < f₀ t ∧ 0 < f₁ t := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact ⟨norm_pos_iff.mpr (h₀.smul_strict ht.1.le ht.2).isUnit_det.ne_zero,
      norm_pos_iff.mpr (h₁.smul_strict ht.1.le ht.2).isUnit_det.ne_zero⟩
  have hlim₀ : Tendsto f₀ (𝓝[<] 1) (𝓝 (f₀ 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (hc₀.tendsto 1)
  have hlim₁ : Tendsto f₁ (𝓝[<] 1) (𝓝 (f₁ 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (hc₁.tendsto 1)
  -- a function tending to `0` from above has `log → -∞`
  have hbot : ∀ f : ℝ → ℝ, Tendsto f (𝓝[<] 1) (𝓝 0) → (∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < f t) →
      Tendsto (fun t => Real.log (f t)) (𝓝[<] 1) atBot := by
    intro f hf hfp
    apply Real.tendsto_log_nhdsGT_zero.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hf, hfp⟩
  rw [← h1₀, ← h1₁]
  show _ ≤ liminf (fun t => ENNReal.ofReal |Real.log (f₁ t) - Real.log (f₀ t)|) (𝓝[<] 1)
  by_cases hz₀ : f₀ 1 = 0 <;> by_cases hz₁ : f₁ 1 = 0
  · rw [hz₀, hz₁]; simp
  · -- `log f₀ → -∞`, `log f₁ → log f₁(1)`
    have hb := hbot f₀ (hz₀ ▸ hlim₀) (hpos.mono fun t ht => ht.1)
    have hl : Tendsto (fun t => Real.log (f₁ t)) (𝓝[<] 1) (𝓝 (Real.log (f₁ 1))) :=
      (Real.continuousAt_log hz₁).tendsto.comp hlim₁
    have htop : Tendsto (fun t => |Real.log (f₁ t) - Real.log (f₀ t)|) (𝓝[<] 1) atTop := by
      have : Tendsto (fun t => Real.log (f₀ t) - Real.log (f₁ t)) (𝓝[<] 1) atBot :=
        hb.atBot_add hl.neg
      refine (tendsto_abs_atBot_atTop.comp this).congr fun t => ?_
      simp [abs_sub_comm]
    have h := (ENNReal.tendsto_ofReal_atTop.comp htop).liminf_eq
    simp only [Function.comp_def] at h
    rw [h]
    exact le_top
  · have hb := hbot f₁ (hz₁ ▸ hlim₁) (hpos.mono fun t ht => ht.2)
    have hl : Tendsto (fun t => Real.log (f₀ t)) (𝓝[<] 1) (𝓝 (Real.log (f₀ 1))) :=
      (Real.continuousAt_log hz₀).tendsto.comp hlim₀
    have htop : Tendsto (fun t => |Real.log (f₁ t) - Real.log (f₀ t)|) (𝓝[<] 1) atTop := by
      have : Tendsto (fun t => Real.log (f₁ t) - Real.log (f₀ t)) (𝓝[<] 1) atBot :=
        hb.atBot_add hl.neg
      exact tendsto_abs_atBot_atTop.comp this
    have h := (ENNReal.tendsto_ofReal_atTop.comp htop).liminf_eq
    simp only [Function.comp_def] at h
    rw [h]
    exact le_top
  · have hl₀ : Tendsto (fun t => Real.log (f₀ t)) (𝓝[<] 1) (𝓝 (Real.log (f₀ 1))) :=
      (Real.continuousAt_log hz₀).tendsto.comp hlim₀
    have hl₁ : Tendsto (fun t => Real.log (f₁ t)) (𝓝[<] 1) (𝓝 (Real.log (f₁ 1))) :=
      (Real.continuousAt_log hz₁).tendsto.comp hlim₁
    have : Tendsto (fun t => ENNReal.ofReal |Real.log (f₁ t) - Real.log (f₀ t)|) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal |Real.log (f₁ 1) - Real.log (f₀ 1)|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hl₁.sub hl₀).abs)
    rw [this.liminf_eq]

/-!
## The interpolation by rank-one twists (Step 1)
-/

section Interpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Step 1: `V₀ = T Q*` and `V₁ = T diag(ζ) Q*` with `T = V₀Q`, `Q` unitary,
`|ζ_j| = 1` (`V₀*V₁ = Q diag(ζ) Q*`). -/
theorem exists_interpolation {V₀ V₁ : Matrix ι ι ℂ} (hV₀ : V₀ᴴ * V₀ = 1) (hV₁ : V₁ᴴ * V₁ = 1) :
    ∃ (T Q : Matrix ι ι ℂ) (ζ : ι → ℂ), Tᴴ * T = 1 ∧ Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 ∧
      (∀ i, ‖ζ i‖ = 1) ∧ V₀ = diagConj T Q 1 ∧ V₁ = diagConj T Q ζ := by
  have hV₀' : V₀ * V₀ᴴ = 1 := mul_eq_one_comm.mp hV₀
  have hW : (V₀ᴴ * V₁)ᴴ * (V₀ᴴ * V₁) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc V₀,
      hV₀', Matrix.one_mul, hV₁]
  obtain ⟨Q, ζ, hQ, hQ', hζ, hdiag⟩ := exists_unitary_diagonalization hW
  refine ⟨V₀ * Q, Q, ζ, ?_, hQ, hQ', hζ, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V₀ᴴ, hV₀, Matrix.one_mul, hQ]
  · rw [diagConj, show (Matrix.diagonal (1 : ι → ℂ)) = 1 from diagonal_one, Matrix.mul_one,
      Matrix.mul_assoc, hQ', Matrix.mul_one]
  · rw [diagConj, Matrix.mul_assoc V₀, Matrix.mul_assoc V₀, ← hdiag,
      ← Matrix.mul_assoc, hV₀', Matrix.one_mul]

/-- The partial phase vectors `d_k`: the first `k` eigenphases (in the order `e`) switched on. -/
def partialPhase (e : ι ≃ Fin (Fintype.card ι)) (ζ : ι → ℂ) (k : ℕ) : ι → ℂ :=
  fun i => if (e i).val < k then ζ i else 1

omit [DecidableEq ι] in
theorem partialPhase_zero (e : ι ≃ Fin (Fintype.card ι)) (ζ : ι → ℂ) :
    partialPhase e ζ 0 = 1 := by
  funext i; simp [partialPhase]

omit [DecidableEq ι] in
theorem partialPhase_card (e : ι ≃ Fin (Fintype.card ι)) (ζ : ι → ℂ) :
    partialPhase e ζ (Fintype.card ι) = ζ := by
  funext i; simp [partialPhase, (e i).isLt]

omit [DecidableEq ι] in
theorem norm_partialPhase {ζ : ι → ℂ} (hζ : ∀ i, ‖ζ i‖ = 1) (e : ι ≃ Fin (Fintype.card ι))
    (k : ℕ) (i : ι) : ‖partialPhase e ζ k i‖ = 1 := by
  unfold partialPhase; split_ifs <;> simp [hζ]

omit [DecidableEq ι] in
theorem norm_partialPhase_sub_one_le (ζ : ι → ℂ) (e : ι ≃ Fin (Fintype.card ι)) (k : ℕ)
    (i : ι) : ‖partialPhase e ζ k i - 1‖ ≤ ‖ζ i - 1‖ := by
  unfold partialPhase; split_ifs <;> simp

theorem partialPhase_succ (e : ι ≃ Fin (Fintype.card ι)) (ζ : ι → ℂ)
    (k : Fin (Fintype.card ι)) :
    partialPhase e ζ (k + 1) =
      partialPhase e ζ k * Function.update (1 : ι → ℂ) (e.symm k) (ζ (e.symm k)) := by
  funext i
  simp only [partialPhase, Pi.mul_apply]
  by_cases h : i = e.symm k
  · subst h; simp
  · have h' : (e i).val ≠ k.val := by
      intro h''; apply h; rw [← Fin.ext_iff.mpr h'']; simp
    rw [Function.update_of_ne h, Pi.one_apply, mul_one]
    by_cases h2 : (e i).val < k.val
    · have h3 : (e i).val < k.val + 1 := by omega
      simp only [h2, h3, ↓reduceIte]
    · have h3 : ¬ (e i).val < k.val + 1 := by omega
      simp only [h2, h3, ↓reduceIte]

theorem twisted_partial_sum_le {ζ : ι → ℂ} (hζ : ∀ i, ‖ζ i‖ = 1) (e : ι ≃ Fin (Fintype.card ι))
    (k : ℕ) (j : ι) {u : ℂ} (hu : ‖u‖ = 1) :
    ∑ i, ‖(partialPhase e ζ k * Function.update (1 : ι → ℂ) j u) i - 1‖ ≤
      ∑ i, ‖ζ i - 1‖ + 2 := by
  apply sum_norm_sub_one_le j
  · intro i hi
    rw [Pi.mul_apply, Function.update_of_ne hi, Pi.one_apply, mul_one]
    exact norm_partialPhase_sub_one_le ζ e k i
  · rw [Pi.mul_apply, Function.update_self, norm_mul, norm_partialPhase hζ, hu, one_mul]

theorem col_unit {Q : Matrix ι ι ℂ} (hQ : Qᴴ * Q = 1) (j : ι) :
    star (fun x => Q x j) ⬝ᵥ (fun x => Q x j) = 1 := by
  have h := congrFun (congrFun hQ j) j
  rw [mul_apply, one_apply_eq] at h
  rw [← h, dotProduct]
  simp [conjTranspose_apply]

end Interpolation

/-!
## Summation along the interpolation (Steps 3–5) and the radial limit
-/

section Summation

variable {W : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

/-- Steps 3–5 at a fixed radial regulator `0 ≤ t < 1`: along unitaries `V_0, …, V_n` with
`V_{k+1} = V_k (I + (ζ_k - 1) w_k w_k*)`, if every fractional moment of the two endpoint
quadratic forms of every step is at most `B`, then
`E_U |log|det(I - tÛV_n)| - log|det(I - tÛV_0)|| ≤ 6p⁻¹ B Σ_k |ζ_k - 1|^p`. -/
theorem lintegral_logGap_le_of_steps {b e s ν : ℝ} (hη : 0 < (boundaryZ b e).im) (hν : 0 ≤ ν)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n : ℕ}
    (Vk : ℕ → Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ)
    (wk : Fin n → (Fin 2 × Fin W) ⊕ β → ℂ) (ζk : Fin n → ℂ)
    (hVku : ∀ k, (Vk k)ᴴ * Vk k = 1) (hwku : ∀ k, star (wk k) ⬝ᵥ wk k = 1)
    (hζk : ∀ k, ‖ζk k‖ = 1) (hstep : ∀ k : Fin n, Vk (k + 1) = Vk k * rankOneTwist (wk k) (ζk k))
    {B : ℝ} (hB : 0 ≤ B)
    (hmom : ∀ (m : ℕ) (k : Fin n), ∫⁻ ω, ENNReal.ofReal
      (‖fullQuad t (collarScattering b e s ν ω) (Vk m) (wk k)‖ ^ p) ∂collarLaw W b ≤
        ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal |logDetCollar t (collarScattering b e s ν ω) (Vk n) -
        logDetCollar t (collarScattering b e s ν ω) (Vk 0)| ∂collarLaw W b ≤
      ENNReal.ofReal (6 / p * B * ∑ k, ‖ζk k - 1‖ ^ p) := by
  have hUm := measurable_collarScattering b e s ν W
  have hUc : ∀ᵐ ω ∂collarLaw W b, IsContraction (collarScattering b e s ν ω) := by
    filter_upwards [ae_collar_hermitian W b] with ω hω
    exact isContraction_collarScattering (s := s) hη hν hω.1 hω.2
  set L : ℕ → CollarSample W → ℝ := fun k ω =>
    logDetCollar t (collarScattering b e s ν ω) (Vk k) with hL
  set a : Fin n → ℝ := fun k => ‖ζk k - 1‖ ^ p with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => Real.rpow_nonneg (norm_nonneg _) _
  have htel : ∀ ω, ENNReal.ofReal |L n ω - L 0 ω| ≤
      ∑ k : Fin n, ENNReal.ofReal |L (k + 1) ω - L k ω| := by
    intro ω
    have h1 : L n ω - L 0 ω = ∑ k : Fin n, (L (k + 1) ω - L k ω) := by
      rw [← Finset.sum_range_sub (fun k => L k ω) n, Finset.sum_range]
    rw [h1, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
  have hLm : ∀ k, Measurable (L k) := fun k => measurable_logDetCollar hUm t (Vk k)
  have hone : ∀ k : Fin n, ∫⁻ ω, ENNReal.ofReal |L (k + 1) ω - L k ω| ∂collarLaw W b ≤
      ENNReal.ofReal (6 / p * B * a k) := by
    intro k
    have hqm : ∀ m, Measurable (fun ω => ENNReal.ofReal
        (‖fullQuad t (collarScattering b e s ν ω) (Vk m) (wk k)‖ ^ p)) := fun m =>
      ENNReal.measurable_ofReal.comp
        (((measurable_fullQuad hUm t (Vk m) (wk k)).norm).pow_const p)
    have hc : 0 ≤ 3 / p * a k := by have := ha0 k; positivity
    calc ∫⁻ ω, ENNReal.ofReal |L (k + 1) ω - L k ω| ∂collarLaw W b
        ≤ ∫⁻ ω, ENNReal.ofReal (3 / p * a k) *
            (ENNReal.ofReal (‖fullQuad t (collarScattering b e s ν ω) (Vk k) (wk k)‖ ^ p) +
              ENNReal.ofReal (‖fullQuad t (collarScattering b e s ν ω) (Vk (k + 1)) (wk k)‖ ^
                p)) ∂collarLaw W b := by
          apply lintegral_mono_ae
          filter_upwards [hUc] with ω hω
          have h1 := abs_log_det_twist_le hω (hVku k) (hwku k) (hζk k) ht0 ht1 hp0 hp1.le
          rw [← hstep k] at h1
          rw [← ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (norm_nonneg _) _), ← ENNReal.ofReal_mul hc]
          apply ENNReal.ofReal_le_ofReal
          exact h1
      _ = ENNReal.ofReal (3 / p * a k) *
            (∫⁻ ω, ENNReal.ofReal (‖fullQuad t (collarScattering b e s ν ω) (Vk k) (wk k)‖ ^ p)
              ∂collarLaw W b + ∫⁻ ω, ENNReal.ofReal
                (‖fullQuad t (collarScattering b e s ν ω) (Vk (k + 1)) (wk k)‖ ^ p)
                ∂collarLaw W b) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hqm _)]
      _ ≤ ENNReal.ofReal (3 / p * a k) * (ENNReal.ofReal B + ENNReal.ofReal B) := by
          gcongr
          · exact hmom k k
          · exact hmom (k + 1) k
      _ = ENNReal.ofReal (6 / p * B * a k) := by
          rw [← ENNReal.ofReal_add hB hB, ← ENNReal.ofReal_mul hc]
          congr 1; ring
  calc ∫⁻ ω, ENNReal.ofReal |L n ω - L 0 ω| ∂collarLaw W b
      ≤ ∫⁻ ω, ∑ k : Fin n, ENNReal.ofReal |L (k + 1) ω - L k ω| ∂collarLaw W b :=
        lintegral_mono htel
    _ = ∑ k : Fin n, ∫⁻ ω, ENNReal.ofReal |L (k + 1) ω - L k ω| ∂collarLaw W b :=
        lintegral_finsetSum _ fun k _ =>
          ENNReal.measurable_ofReal.comp (((hLm _).sub (hLm _)).abs)
    _ ≤ ∑ k : Fin n, ENNReal.ofReal (6 / p * B * a k) := Finset.sum_le_sum fun k _ => hone k
    _ = ENNReal.ofReal (6 / p * B * ∑ k, a k) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by have := ha0 k; positivity),
          Finset.mul_sum]

/-- The radial limit `t ↑ 1` of a log-gap bound (Fatou; boundary log with `log 0 = 0`). -/
theorem lintegral_logGap_boundary_le {b e s ν : ℝ} (hη : 0 < (boundaryZ b e).im) (hν : 0 ≤ ν)
    {V₀ V₁ : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ} (hV₀ : V₀ᴴ * V₀ = 1)
    (hV₁ : V₁ᴴ * V₁ = 1) {τ : ℝ} (hτ1 : τ < 1) {F : ℝ → ℝ} {c : ℝ}
    (hF : Tendsto F (𝓝[<] 1) (𝓝 c))
    (hrad : ∀ t ∈ Ioo τ 1, ∫⁻ ω, ENNReal.ofReal
      |logDetCollar t (collarScattering b e s ν ω) V₁ -
        logDetCollar t (collarScattering b e s ν ω) V₀| ∂collarLaw W b ≤ ENNReal.ofReal (F t)) :
    ∫⁻ ω, ENNReal.ofReal
        |Real.log ‖(1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 * V₁).det‖ -
          Real.log ‖(1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 * V₀).det‖|
        ∂collarLaw W b ≤ ENNReal.ofReal c := by
  have hUm := measurable_collarScattering b e s ν W
  have hUc : ∀ᵐ ω ∂collarLaw W b, IsContraction (collarScattering b e s ν ω) := by
    filter_upwards [ae_collar_hermitian W b] with ω hω
    exact isContraction_collarScattering (s := s) hη hν hω.1 hω.2
  have hlim : Tendsto (fun t => ENNReal.ofReal (F t)) (𝓝[<] 1) (𝓝 (ENNReal.ofReal c)) :=
    (ENNReal.continuous_ofReal.tendsto c).comp hF
  calc ∫⁻ ω, ENNReal.ofReal
          |Real.log ‖(1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 * V₁).det‖ -
            Real.log ‖(1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 * V₀).det‖|
          ∂collarLaw W b
      ≤ ∫⁻ ω, liminf (fun t : ℝ => ENNReal.ofReal
          |logDetCollar t (collarScattering b e s ν ω) V₁ -
            logDetCollar t (collarScattering b e s ν ω) V₀|) (𝓝[<] 1) ∂collarLaw W b := by
        apply lintegral_mono_ae
        filter_upwards [hUc] with ω hω
        have hc₀ : IsContraction (collarHat (β := β) (collarScattering b e s ν ω) * V₀) :=
          (isContraction_fromBlocks_zero hω).mul (isContraction_of_unitary hV₀)
        have hc₁ : IsContraction (collarHat (β := β) (collarScattering b e s ν ω) * V₁) :=
          (isContraction_fromBlocks_zero hω).mul (isContraction_of_unitary hV₁)
        exact ofReal_abs_logGap_le_liminf hc₀ hc₁
    _ ≤ liminf (fun t : ℝ => ∫⁻ ω, ENNReal.ofReal
          |logDetCollar t (collarScattering b e s ν ω) V₁ -
            logDetCollar t (collarScattering b e s ν ω) V₀| ∂collarLaw W b) (𝓝[<] 1) := by
        apply lintegral_liminf_le
        intro t
        exact ENNReal.measurable_ofReal.comp (((measurable_logDetCollar hUm t V₁).sub
          (measurable_logDetCollar hUm t V₀)).abs)
    _ ≤ liminf (fun t : ℝ => ENNReal.ofReal (F t)) (𝓝[<] 1) :=
        liminf_le_liminf (by
          filter_upwards [Ioo_mem_nhdsLT hτ1] with t ht
          exact hrad t ht)
    _ = _ := hlim.liminf_eq

end Summation

/-!
## The unitary log-comparison lemma
-/

/-- **The unitary log-comparison lemma.** Fixed first: `0 < b < 1/2`, `κ > 0`. Then: the scalar
threshold `d₂ > 0` (the paper's `d_*/8`),
the small constant `c_* > 0`, the collar height/shift ranges `ν₀, s₀ > 0`, a radial threshold
`τ < 1` and `W₀`; then `p ∈ (0,1)` and `C_p ≥ 0`. Uniformly in `W ≥ W₀`,
`e ∈ bulkInterval κ`, `|s| ≤ s₀`, `0 ≤ ν ≤ ν₀`, the finite complement `β` and the
deterministic unitaries `V₀, V₁` on `(Fin 2 × Fin W) ⊕ β` with `d(r₀) ≤ d₂` and
`σ = Tr|V₁ - V₀|^p ≤ c_* W`, over the fresh collar `collarLaw W b`:
* (radial, the main content) for `t ∈ (τ, 1)`, uniformly in `t`:
  `E_U |log|det(I - tÛV₁)| - log|det(I - tÛV₀)|| ≤ C_p (1 + g₀ + σ + 2W(1-t²)) σ`;
* (boundary, by Fatou) `E_U |log|det(I - ÛV₁)| - log|det(I - ÛV₀)|| ≤ C_p (1 + g₀ + σ) σ`
  with `Real.log 0 = 0`: the integrand is `0` where both determinants vanish, and the event where
  exactly one vanishes is forced null (Fatou gives `+∞` there),
`g₀ = Tr(I - r₀*r₀)`, `r₀ = P V₀ P`. Expectations are lower Lebesgue integrals. -/
theorem unitary_log_comparison (hK : CollarKernelContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (d₂ cstar s₀ ν₀ τ : ℝ) (W₀ : ℕ), 0 < d₂ ∧ 0 < cstar ∧ 0 < s₀ ∧ 0 < ν₀ ∧ 0 ≤ τ ∧ τ < 1 ∧
      ∀ p : ℝ, 0 < p → p < 1 → ∃ Cp : ℝ, 0 ≤ Cp ∧
        ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Icc (-s₀) s₀,
        ∀ ν ∈ Icc 0 ν₀, ∀ (β : Type u) [Fintype β] [DecidableEq β]
          (V₀ V₁ : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ),
          V₀ᴴ * V₀ = 1 → V₁ᴴ * V₁ = 1 →
          scatteringDistance b e V₀.toBlocks₁₁ ≤ d₂ → schattenFrac p (V₁ - V₀) ≤ cstar * W →
          (∀ t ∈ Ioo τ 1, ∫⁻ ω, ENNReal.ofReal |logDetCollar t (collarScattering b e s ν ω) V₁ -
              logDetCollar t (collarScattering b e s ν ω) V₀| ∂collarLaw W b ≤
            ENNReal.ofReal (Cp * (1 + conductance V₀.toBlocks₁₁ + schattenFrac p (V₁ - V₀) +
              (1 - t ^ 2) * (2 * W)) * schattenFrac p (V₁ - V₀))) ∧
          ∫⁻ ω, ENNReal.ofReal
              |Real.log ‖(1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 * V₁).det‖ -
                Real.log ‖(1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 * V₀).det‖|
              ∂collarLaw W b ≤
            ENNReal.ofReal (Cp * (1 + conductance V₀.toBlocks₁₁ + schattenFrac p (V₁ - V₀)) *
              schattenFrac p (V₁ - V₀)) := by
  obtain ⟨d₁, s₀, ν₀, τ, W₀, hd₁, hs₀, hν₀, hτ0, hτ1, hPF⟩ := phase_fractional_inverse.{u} hK
    hb0 hb1 hκ
  have hb1' : b < 1 := by linarith
  have hηm := etaMin_pos hb1' hκ
  set ηm := etaMin b κ with hηmdef
  refine ⟨d₁ / 2, ηm * d₁ / 4, s₀, ν₀, τ, max W₀ ⌈4 / (ηm * d₁)⌉₊, by positivity,
    by positivity, hs₀, hν₀, hτ0, hτ1, ?_⟩
  intro p hp0 hp1
  obtain ⟨Cp1, hCp1, hPFp⟩ := hPF p hp0 hp1
  refine ⟨30 * Cp1 / p, by positivity, ?_⟩
  intro W hW hW₀ e he s hs ν hν β _ _ V₀ V₁ hV₀ hV₁ hdist hσ
  have hW₀' : W₀ ≤ W := (le_max_left _ _).trans hW₀
  have hWbig : 4 / (ηm * d₁) ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hW₀)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hη := boundaryZ_im_pos hb1' hκ he
  have hηge := boundaryZ_im_ge hb1' hκ he
  have hprob := isProbabilityMeasure_collarLaw W b
  obtain ⟨T, Q, ζ, hT, hQ, hQ', hζ, hV₀e, hV₁e⟩ := exists_interpolation hV₀ hV₁
  -- `σ = Σ_j |ζ_j - 1|^p` and `Σ_j |ζ_j - 1| ≤ 2σ`
  set σ := schattenFrac p (V₁ - V₀) with hσdef
  have hσeq : σ = ∑ i, ‖ζ i - 1‖ ^ p := by
    rw [hσdef, schattenFrac, hV₀e, hV₁e, fracTrace_diagConj_sub hT hQ' ζ p]
  set S₁ := ∑ i, ‖ζ i - 1‖ with hS₁
  have hS₁σ : S₁ ≤ 2 * σ := by
    rw [hσeq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => le_two_mul_rpow (norm_nonneg _) ?_ hp0 hp1
    have := norm_sub_le (ζ i) 1; rw [hζ i, norm_one] at this; linarith
  have hσ0 : 0 ≤ σ := by
    rw [hσeq]; exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hr₀ : IsContraction V₀.toBlocks₁₁ :=
    isContraction_toBlocks₁₁ (isContraction_of_unitary hV₀)
  set g₀ := conductance V₀.toBlocks₁₁ with hg₀
  have hg₀0 : 0 ≤ g₀ := conductance_nonneg hr₀
  set G := g₀ + 4 * σ + 4 with hG
  -- the hypotheses of the phase fractional-inverse lemma along the interpolation
  have hhyp : ∀ d' : (Fin 2 × Fin W) ⊕ β → ℂ, ∑ i, ‖d' i - 1‖ ≤ S₁ + 2 →
      scatteringDistance b e (diagConj T Q d').toBlocks₁₁ ≤ d₁ ∧
        conductance (diagConj T Q d').toBlocks₁₁ ≤ G := by
    intro d' hd'
    constructor
    · have h1 := scatteringDistance_le hη V₀.toBlocks₁₁ (diagConj T Q d').toBlocks₁₁
        (B := (W : ℝ)⁻¹ * (S₁ + 2)) (fun j => by
          rw [hV₀e]
          exact (norm_blockTrace_diagConj_sub_le hT hQ d' j).trans
            (mul_le_mul_of_nonneg_left hd' (by positivity)))
      have h2 : (W : ℝ)⁻¹ * (S₁ + 2) / (2 * (boundaryZ b e).im) ≤ d₁ / 2 := by
        have hσW : σ ≤ ηm * d₁ / 4 * W := hσ
        have h3 : (W : ℝ)⁻¹ * (S₁ + 2) ≤ ηm * d₁ / 2 + 2 / W := by
          rw [inv_mul_eq_div, div_le_iff₀ hWpos]
          have : 2 / (W : ℝ) * W = 2 := by field_simp
          nlinarith
        have h4 : 2 / (W : ℝ) ≤ ηm * d₁ / 2 := by
          rw [div_le_iff₀ hWpos]
          have := (div_le_iff₀ (by positivity : 0 < ηm * d₁)).mp hWbig
          nlinarith
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    · have h1 := conductance_diagConj_le hT hQ (by rw [← hV₀e]; exact hr₀) d'
      rw [← hV₀e] at h1
      linarith
  -- the interpolating unitaries
  set n := Fintype.card ((Fin 2 × Fin W) ⊕ β) with hn
  set eq := Fintype.equivFin ((Fin 2 × Fin W) ⊕ β) with heq
  set Vk : ℕ → Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ :=
    fun k => diagConj T Q (partialPhase eq ζ k) with hVk
  have hVk0 : Vk 0 = V₀ := by
    simp only [hVk, partialPhase_zero]; exact hV₀e.symm
  have hVkn : Vk n = V₁ := by
    simp only [hVk, hn, partialPhase_card]; exact hV₁e.symm
  have hVku : ∀ k, (Vk k)ᴴ * Vk k = 1 := fun k =>
    diagConj_unitary hT hQ' (norm_partialPhase hζ eq k)
  set jk : Fin n → (Fin 2 × Fin W) ⊕ β := fun k => eq.symm k with hjk
  set wk : Fin n → (Fin 2 × Fin W) ⊕ β → ℂ := fun k x => Q x (jk k) with hwk
  have hwku : ∀ k, star (wk k) ⬝ᵥ wk k = 1 := fun k => col_unit hQ (jk k)
  have htwist : ∀ (m : ℕ) (k : Fin n) (u : ℂ), Vk m * rankOneTwist (wk k) u =
      diagConj T Q (partialPhase eq ζ m * Function.update (1 : (Fin 2 × Fin W) ⊕ β → ℂ) (jk k) u) := by
    intro m k u
    rw [hVk, hwk, rankOneTwist_eq_diagConj hQ' (jk k) u, diagConj_mul hQ]
  have hstep : ∀ k : Fin n, Vk (k + 1) = Vk k * rankOneTwist (wk k) (ζ (jk k)) := by
    intro k
    rw [htwist, hVk]
    simp only
    rw [partialPhase_succ]
  -- fractional moments at both endpoints of every step
  have hmom : ∀ (m : ℕ) (k : Fin n), ∀ t ∈ Ioo τ 1,
      ∫⁻ ω, ENNReal.ofReal (‖fullQuad t (collarScattering b e s ν ω) (Vk m) (wk k)‖ ^ p)
        ∂collarLaw W b ≤ ENNReal.ofReal (Cp1 * (1 + G + (1 - t ^ 2) * (2 * W))) := by
    intro m k t ht
    refine ((hPFp W hW hW₀' e he s hs ν hν β (Vk m) (hVku m) (wk k) (hwku k) G
      (fun θ => ?_) (fun θ => ?_)).1 t ht)
    · rw [twistedV, htwist]
      exact (hhyp _ (twisted_partial_sum_le hζ eq m (jk k) (norm_exp_mul_I θ))).1
    · rw [twistedV, htwist]
      exact (hhyp _ (twisted_partial_sum_le hζ eq m (jk k) (norm_exp_mul_I θ))).2
  -- the radial bound
  have hrad : ∀ t ∈ Ioo τ 1, ∫⁻ ω, ENNReal.ofReal
      |logDetCollar t (collarScattering b e s ν ω) V₁ -
        logDetCollar t (collarScattering b e s ν ω) V₀| ∂collarLaw W b ≤
      ENNReal.ofReal (30 * Cp1 / p * (1 + g₀ + σ + (1 - t ^ 2) * (2 * W)) * σ) := by
    intro t ht
    have ht0 : 0 ≤ t := hτ0.trans ht.1.le
    have hx : 0 ≤ (1 - t ^ 2) * (2 * W) := mul_nonneg (by nlinarith [ht.2]) (by positivity)
    have hB : 0 ≤ Cp1 * (1 + G + (1 - t ^ 2) * (2 * W)) := mul_nonneg hCp1 (by linarith)
    have key := lintegral_logGap_le_of_steps hη hν.1 ht0 ht.2 hp0 hp1 Vk wk (fun k => ζ (jk k))
      hVku hwku (fun k => hζ _) hstep hB (fun m k => hmom m k t ht)
    rw [hVkn, hVk0] at key
    have hsuma : ∑ k : Fin n, ‖ζ (jk k) - 1‖ ^ p = σ := by
      rw [hσeq, hjk]
      exact Equiv.sum_comp eq.symm (fun i => ‖ζ i - 1‖ ^ p)
    rw [hsuma] at key
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have h5 : 1 + G + (1 - t ^ 2) * (2 * W) ≤ 5 * (1 + g₀ + σ + (1 - t ^ 2) * (2 * W)) := by
      rw [hG]; nlinarith
    have h6 : 0 ≤ 6 / p * Cp1 * σ := by positivity
    calc 6 / p * (Cp1 * (1 + G + (1 - t ^ 2) * (2 * W))) * σ
        = 6 / p * Cp1 * σ * (1 + G + (1 - t ^ 2) * (2 * W)) := by ring
      _ ≤ 6 / p * Cp1 * σ * (5 * (1 + g₀ + σ + (1 - t ^ 2) * (2 * W))) :=
          mul_le_mul_of_nonneg_left h5 h6
      _ = _ := by ring
  refine ⟨hrad, ?_⟩
  -- the boundary bound: Fatou along `t ↑ 1`
  apply lintegral_logGap_boundary_le hη hν.1 hV₀ hV₁ hτ1 _ hrad
  apply tendsto_nhdsWithin_of_tendsto_nhds
  have hc : Continuous (fun t : ℝ => 30 * Cp1 / p * (1 + g₀ + σ + (1 - t ^ 2) * (2 * W)) * σ) := by
    fun_prop
  simpa using hc.tendsto 1

end BlockBand.Endpoints.PhaseFractional
