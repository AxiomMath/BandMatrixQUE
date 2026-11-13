module

public import BlockBand.Internal.Contracts.Layers

/-!
# Gaussian inputs of the Gaussian absorption lemma: small balls for the bonds

For a fixed unit vector `v = (v1,v2)`, in the separate-port case
`‖B*v‖² =law (b/W)(‖v1‖²G1 + ‖v2‖²G2)` with `G_i` independent gamma variables of shape `W`, and
at least one coefficient is at least `1/2`; in the common-port case `B*v` is directly a circular
Gaussian vector with covariance `bI/W`. In either case `P(‖B*v‖ < t) ≤ (C_b t²)^W`.

## Laws and normalization

* `whiteNoise κ v` is the product of `|κ|` independent `gaussianReal 0 v`.
* `ginibreMeasure ι κ t` is the image of `whiteNoise (ι × κ × Fin 2) (t/2)` under
  `ginibreAssemble` (definitional), so `E|B_ij|² = t`; the layer bonds have `t = b/W`, i.e.
  `E|B_ij|² = b/W`.
* `bondLaw k p W t` is the bond factor of `layerLaw`: `layerLaw W b σ` is by definition
  `(Π_a GUE_W(c/W)).prod (bondLaw σ.blocks σ.ports W (b/W))`.

## Results

* `whiteNoise_sum_sq_lt` (clause 1, chi-square small ball, Chernoff route): if
  `|κ| = 2m` and `s > 0`, `P(Σ_k x_k² < s) ≤ (e s/(2 m v))^m`. For a circular Gaussian
  matrix (`ginibreMeasure_frobenius_le`): `P(Σ |g_xy|² ≤ s) ≤ (e s/(n t))^n`, `n` the number
  of complex entries (`ι = Fin m`, `κ = Fin 1` is a circular vector). This is the Gamma(n,1)
  CDF bound `P(G < x) ≤ (e x/n)^n`, weaker than `x^n/n!` by the factor `e^n n!/n^n ≤ e √n`;
  only the form `(C x/n)^n` is used below.
* `whiteNoise_map_linear` (rotation invariance): a linear image of white noise by a real
  matrix `M` with `MMᵀ = m I` is white noise of variance `m v` (characteristic functions).
* `bondLaw_smallBall`, `layerLaw_bond_smallBall`, `layerLaw_bond_smallBall_norm` (clause 2):
  for each of the four `LayerShape`s, `W ≥ 1`, `b > 0`, a deterministic unit vector `v` on
  the physical sites and `τ > 0`, `P(‖(bondMatrix σ B)ᴴ v‖ < τ) ≤ ((2e/b) τ²)^W`
  (Euclidean norms). The constant `C_b = 2e/b` depends only on `b`; the bound is uniform in
  `W`, the shape and `v`. Route: for a port `j` whose incident blocks carry mass
  `m_j = Σ_{a ~ j} ‖v_a‖² ≥ 1/2` (`exists_port_mass_ge`), the port-`j` component of `B*v` is a
  circular Gaussian vector of covariance `(b/W) m_j I` (`whiteNoise_map_linear`), and the
  small ball above applies.
* Clause 3 (operator-norm tail), with the `1/4`-nets of the unit spheres as explicit
  hypotheses (finite sets of unit vectors covering the sphere at distance `1/4`):
  `ginibre_pair_tail` / `bondLaw_pair_tail` (for unit `u, w`, `Re⟨u, B w⟩` is centered
  Gaussian of variance `≤ t/2`, so `P(Re⟨u,Bw⟩ ≥ a) ≤ exp(-a²/t)`), `opNorm_lt_of_net`
  (deterministic: `Re⟨n, A n'⟩ < c` on the nets implies `‖A‖ < 2c`),
  `measure_opNorm_ge_of_net` (union bound), and the tails
  `ginibre_opNorm_tail_of_net`: `P(‖B‖ ≥ a) ≤ |Nu||Nw| exp(-a²/(4t))` for `B ~ Gin(t)`, and
  `layerLaw_bondMatrix_opNorm_tail_of_net`:
  `P(‖bondMatrix σ B‖ ≥ a) ≤ |Nu||Nw| exp(-a² W/(4b))` under `layerLaw W b σ`
  (`L²` operator norm, `Matrix.Norms.L2Operator`).

Not in this module: the existence of the nets with `|N| ≤ 12^{dim_ℝ}` (module `Nets`, not imported), and the moment bound
`E(1 + ‖bondMatrix σ B‖)^q ≤ C₂^q`, `1 ≤ q ≤ W`, which follows from the tail above by
integrating it against `q (1+a)^{q-1}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

/-- Real white noise: `|κ|` independent centered real Gaussians of variance `v`. -/
def whiteNoise (κ : Type*) [Fintype κ] (v : ℝ≥0) : Measure (κ → ℝ) :=
  Measure.pi fun _ : κ => gaussianReal 0 v

/-- White noise is a probability measure. -/
instance isProbabilityMeasure_whiteNoise (κ : Type*) [Fintype κ] (v : ℝ≥0) :
    IsProbabilityMeasure (whiteNoise κ v) := by
  unfold whiteNoise; infer_instance

/-- `E exp(-l X²) = (1 + 2 l v)^{-1/2}` for `X ~ N(0, v)`, `v > 0`, `l ≥ 0`. -/
theorem integral_exp_neg_mul_sq_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {l : ℝ} (hl : 0 ≤ l) :
    ∫ x, Real.exp (-l * x ^ 2) ∂gaussianReal 0 v = (Real.sqrt (1 + 2 * l * v))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  have h1 : ∀ x : ℝ, gaussianPDFReal 0 v x • Real.exp (-l * x ^ 2) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-((2 * (v : ℝ))⁻¹ + l) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal_def, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h1]
  rw [integral_const_mul, integral_gaussian]
  have h2 : Real.pi / ((2 * (v : ℝ))⁻¹ + l) = (2 * Real.pi * v) / (1 + 2 * l * v) := by
    field_simp
  have hA : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity)
  rw [h2, Real.sqrt_div (by positivity), div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hA.ne',
    one_mul]

/-- **Chi-square small ball** (clause 1, Chernoff route): for `|κ| = 2m`, `v > 0`, `s > 0`,
`P(Σ_k x_k² ≤ s) ≤ (e s/(2 m v))^m` under `whiteNoise κ v`. -/
theorem whiteNoise_sum_sq_le {κ : Type*} [Fintype κ] {v : ℝ≥0} (hv : v ≠ 0) {m : ℕ}
    (hm : Fintype.card κ = 2 * m) {s : ℝ} (hs : 0 < s) :
    whiteNoise κ v {x | ∑ k, x k ^ 2 ≤ s} ≤
      ENNReal.ofReal ((Real.exp 1 * s / (2 * m * v)) ^ m) := by
  rcases Nat.eq_zero_or_pos m with h0 | hmpos
  · subst h0; simp [prob_le_one]
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  set l : ℝ := m / s with hl
  have hl0 : 0 < l := by positivity
  set f : (κ → ℝ) → ℝ := fun x => ∏ k, Real.exp (-l * x k ^ 2) with hf
  have hfint : Integrable f (whiteNoise κ v) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine Finset.prod_le_one₀ (fun _ _ => by positivity) (fun k _ => ?_)
    rw [Real.exp_le_one_iff]
    have := sq_nonneg (x k)
    nlinarith
  have hint : ∫ x, f x ∂(whiteNoise κ v) = ((Real.sqrt (1 + 2 * l * v))⁻¹) ^ (2 * m) := by
    simp only [hf, whiteNoise]
    rw [integral_fintype_prod_eq_prod (f := fun _ x => Real.exp (-l * x ^ 2))]
    simp only [integral_exp_neg_mul_sq_gaussianReal hv hl0.le, Finset.prod_const,
      Finset.card_univ, hm]
  have hmark := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => by positivity) hfint
    (Real.exp (-l * s))
  have hsub : {x : κ → ℝ | ∑ k, x k ^ 2 ≤ s} ⊆ {x | Real.exp (-l * s) ≤ f x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [hf]
    simp only
    rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    nlinarith
  have hreal : (whiteNoise κ v).real {x | ∑ k, x k ^ 2 ≤ s} ≤
      Real.exp (l * s) * ((Real.sqrt (1 + 2 * l * v))⁻¹) ^ (2 * m) := by
    have h3 := measureReal_mono (μ := whiteNoise κ v) hsub
    rw [hint] at hmark
    have he : 0 < Real.exp (-l * s) := Real.exp_pos _
    have : (whiteNoise κ v).real {x | Real.exp (-l * s) ≤ f x} ≤
        Real.exp (l * s) * ((Real.sqrt (1 + 2 * l * v))⁻¹) ^ (2 * m) := by
      rw [show Real.exp (l * s) = (Real.exp (-l * s))⁻¹ by rw [← Real.exp_neg]; ring_nf]
      rw [le_inv_mul_iff₀ he]
      exact hmark
    linarith
  have hbound : Real.exp (l * s) * ((Real.sqrt (1 + 2 * l * v))⁻¹) ^ (2 * m) ≤
      (Real.exp 1 * s / (2 * m * v)) ^ m := by
    have hls : l * s = m := by rw [hl]; field_simp
    rw [hls, pow_mul, inv_pow, Real.sq_sqrt (by positivity)]
    have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [hexp, div_pow, mul_pow]
    have h4 : (2 * (m : ℝ) * v / s) ^ m ≤ (1 + 2 * l * v) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      rw [hl]; field_simp; linarith
    have h5 : 0 < (2 * (m : ℝ) * v / s) ^ m := by positivity
    rw [inv_pow]
    calc Real.exp 1 ^ m * ((1 + 2 * l * v) ^ m)⁻¹
          ≤ Real.exp 1 ^ m * ((2 * (m : ℝ) * v / s) ^ m)⁻¹ := by gcongr
      _ = Real.exp 1 ^ m * s ^ m / (2 * m * v) ^ m := by
          rw [div_pow]; field_simp
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hreal.trans hbound)

/-- Strict-inequality form of `whiteNoise_sum_sq_le`. -/
theorem whiteNoise_sum_sq_lt {κ : Type*} [Fintype κ] {v : ℝ≥0} (hv : v ≠ 0) {m : ℕ}
    (hm : Fintype.card κ = 2 * m) {s : ℝ} (hs : 0 < s) :
    whiteNoise κ v {x | ∑ k, x k ^ 2 < s} ≤
      ENNReal.ofReal ((Real.exp 1 * s / (2 * m * v)) ^ m) := by
  refine (measure_mono ?_).trans (whiteNoise_sum_sq_le hv hm hs)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact hx.le

/-- **Rotation invariance of white noise.** If the real matrix `M : κ × ι` satisfies
`‖Mᵀ t‖² = m ‖t‖²` for all `t` (i.e. `M Mᵀ = m I`), then `x ↦ M x` maps `whiteNoise ι v` to
`whiteNoise κ (m v)`. Proof by characteristic functions (`charFun_eq_pi_iff`). -/
theorem whiteNoise_map_linear {ι κ : Type*} [Fintype ι] [Fintype κ] (v m : ℝ≥0)
    (M : κ → ι → ℝ) (hM : ∀ t : κ → ℝ, ∑ i, (∑ k, t k * M k i) ^ 2 = m * ∑ k, t k ^ 2) :
    (whiteNoise ι v).map (fun x k => ∑ i, M k i * x i) = whiteNoise κ (m * v) := by
  have hmeas : Measurable (fun x : ι → ℝ => fun k => ∑ i, M k i * x i) := by fun_prop
  unfold whiteNoise
  rw [← charFun_eq_pi_iff]
  intro t
  set u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ∑ k, t k * M k i) with hu
  have hstep : charFun (((Measure.pi fun _ : ι => gaussianReal 0 v).map
      (fun x k => ∑ i, M k i * x i)).map (WithLp.toLp 2)) t =
      charFun ((Measure.pi fun _ : ι => gaussianReal 0 v).map (WithLp.toLp 2)) u := by
    rw [← MeasurableEquiv.coe_toLp, ← MeasurableEquiv.coe_toLp, charFun_apply, charFun_apply,
      integral_map_equiv, integral_map_equiv, integral_map hmeas.aemeasurable]
    · congr 1
      funext x
      congr 3
      simp only [MeasurableEquiv.coe_toLp, PiLp.inner_apply, hu]
      simp only [RCLike.inner_apply, conj_trivial]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    · exact (Measurable.aestronglyMeasurable (by fun_prop))
  rw [hstep, charFun_pi]
  simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  have h := hM (fun k => t k)
  have h' : (v : ℝ) * ∑ i, (∑ k, t k * M k i) ^ 2 = ((m * v : ℝ≥0) : ℝ) * ∑ k, t k ^ 2 := by
    rw [h]; push_cast; ring
  simp only [hu]
  exact_mod_cast h'

/-- Independent copies of an image of white noise are an image of one larger white noise. -/
theorem pi_map_whiteNoise {ι κ Y : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace Y]
    (v : ℝ≥0) (f : (κ → ℝ) → Y) (hf : Measurable f) :
    Measure.pi (fun _ : ι => (whiteNoise κ v).map f) =
      (whiteNoise (ι × κ) v).map (fun r i => f (fun c => r (i, c))) := by
  have h1 : Measure.pi (fun _ : ι => whiteNoise κ v) =
      (whiteNoise (ι × κ) v).map (MeasurableEquiv.curry ι κ ℝ) := by
    have := Measure.infinitePi_map_curry (fun (_ : ι) (_ : κ) => gaussianReal (0 : ℝ) v)
    simp only [Measure.infinitePi_eq_pi] at this
    unfold whiteNoise
    exact this.symm
  rw [← Measure.pi_map_pi (fun _ => hf.aemeasurable), h1,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  rfl

/-- The complex matrix `x + i y` assembled from real coordinates `(x, y)`. -/
def ginibreAssemble {ι κ : Type*} (r : ι × κ × Fin 2 → ℝ) : Matrix ι κ ℂ :=
  Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I

/-- `ginibreAssemble` is measurable. -/
@[fun_prop]
theorem measurable_ginibreAssemble {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Measurable (ginibreAssemble (ι := ι) (κ := κ)) := by
  unfold ginibreAssemble
  fun_prop

/-- `ginibreMeasure` is the image of `whiteNoise _ (t/2)` (definitional). -/
theorem ginibreMeasure_eq_map {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    ginibreMeasure ι κ t = (whiteNoise (ι × κ × Fin 2) (t / 2)).map ginibreAssemble := rfl

/-- `ginibreMeasure` is a probability measure. -/
instance isProbabilityMeasure_ginibreMeasure (ι κ : Type*) [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    IsProbabilityMeasure (ginibreMeasure ι κ t) := by
  rw [ginibreMeasure_eq_map]; infer_instance

/-- The bond factor of `layerLaw`: `k × p` independent `Gin_W(t)` blocks (`t = b/W` in a
layer, so `E|B_ij|² = b/W`). -/
def bondLaw (k p W : ℕ) (t : ℝ≥0) : Measure (Fin k → Fin p → Matrix (Fin W) (Fin W) ℂ) :=
  Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin p => ginibreMeasure (Fin W) (Fin W) t

/-- Assembly of all bond blocks from one family of real coordinates. -/
def bondAssemble {k p W : ℕ} (r : Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ) :
    Fin k → Fin p → Matrix (Fin W) (Fin W) ℂ :=
  fun a j => ginibreAssemble fun c => r (a, j, c)

/-- `bondAssemble` is measurable. -/
theorem measurable_bondAssemble {k p W : ℕ} : Measurable (bondAssemble (k := k) (p := p) (W := W)) := by
  unfold bondAssemble
  fun_prop

/-- The bond law is the image of one white noise of variance `t/2` under `bondAssemble`. -/
theorem bondLaw_eq_map (k p W : ℕ) (t : ℝ≥0) :
    bondLaw k p W t = (whiteNoise (Fin k × (Fin p × (Fin W × Fin W × Fin 2))) (t / 2)).map
      bondAssemble := by
  unfold bondLaw
  simp only [ginibreMeasure_eq_map]
  rw [pi_map_whiteNoise _ _ measurable_ginibreAssemble, pi_map_whiteNoise]
  · rfl
  · fun_prop

/-- Mass `m_j = Σ_{a ~ j} ‖v_a‖²` of `v` on the blocks incident to port `j`. -/
def portMass {k p W : ℕ} (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ) (j : Fin p) : ℝ :=
  ∑ x : Fin k × Fin W, if inc x.1 j then ‖v x‖ ^ 2 else 0

/-- Port-`j` component `(B* v)_{(j,·)} = Σ_{a ~ j} B_{aj}* v_a`. -/
def portVec {k p W : ℕ} (inc : Fin k → Fin p → Bool) (B : Fin k → Fin p → Matrix (Fin W) (Fin W) ℂ)
    (v : Fin k × Fin W → ℂ) (j : Fin p) : Fin W → ℂ :=
  fun β => ∑ x : Fin k × Fin W, star (if inc x.1 j then B x.1 j x.2 β else 0) * v x

/-- Real coefficients of `(Re, Im)(conj(x + i y) z)` in `(x, y)`. -/
def portCoef (c' c : Fin 2) (z : ℂ) : ℝ :=
  if c' = 0 then (if c = 0 then z.re else z.im) else (if c = 0 then z.im else -z.re)

/-- Real matrix of `r ↦ (Re, Im)` of the port-`j` component of `B* v`, `B = bondAssemble r`. -/
def portMatrix {k p W : ℕ} (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ) (j : Fin p) :
    Fin W × Fin 2 → Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ :=
  fun q i => if i.2.1 = j then (if i.2.2.2.1 = q.1 then
    (if inc i.1 j then portCoef q.2 i.2.2.2.2 (v (i.1, i.2.2.1)) else 0) else 0) else 0

/-- Explicit form of `portMatrix` applied to a coordinate vector. -/
theorem portMatrix_mulVec {k p W : ℕ} (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ)
    (j : Fin p) (r : Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ) (β : Fin W) (c' : Fin 2) :
    ∑ i, portMatrix inc v j (β, c') i * r i =
      ∑ x : Fin k × Fin W, if inc x.1 j then
        portCoef c' 0 (v x) * r (x.1, j, x.2, β, 0) + portCoef c' 1 (v x) * r (x.1, j, x.2, β, 1)
        else 0 := by
  simp only [portMatrix, Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.sum_univ_two]

/-- The real part of the port component is linear in the real coordinates. -/
theorem portVec_re {k p W : ℕ} (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ)
    (j : Fin p) (r : Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ) (β : Fin W) :
    (portVec inc (bondAssemble r) v j β).re = ∑ i, portMatrix inc v j (β, 0) i * r i := by
  rw [portMatrix_mulVec]
  simp only [portVec, bondAssemble, ginibreAssemble, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp [portCoef]
  ring

/-- The imaginary part of the port component is linear in the real coordinates. -/
theorem portVec_im {k p W : ℕ} (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ)
    (j : Fin p) (r : Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ) (β : Fin W) :
    (portVec inc (bondAssemble r) v j β).im = ∑ i, portMatrix inc v j (β, 1) i * r i := by
  rw [portMatrix_mulVec]
  simp only [portVec, bondAssemble, ginibreAssemble, Complex.im_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp [portCoef]
  ring

/-- `portMatrix · portMatrixᵀ = m_j I`: the real form of the covariance identity
`E (B* v)_j (B* v)_j* = t m_j I`. -/
theorem portMatrix_isometry {k p W : ℕ} (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ)
    (j : Fin p) (t : Fin W × Fin 2 → ℝ) :
    ∑ i, (∑ q, t q * portMatrix inc v j q i) ^ 2 = portMass inc v j * ∑ q, t q ^ 2 := by
  simp only [portMatrix, Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fin.sum_univ_two]
  have key : ∀ (a : Fin k) (j' : Fin p) (α β : Fin W),
      ((if j' = j then
          if inc a j = true then t (β, 0) * portCoef 0 0 (v (a, α)) + t (β, 1) * portCoef 1 0 (v (a, α))
          else 0
        else 0) ^ 2 +
      (if j' = j then
          if inc a j = true then t (β, 0) * portCoef 0 1 (v (a, α)) + t (β, 1) * portCoef 1 1 (v (a, α))
          else 0
        else 0) ^ 2) =
      if j' = j then (if inc a j = true then
        (‖v (a, α)‖ ^ 2) * (t (β, 0) ^ 2 + t (β, 1) ^ 2) else 0) else 0 := by
    intro a j' α β
    split_ifs
    · simp only [portCoef, Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    all_goals simp
  simp_rw [key]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, portMass, Fintype.sum_prod_type, Finset.sum_mul, ite_mul, zero_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · exact Finset.sum_comm
  · simp

/-- Measurability of the port component. -/
theorem measurable_portVec {k p W : ℕ} (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ)
    (j : Fin p) (β : Fin W) : Measurable fun B : Fin k → Fin p → Matrix (Fin W) (Fin W) ℂ =>
      portVec inc B v j β := by
  unfold portVec
  fun_prop

/-- **Port small ball.** Under `bondLaw k p W t` (`t > 0`), if `m_j > 0` and `s > 0`,
`P(Σ_β |(B* v)_{(j,β)}|² < s) ≤ (e s/(W m_j t))^W`. -/
theorem bondLaw_portVec_lt {k p W : ℕ} {t : ℝ≥0} (ht : t ≠ 0)
    (inc : Fin k → Fin p → Bool) (v : Fin k × Fin W → ℂ) (j : Fin p)
    (hm : 0 < portMass inc v j) {s : ℝ} (hs : 0 < s) :
    bondLaw k p W t {B | ∑ β, ‖portVec inc B v j β‖ ^ 2 < s} ≤
      ENNReal.ofReal ((Real.exp 1 * s / (W * portMass inc v j * t)) ^ W) := by
  set m : ℝ≥0 := Real.toNNReal (portMass inc v j) with hmdef
  have hmc : (m : ℝ) = portMass inc v j := Real.coe_toNNReal _ hm.le
  have hM : ∀ u : Fin W × Fin 2 → ℝ,
      ∑ i, (∑ q, u q * portMatrix inc v j q i) ^ 2 = m * ∑ q, u q ^ 2 :=
    by rw [hmc]; exact portMatrix_isometry inc v j
  have hL : Measurable (fun x : Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ =>
      fun q => ∑ i, portMatrix inc v j q i * x i) := by fun_prop
  have hset : MeasurableSet {B : Fin k → Fin p → Matrix (Fin W) (Fin W) ℂ |
      ∑ β, ‖portVec inc B v j β‖ ^ 2 < s} :=
    measurableSet_lt (Finset.measurable_sum _ fun β _ =>
      ((measurable_portVec inc v j β).norm).pow_const 2) measurable_const
  rw [bondLaw_eq_map, Measure.map_apply measurable_bondAssemble hset]
  have hpre : bondAssemble ⁻¹' {B : Fin k → Fin p → Matrix (Fin W) (Fin W) ℂ |
      ∑ β, ‖portVec inc B v j β‖ ^ 2 < s} =
      (fun x q => ∑ i, portMatrix inc v j q i * x i) ⁻¹' {y | ∑ q, y q ^ 2 < s} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, ← portVec_re, ← portVec_im]
    simp_rw [Complex.sq_norm, Complex.normSq_apply, sq]
  rw [hpre, ← Measure.map_apply hL (measurableSet_lt (by fun_prop) measurable_const),
    whiteNoise_map_linear (t / 2) m _ hM]
  have hv : m * (t / 2) ≠ 0 := by
    have : (m : ℝ) ≠ 0 := by rw [hmc]; exact hm.ne'
    have : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    intro h
    have h' : ((m * (t / 2) : ℝ≥0) : ℝ) = 0 := by rw [h]; rfl
    push_cast at h'
    simp_all
  refine (whiteNoise_sum_sq_lt hv (m := W) (by simp [mul_comm]) hs).trans (le_of_eq ?_)
  congr 2
  push_cast
  rw [hmc]
  ring

/-- The port components of `(bondMatrix σ B)ᴴ v`. -/
theorem bondMatrix_mulVec_apply {W : ℕ} (σ : LayerShape)
    (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) (v : PhysSite W σ → ℂ)
    (j : Fin σ.ports) (β : Fin W) :
    ((bondMatrix σ B)ᴴ *ᵥ v) (j, β) = portVec σ.incident B v j β := by
  simp only [Matrix.mulVec, dotProduct, conjTranspose_apply, bondMatrix, portVec]

/-- For a unit vector, some port carries incident mass at least `1/2` (all four shapes;
the mass is `1` except in the separate-port case). -/
theorem exists_port_mass_ge {W : ℕ} (σ : LayerShape) (v : PhysSite W σ → ℂ)
    (hv : ∑ x, ‖v x‖ ^ 2 = 1) : ∃ j, 1 / 2 ≤ portMass σ.incident v j := by
  cases σ with
  | separate =>
    have hsum : portMass LayerShape.separate.incident v 0 +
        portMass LayerShape.separate.incident v 1 = 1 := by
      rw [← hv]
      simp only [portMass, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases x with ⟨a, α⟩
      fin_cases a <;> simp [LayerShape.incident]
    by_contra h
    push Not at h
    linarith [h 0, h 1]
  | common => exact ⟨0, by simp [portMass, LayerShape.incident, hv]; norm_num⟩
  | oneBlockOnePort => exact ⟨0, by simp [portMass, LayerShape.incident, hv]; norm_num⟩
  | oneBlockTwoPorts => exact ⟨0, by simp [portMass, LayerShape.incident, hv]; norm_num⟩

/-- **Fixed-vector small ball for the bonds** (the Gaussian absorption lemma):
for each shape, `W ≥ 1`, `b > 0`, `Σ_x |v_x|² = 1`, `τ > 0`,
`P(‖(bondMatrix σ B)ᴴ v‖² < τ²) ≤ ((2e/b) τ²)^W` under the bond law `Gin(b/W)`. -/
theorem bondLaw_smallBall (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    (v : PhysSite W σ → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) {τ : ℝ} (hτ : 0 < τ) :
    bondLaw σ.blocks σ.ports W (Real.toNNReal (b / W))
        {B | ∑ y, ‖((bondMatrix σ B)ᴴ *ᵥ v) y‖ ^ 2 < τ ^ 2} ≤
      ENNReal.ofReal ((2 * Real.exp 1 / b * τ ^ 2) ^ W) := by
  obtain ⟨j, hj⟩ := exists_port_mass_ge σ v hv
  have hm : 0 < portMass σ.incident v j := lt_of_lt_of_le (by norm_num) hj
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : Real.toNNReal (b / W) ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hsub : {B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ |
      ∑ y, ‖((bondMatrix σ B)ᴴ *ᵥ v) y‖ ^ 2 < τ ^ 2} ⊆
      {B | ∑ β, ‖portVec σ.incident B v j β‖ ^ 2 < τ ^ 2} := by
    intro B hB
    simp only [Set.mem_ofPred_eq] at hB ⊢
    refine lt_of_le_of_lt ?_ hB
    rw [Fintype.sum_prod_type]
    simp_rw [bondMatrix_mulVec_apply]
    exact Finset.single_le_sum (f := fun j' => ∑ β, ‖portVec σ.incident B v j' β‖ ^ 2)
      (fun j' _ => Finset.sum_nonneg fun β _ => by positivity) (Finset.mem_univ j)
  refine (measure_mono hsub).trans ((bondLaw_portVec_lt ht σ.incident v j hm (by positivity)).trans
    (ENNReal.ofReal_le_ofReal ?_))
  rw [Real.coe_toNNReal _ (by positivity)]
  apply pow_le_pow_left₀ (by positivity)
  have e1 : Real.exp 1 * τ ^ 2 / (W * portMass σ.incident v j * (b / W)) =
      Real.exp 1 * τ ^ 2 / b * (portMass σ.incident v j)⁻¹ := by
    field_simp
  rw [e1]
  have e2 : 2 * Real.exp 1 / b * τ ^ 2 = Real.exp 1 * τ ^ 2 / b * 2 := by ring
  rw [e2]
  have h2 : (portMass σ.incident v j)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hm (by norm_num)]; linarith
  have : 0 ≤ Real.exp 1 * τ ^ 2 / b := by positivity
  exact mul_le_mul_of_nonneg_left h2 this

/-- **Clause 1 for circular Gaussians.** Under `ginibreMeasure ι κ t`, `t > 0`, `s > 0`, with
`n = |ι| |κ|` complex entries: `P(Σ_{x,y} |B_xy|² ≤ s) ≤ (e s/(n t))^n`. For `κ = Fin 1` this is
the small ball of a circular Gaussian vector of covariance `t I`. -/
theorem ginibreMeasure_frobenius_le {ι κ : Type*} [Fintype ι] [Fintype κ] {t : ℝ≥0}
    (ht : t ≠ 0) {s : ℝ} (hs : 0 < s) :
    ginibreMeasure ι κ t {B | ∑ x, ∑ y, ‖B x y‖ ^ 2 ≤ s} ≤
      ENNReal.ofReal ((Real.exp 1 * s / (Fintype.card ι * Fintype.card κ * t)) ^
        (Fintype.card ι * Fintype.card κ)) := by
  have hset : MeasurableSet {B : Matrix ι κ ℂ | ∑ x, ∑ y, ‖B x y‖ ^ 2 ≤ s} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [ginibreMeasure_eq_map, Measure.map_apply measurable_ginibreAssemble hset]
  have hpre : ginibreAssemble ⁻¹' {B : Matrix ι κ ℂ | ∑ x, ∑ y, ‖B x y‖ ^ 2 ≤ s} =
      {r | ∑ q, r q ^ 2 ≤ s} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ginibreAssemble, Matrix.of_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp_rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  rw [hpre]
  have hv : t / 2 ≠ 0 := by simpa using ht
  refine (whiteNoise_sum_sq_le hv (m := Fintype.card ι * Fintype.card κ)
    (by simp [Fintype.card_prod]; ring) hs).trans (le_of_eq ?_)
  congr 2
  push_cast
  ring

/-- `GUE_W(t)` is a probability measure. -/
theorem isProbabilityMeasure_gueMeasure (W : ℕ) (t : ℝ≥0) :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t) := by
  unfold BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
    BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

/-- Events of the bonds have the same probability under `layerLaw` and `bondLaw`. -/
theorem layerLaw_bond_event (W : ℕ) (b : ℝ) (σ : LayerShape)
    (S : Set (Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ)) :
    layerLaw W b σ {ω | ω.2 ∈ S} = bondLaw σ.blocks σ.ports W (Real.toNNReal (b / W)) S := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have hset : {ω : LayerSample W σ | ω.2 ∈ S} = Set.univ ×ˢ S := by ext ω; simp
  rw [hset, layerLaw, Measure.prod_prod, measure_univ, one_mul]
  rfl

/-- **Clause 2 under `layerLaw`** (the Gaussian absorption lemma), sums of
squares: `P(Σ_y |((bondMatrix σ B)ᴴ v)_y|² < τ²) ≤ ((2e/b) τ²)^W` for every shape, `W ≥ 1`,
`b > 0`, `Σ_x |v_x|² = 1`, `τ > 0`. -/
theorem layerLaw_bond_smallBall (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    (v : PhysSite W σ → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) {τ : ℝ} (hτ : 0 < τ) :
    layerLaw W b σ {ω | ∑ y, ‖((bondMatrix σ ω.2)ᴴ *ᵥ v) y‖ ^ 2 < τ ^ 2} ≤
      ENNReal.ofReal ((2 * Real.exp 1 / b * τ ^ 2) ^ W) := by
  exact (le_of_eq (layerLaw_bond_event W b σ
    {B | ∑ y, ‖((bondMatrix σ B)ᴴ *ᵥ v) y‖ ^ 2 < τ ^ 2})).trans (bondLaw_smallBall σ hW hb v hv hτ)

/-- **Clause 2, Euclidean norms** (the Gaussian absorption lemma):
`P(‖(bondMatrix σ B)ᴴ v‖ < τ) ≤ (C_b τ²)^W` with `C_b = 2e/b`, for every shape, `W ≥ 1`,
`b > 0`, every deterministic `‖v‖ = 1` and `τ > 0`, under `layerLaw W b σ`. -/
theorem layerLaw_bond_smallBall_norm (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ}
    (hb : 0 < b) (v : PhysSite W σ → ℂ)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PhysSite W σ))‖ = 1) {τ : ℝ} (hτ : 0 < τ) :
    layerLaw W b σ {ω | ‖(WithLp.toLp 2 ((bondMatrix σ ω.2)ᴴ *ᵥ v) :
        EuclideanSpace ℂ (PortSite W σ))‖ < τ} ≤
      ENNReal.ofReal ((2 * Real.exp 1 / b * τ ^ 2) ^ W) := by
  have hv' : ∑ x, ‖v x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
    simpa using hv
  have hset : {ω : LayerSample W σ | ‖(WithLp.toLp 2 ((bondMatrix σ ω.2)ᴴ *ᵥ v) :
        EuclideanSpace ℂ (PortSite W σ))‖ < τ} =
      {ω | ∑ y, ‖((bondMatrix σ ω.2)ᴴ *ᵥ v) y‖ ^ 2 < τ ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, EuclideanSpace.norm_eq]
    exact Real.sqrt_lt' hτ
  rw [hset]
  exact layerLaw_bond_smallBall σ hW hb v hv' hτ

/-!
## Clause 3: operator-norm tail of a Ginibre block via nets

In the Gaussian absorption lemma, "Gaussian norm tails give `‖K‖_{L^q} ≤ C_b(1 + √(q/W))`". The
`ε`-nets (`ε = 1/4`) are explicit hypotheses here; their existence with cardinality
`≤ (3/ε)^{2W}` is proved in the separate module `Nets` (not imported).
-/

open scoped Matrix.Norms.L2Operator

/-- Gaussian tail: `P(X ≥ a) ≤ exp(-a²/(2v))` for `X ~ N(0, v)`, `v > 0`, `a ≥ 0`
(Chernoff with the Gaussian moment generating function). -/
theorem gaussianReal_Ici_le {v : ℝ≥0} (hv : v ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    gaussianReal 0 v (Set.Ici a) ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * v))) := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  have h := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 v) a
    (t := a / v) (by positivity) (integrable_exp_mul_gaussianReal _)
  rw [mgf_id_gaussianReal] at h
  have he : Real.exp (-(a / v) * a) * Real.exp (0 * (a / v) + v * (a / v) ^ 2 / 2) =
      Real.exp (-a ^ 2 / (2 * v)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [he] at h
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) h)
  rfl

/-- Real coefficients of `r ↦ Re Σ_{x,y} conj(u_x) (r_{xy0} + i r_{xy1}) w_y`. -/
def pairCoef {ι κ : Type*} (u : ι → ℂ) (w : κ → ℂ) : Unit → ι × κ × Fin 2 → ℝ :=
  fun _ q => if q.2.2 = 0 then (star (u q.1) * w q.2.1).re else -(star (u q.1) * w q.2.1).im

/-- `Σ_q pairCoef² = ‖u‖² ‖w‖²`. -/
theorem pairCoef_sum_sq {ι κ : Type*} [Fintype ι] [Fintype κ] (u : ι → ℂ) (w : κ → ℂ) :
    ∑ q, pairCoef u w () q ^ 2 = (∑ x, ‖u x‖ ^ 2) * ∑ y, ‖w y‖ ^ 2 := by
  simp only [pairCoef, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [neg_sq, ← norm_star (u x), ← mul_pow, ← norm_mul, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- `Re⟨u, B w⟩` is linear in the real coordinates of `B = ginibreAssemble r`. -/
theorem pairCoef_re {ι κ : Type*} [Fintype ι] [Fintype κ] (u : ι → ℂ) (w : κ → ℂ)
    (r : ι × κ × Fin 2 → ℝ) :
    (∑ x, ∑ y, star (u x) * (ginibreAssemble r x y * w y)).re =
      ∑ q, pairCoef u w () q * r q := by
  simp only [pairCoef, ginibreAssemble, Matrix.of_apply, Complex.re_sum, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp
  ring

/-- **Fixed-pair Gaussian tail.** Under `ginibreMeasure ι κ t` (`t > 0`), for unit `u, w`,
`Re⟨u, B w⟩ ~ N(0, t/2)` (by `whiteNoise_map_linear`), hence
`P(Re⟨u, B w⟩ ≥ a) ≤ exp(-a²/t)` for `a ≥ 0`. -/
theorem ginibre_pair_tail {ι κ : Type*} [Fintype ι] [Fintype κ] {t : ℝ≥0} (ht : t ≠ 0)
    (u : ι → ℂ) (w : κ → ℂ) (hu : ∑ x, ‖u x‖ ^ 2 = 1) (hw : ∑ y, ‖w y‖ ^ 2 = 1) {a : ℝ}
    (ha : 0 ≤ a) :
    ginibreMeasure ι κ t {B | a ≤ (∑ x, ∑ y, star (u x) * (B x y * w y)).re} ≤
      ENNReal.ofReal (Real.exp (-a ^ 2 / t)) := by
  have hset : MeasurableSet {B : Matrix ι κ ℂ | a ≤ (∑ x, ∑ y, star (u x) * (B x y * w y)).re} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [ginibreMeasure_eq_map, Measure.map_apply measurable_ginibreAssemble hset]
  have hL : Measurable (fun r : ι × κ × Fin 2 → ℝ => fun k : Unit =>
      ∑ q, pairCoef u w k q * r q) := by fun_prop
  have hpre : ginibreAssemble ⁻¹'
      {B : Matrix ι κ ℂ | a ≤ (∑ x, ∑ y, star (u x) * (B x y * w y)).re} =
      (fun r : ι × κ × Fin 2 → ℝ => fun k : Unit => ∑ q, pairCoef u w k q * r q) ⁻¹'
        {y | a ≤ y ()} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, pairCoef_re]
  have hM : ∀ s : Unit → ℝ, ∑ q, (∑ k, s k * pairCoef u w k q) ^ 2 = (1 : ℝ≥0) * ∑ k, s k ^ 2 := by
    intro s
    simp only [Finset.univ_unique, Finset.sum_singleton, mul_pow, ← Finset.mul_sum]
    rw [pairCoef_sum_sq, hu, hw]
    simp
  rw [hpre, ← Measure.map_apply hL (measurableSet_le measurable_const (measurable_pi_apply ())),
    whiteNoise_map_linear (t / 2) 1 (pairCoef u w) hM]
  have hbox : {y : Unit → ℝ | a ≤ y ()} = Set.univ.pi (fun _ => Set.Ici a) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ici]
    exact ⟨fun h _ => h, fun h => h ()⟩
  rw [hbox, whiteNoise, Measure.pi_pi, Finset.univ_unique, Finset.prod_singleton]
  have hv : (1 : ℝ≥0) * (t / 2) ≠ 0 := by simpa using ht
  refine (gaussianReal_Ici_le hv ha).trans (le_of_eq ?_)
  congr 2
  push_cast
  ring

/-- **Deterministic net bound.** If `Nu`, `Nw` are `1/4`-nets of the unit spheres (no
requirement `Nu ⊆ S`), `c > 0` and `Re⟨n, A n'⟩ < c` for all net pairs, then `‖A‖ < 2c`
(`L²` operator norm). -/
theorem opNorm_lt_of_net {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ)
    (Nu : Finset (EuclideanSpace ℂ ι)) (Nw : Finset (EuclideanSpace ℂ κ))
    (hNu : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 → ∃ n ∈ Nu, ‖x - n‖ ≤ 1 / 4)
    (hNw : ∀ x : EuclideanSpace ℂ κ, ‖x‖ = 1 → ∃ n ∈ Nw, ‖x - n‖ ≤ 1 / 4)
    {c : ℝ} (hc : 0 < c)
    (h : ∀ n ∈ Nu, ∀ n' ∈ Nw, (inner ℂ n (WithLp.toLp 2 (A *ᵥ WithLp.ofLp n'))).re < c) :
    ‖A‖ < 2 * c := by
  by_contra hcon
  push Not at hcon
  set F : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) with hF
  have hAF : ‖A‖ = ‖F‖ := Matrix.l2_opNorm_def A
  have hFapp : ∀ y, F y = WithLp.toLp 2 (A *ᵥ WithLp.ofLp y) := by
    intro y
    rw [hF, LinearMap.coe_toContinuousLinearMap']
    rfl
  have hA0 : 0 < ‖A‖ := by linarith
  have hr : (23 / 24) * ‖A‖ < ‖F‖ := by rw [← hAF]; linarith
  obtain ⟨x, hx1, hx⟩ := F.exists_lt_apply_of_lt_opNorm hr
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [map_zero, norm_zero] at hx
    linarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set xh : EuclideanSpace ℂ κ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hxh
  have hcx : ‖((‖x‖⁻¹ : ℝ) : ℂ)‖ = ‖x‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxn)]
  have hxh1 : ‖xh‖ = 1 := by
    rw [hxh, norm_smul, hcx, inv_mul_cancel₀ hxn.ne']
  have hFxh : ‖F x‖ ≤ ‖F xh‖ := by
    rw [hxh, map_smul, norm_smul, hcx]
    have : 1 ≤ ‖x‖⁻¹ := one_le_inv₀ hxn |>.mpr hx1.le
    nlinarith [norm_nonneg (F x)]
  obtain ⟨n', hn'N, hn'⟩ := hNw xh hxh1
  have hFn' : (23 / 24) * ‖A‖ - ‖A‖ / 4 < ‖F n'‖ := by
    have h1 : ‖F (xh - n')‖ ≤ ‖F‖ * ‖xh - n'‖ := F.le_opNorm _
    have h2 : ‖F xh‖ - ‖F n'‖ ≤ ‖F (xh - n')‖ := by
      rw [map_sub]; exact norm_sub_norm_le _ _
    have h3 : ‖F‖ * ‖xh - n'‖ ≤ ‖F‖ * (1 / 4) :=
      mul_le_mul_of_nonneg_left hn' (norm_nonneg _)
    rw [← hAF] at h1 h3
    linarith
  set z := F n' with hz
  have hzpos : 0 < ‖z‖ := by linarith
  set yh : EuclideanSpace ℂ ι := ((‖z‖⁻¹ : ℝ) : ℂ) • z with hyh
  have hcz : ‖((‖z‖⁻¹ : ℝ) : ℂ)‖ = ‖z‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzpos)]
  have hyh1 : ‖yh‖ = 1 := by
    rw [hyh, norm_smul, hcz, inv_mul_cancel₀ hzpos.ne']
  obtain ⟨n, hnN, hn⟩ := hNu yh hyh1
  have hre1 : (inner ℂ yh z).re = ‖z‖ := by
    rw [hyh, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp only [Complex.conj_ofReal]
    have e : ((‖z‖⁻¹ : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2 = ((‖z‖ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
      congr 1
      field_simp
    exact (congrArg Complex.re e).trans (Complex.ofReal_re _)
  have hre2 : (inner ℂ (yh - n) z).re ≤ ‖yh - n‖ * ‖z‖ := by
    have := re_inner_le_norm (𝕜 := ℂ) (yh - n) z
    exact this
  have hre : (inner ℂ n z).re = (inner ℂ yh z).re - (inner ℂ (yh - n) z).re := by
    rw [inner_sub_left, Complex.sub_re]; ring
  have hlt := h n hnN n' hn'N
  rw [← hFapp] at hlt
  have h4 : ‖yh - n‖ * ‖z‖ ≤ (1 / 4) * ‖z‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  have hz' : (inner ℂ n z).re = (inner ℂ n (F n')).re := rfl
  nlinarith

/-- A unit vector of `EuclideanSpace ℂ ι` has `Σ |n_x|² = 1`. -/
theorem sum_sq_eq_one_of_norm {ι : Type*} [Fintype ι] {n : EuclideanSpace ℂ ι} (hn : ‖n‖ = 1) :
    ∑ x, ‖(WithLp.ofLp n) x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hn
  exact hn

/-- `⟨n, B n'⟩` in coordinates. -/
theorem inner_toLp_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Matrix ι κ ℂ)
    (n : EuclideanSpace ℂ ι) (n' : EuclideanSpace ℂ κ) :
    inner ℂ n (WithLp.toLp 2 (B *ᵥ WithLp.ofLp n')) =
      ∑ x, ∑ y, star ((WithLp.ofLp n) x) * (B x y * (WithLp.ofLp n') y) := by
  simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm]

/-- **Net union bound for the operator norm** (generic law). Let `Nu`, `Nw` be finite
`1/4`-nets of the unit spheres of `ℂ^ι`, `ℂ^κ`. If for every pair of net points the event
`Re⟨n, B n'⟩ ≥ a/2` has `μ`-probability at most `p`, then `μ(‖B‖ ≥ a) ≤ |Nu| |Nw| p`
(`L²` operator norm). Deterministic input: `opNorm_lt_of_net`. -/
theorem measure_opNorm_ge_of_net {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (μ : Measure Ω) (f : Ω → Matrix ι κ ℂ)
    (Nu : Finset (EuclideanSpace ℂ ι)) (Nw : Finset (EuclideanSpace ℂ κ))
    (hNu : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 → ∃ n ∈ Nu, ‖x - n‖ ≤ 1 / 4)
    (hNw : ∀ x : EuclideanSpace ℂ κ, ‖x‖ = 1 → ∃ n ∈ Nw, ‖x - n‖ ≤ 1 / 4)
    {a : ℝ} (ha : 0 < a) {p : ℝ}
    (htail : ∀ n ∈ Nu, ∀ n' ∈ Nw,
      μ {ω | a / 2 ≤
        (∑ x, ∑ y, star ((WithLp.ofLp n) x) * (f ω x y * (WithLp.ofLp n') y)).re} ≤
        ENNReal.ofReal p) :
    μ {ω | a ≤ ‖f ω‖} ≤ ENNReal.ofReal (Nu.card * Nw.card * p) := by
  set S : EuclideanSpace ℂ ι → EuclideanSpace ℂ κ → Set Ω := fun n n' =>
    {ω | a / 2 ≤ (∑ x, ∑ y, star ((WithLp.ofLp n) x) * (f ω x y * (WithLp.ofLp n') y)).re}
    with hS
  have hsub : {ω | a ≤ ‖f ω‖} ⊆ ⋃ n ∈ Nu, ⋃ n' ∈ Nw, S n n' := by
    intro ω hω
    by_contra hnot
    simp only [hS, Set.mem_iUnion, not_exists, Set.mem_ofPred_eq, not_le] at hnot
    have hlt := opNorm_lt_of_net (f ω) Nu Nw hNu hNw (c := a / 2) (by positivity)
      (fun n hn n' hn' => by rw [inner_toLp_mulVec]; exact hnot n hn n' hn')
    simp only [Set.mem_ofPred_eq] at hω
    linarith
  calc μ {ω | a ≤ ‖f ω‖}
      ≤ μ (⋃ n ∈ Nu, ⋃ n' ∈ Nw, S n n') := measure_mono hsub
    _ ≤ ∑ n ∈ Nu, μ (⋃ n' ∈ Nw, S n n') := measure_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Nu, ∑ n' ∈ Nw, μ (S n n') :=
        Finset.sum_le_sum fun n _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Nu, ∑ n' ∈ Nw, ENNReal.ofReal p :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => htail n hn n' hn'
    _ = ENNReal.ofReal (Nu.card * Nw.card * p) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp [mul_assoc]

/-- **Operator-norm tail of one Ginibre block** (clause 3, given nets). Under
`ginibreMeasure ι κ t` (`E|B_xy|² = t > 0`), for finite `1/4`-nets `Nu ⊆ S(ℂ^ι)`,
`Nw ⊆ S(ℂ^κ)` and `a > 0`: `P(‖B‖ ≥ a) ≤ |Nu| |Nw| exp(-a²/(4t))` (`L²` operator norm). For the
layer bonds `t = b/W` this is `|Nu| |Nw| exp(-a² W/(4b))`; with nets of cardinality
`≤ 12^{2W}` it gives `P(‖B‖ ≥ 7√b) ≤ e^{-W}`. -/
theorem ginibre_opNorm_tail_of_net {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {t : ℝ≥0} (ht : t ≠ 0)
    (Nu : Finset (EuclideanSpace ℂ ι)) (Nw : Finset (EuclideanSpace ℂ κ))
    (hNu1 : ∀ n ∈ Nu, ‖n‖ = 1) (hNw1 : ∀ n ∈ Nw, ‖n‖ = 1)
    (hNu : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 → ∃ n ∈ Nu, ‖x - n‖ ≤ 1 / 4)
    (hNw : ∀ x : EuclideanSpace ℂ κ, ‖x‖ = 1 → ∃ n ∈ Nw, ‖x - n‖ ≤ 1 / 4)
    {a : ℝ} (ha : 0 < a) :
    ginibreMeasure ι κ t {B | a ≤ ‖B‖} ≤
      ENNReal.ofReal (Nu.card * Nw.card * Real.exp (-a ^ 2 / (4 * t))) := by
  refine measure_opNorm_ge_of_net _ id Nu Nw hNu hNw ha fun n hn n' hn' => ?_
  refine (ginibre_pair_tail ht _ _ (sum_sq_eq_one_of_norm (hNu1 n hn))
    (sum_sq_eq_one_of_norm (hNw1 n' hn')) (by positivity : 0 ≤ a / 2)).trans (le_of_eq ?_)
  congr 2
  ring

/-- Real coefficients of `r ↦ Re⟨u, bondMatrix σ (bondAssemble r) w⟩` (incident blocks only). -/
def bondPairCoef {k p W : ℕ} (inc : Fin k → Fin p → Bool) (u : Fin k × Fin W → ℂ)
    (w : Fin p × Fin W → ℂ) : Unit → Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ :=
  fun _ i => if inc i.1 i.2.1 then
    pairCoef (fun α => u (i.1, α)) (fun β => w (i.2.1, β)) () i.2.2 else 0

/-- `Re⟨u, bondMatrix B w⟩` is linear in the real bond coordinates. -/
theorem bondPairCoef_re {k p W : ℕ} (inc : Fin k → Fin p → Bool) (u : Fin k × Fin W → ℂ)
    (w : Fin p × Fin W → ℂ) (r : Fin k × (Fin p × (Fin W × Fin W × Fin 2)) → ℝ) :
    (∑ x : Fin k × Fin W, ∑ y : Fin p × Fin W, star (u x) *
      ((if inc x.1 y.1 then bondAssemble r x.1 y.1 x.2 y.2 else 0) * w y)).re =
      ∑ i, bondPairCoef inc u w () i * r i := by
  have h1 : ∀ (a : Fin k) (j : Fin p), ∑ q, pairCoef (fun α => u (a, α)) (fun β => w (j, β)) () q *
      r (a, j, q) = (∑ α, ∑ β, star (u (a, α)) * (bondAssemble r a j α β * w (j, β))).re :=
    fun a j => (pairCoef_re _ _ _).symm
  have hR : ∑ i, bondPairCoef inc u w () i * r i = ∑ a, ∑ j, ∑ α, ∑ β,
      (if inc a j then (star (u (a, α)) * (bondAssemble r a j α β * w (j, β))).re else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [bondPairCoef]
    split_ifs
    · rw [h1 a j, Complex.re_sum]
      simp only [Complex.re_sum]
    · simp
  have key : ∀ (a : Fin k) (α : Fin W) (j : Fin p) (β : Fin W),
      (star (u (a, α)) * ((if inc a j then bondAssemble r a j α β else 0) * w (j, β))).re =
      if inc a j then (star (u (a, α)) * (bondAssemble r a j α β * w (j, β))).re else 0 := by
    intro a α j β
    split_ifs <;> simp
  rw [hR]
  simp only [Complex.re_sum, Fintype.sum_prod_type, key]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- `Σ bondPairCoef² = Σ_{a ~ j} ‖u_a‖² ‖w_j‖² ≤ ‖u‖² ‖w‖²`. -/
theorem bondPairCoef_sum_sq_le {k p W : ℕ} (inc : Fin k → Fin p → Bool) (u : Fin k × Fin W → ℂ)
    (w : Fin p × Fin W → ℂ) :
    ∑ i, bondPairCoef inc u w () i ^ 2 ≤ (∑ x, ‖u x‖ ^ 2) * ∑ y, ‖w y‖ ^ 2 := by
  have h : ∑ i, bondPairCoef inc u w () i ^ 2 = ∑ a, ∑ j,
      (if inc a j then (∑ α, ‖u (a, α)‖ ^ 2) * ∑ β, ‖w (j, β)‖ ^ 2 else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [bondPairCoef]
    split_ifs
    · exact pairCoef_sum_sq _ _
    · simp
  rw [h, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact le_of_eq rfl
  · positivity

/-- `P(X ≥ a) ≤ exp(-a²/t)` for `X ~ N(0, v)`, `2v ≤ t`, `a > 0` (including `v = 0`). -/
theorem gaussianReal_Ici_le_of_le {v t : ℝ≥0} (hvt : 2 * v ≤ t) {a : ℝ}
    (ha : 0 < a) : gaussianReal 0 v (Set.Ici a) ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / t)) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, Measure.dirac_apply' _ measurableSet_Ici]
    simp [Set.indicator, not_le.mpr ha]
  · refine (gaussianReal_Ici_le hv ha.le).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff]
    have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast (Ne.symm hv))
    have hvt' : (2 * v : ℝ) ≤ t := by exact_mod_cast hvt
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hvt'

/-- **Fixed-pair tail for the bond matrix.** Under `bondLaw` (`Gin(t)` blocks), for unit
`u, w`, `Re⟨u, bondMatrix σ B w⟩ ~ N(0, m t/2)` with `m = Σ_{a ~ j} ‖u_a‖²‖w_j‖² ≤ 1`, hence
`P(Re⟨u, bondMatrix σ B w⟩ ≥ a) ≤ exp(-a²/t)` for `a > 0`; all four shapes. -/
theorem bondLaw_pair_tail (σ : LayerShape) {W : ℕ} {t : ℝ≥0}
    (u : PhysSite W σ → ℂ) (w : PortSite W σ → ℂ) (hu : ∑ x, ‖u x‖ ^ 2 = 1)
    (hw : ∑ y, ‖w y‖ ^ 2 = 1) {a : ℝ} (ha : 0 < a) :
    bondLaw σ.blocks σ.ports W t
        {B | a ≤ (∑ x, ∑ y, star (u x) * (bondMatrix σ B x y * w y)).re} ≤
      ENNReal.ofReal (Real.exp (-a ^ 2 / t)) := by
  have hset : MeasurableSet {B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ |
      a ≤ (∑ x, ∑ y, star (u x) * (bondMatrix σ B x y * w y)).re} :=
    measurableSet_le measurable_const (by unfold bondMatrix; fun_prop)
  rw [bondLaw_eq_map, Measure.map_apply measurable_bondAssemble hset]
  set M := bondPairCoef σ.incident u w with hMdef
  have hL : Measurable (fun r : Fin σ.blocks × (Fin σ.ports × (Fin W × Fin W × Fin 2)) → ℝ =>
      fun k : Unit => ∑ i, M k i * r i) := by fun_prop
  have hpre : bondAssemble ⁻¹' {B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ |
      a ≤ (∑ x, ∑ y, star (u x) * (bondMatrix σ B x y * w y)).re} =
      (fun r : Fin σ.blocks × (Fin σ.ports × (Fin W × Fin W × Fin 2)) → ℝ =>
        fun k : Unit => ∑ i, M k i * r i) ⁻¹' {y | a ≤ y ()} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, bondMatrix]
    rw [bondPairCoef_re]
  set m : ℝ≥0 := Real.toNNReal (∑ i, M () i ^ 2) with hmdef
  have hmc : (m : ℝ) = ∑ i, M () i ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hm1 : m ≤ 1 := by
    have := bondPairCoef_sum_sq_le σ.incident u w
    rw [hu, hw, mul_one] at this
    rw [← NNReal.coe_le_coe, hmc]
    simpa [hMdef] using this
  have hM : ∀ s : Unit → ℝ, ∑ i, (∑ k, s k * M k i) ^ 2 = m * ∑ k, s k ^ 2 := by
    intro s
    simp only [Finset.univ_unique, Finset.sum_singleton, mul_pow, ← Finset.mul_sum]
    rw [hmc]
    simp only [PUnit.default_eq_unit]
    ring
  rw [hpre, ← Measure.map_apply hL (measurableSet_le measurable_const (measurable_pi_apply ())),
    whiteNoise_map_linear (t / 2) m M hM]
  have hbox : {y : Unit → ℝ | a ≤ y ()} = Set.univ.pi (fun _ => Set.Ici a) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ici]
    exact ⟨fun h _ => h, fun h => h ()⟩
  rw [hbox, whiteNoise, Measure.pi_pi, Finset.univ_unique, Finset.prod_singleton]
  refine gaussianReal_Ici_le_of_le ?_ ha
  calc 2 * (m * (t / 2)) = m * t := by ring
    _ ≤ 1 * t := by gcongr
    _ = t := one_mul t

/-- **Operator-norm tail of the bond matrix** (clause 3, given nets): for finite `1/4`-nets
of the unit spheres of the physical and port spaces and `a > 0`,
`P(‖bondMatrix σ B‖ ≥ a) ≤ |Nu| |Nw| exp(-a²/(4t))` under `bondLaw` (`Gin(t)` blocks). -/
theorem bondMatrix_opNorm_tail_of_net (σ : LayerShape) {W : ℕ} {t : ℝ≥0}
    (Nu : Finset (EuclideanSpace ℂ (PhysSite W σ))) (Nw : Finset (EuclideanSpace ℂ (PortSite W σ)))
    (hNu1 : ∀ n ∈ Nu, ‖n‖ = 1) (hNw1 : ∀ n ∈ Nw, ‖n‖ = 1)
    (hNu : ∀ x : EuclideanSpace ℂ (PhysSite W σ), ‖x‖ = 1 → ∃ n ∈ Nu, ‖x - n‖ ≤ 1 / 4)
    (hNw : ∀ x : EuclideanSpace ℂ (PortSite W σ), ‖x‖ = 1 → ∃ n ∈ Nw, ‖x - n‖ ≤ 1 / 4)
    {a : ℝ} (ha : 0 < a) :
    bondLaw σ.blocks σ.ports W t {B | a ≤ ‖bondMatrix σ B‖} ≤
      ENNReal.ofReal (Nu.card * Nw.card * Real.exp (-a ^ 2 / (4 * t))) := by
  refine measure_opNorm_ge_of_net _ (bondMatrix σ) Nu Nw hNu hNw ha fun n hn n' hn' => ?_
  refine (bondLaw_pair_tail σ _ _ (sum_sq_eq_one_of_norm (hNu1 n hn))
    (sum_sq_eq_one_of_norm (hNw1 n' hn')) (by positivity : 0 < a / 2)).trans (le_of_eq ?_)
  congr 2
  ring

/-- **Clause 3 under `layerLaw`, given nets** (`E|B_ij|² = b/W`):
`P(‖bondMatrix σ B‖ ≥ a) ≤ |Nu| |Nw| exp(-a² W/(4b))`, every shape, `W ≥ 1`, `b > 0`, `a > 0`.
With nets of cardinality `≤ 12^{4W}` (real dimension `≤ 4W`) this is `≤ e^{-W}` once
`a² ≥ 4b(1 + 8 log 12)`, e.g. `a = 10 √b`. -/
theorem layerLaw_bondMatrix_opNorm_tail_of_net (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ}
    (hb : 0 < b)
    (Nu : Finset (EuclideanSpace ℂ (PhysSite W σ))) (Nw : Finset (EuclideanSpace ℂ (PortSite W σ)))
    (hNu1 : ∀ n ∈ Nu, ‖n‖ = 1) (hNw1 : ∀ n ∈ Nw, ‖n‖ = 1)
    (hNu : ∀ x : EuclideanSpace ℂ (PhysSite W σ), ‖x‖ = 1 → ∃ n ∈ Nu, ‖x - n‖ ≤ 1 / 4)
    (hNw : ∀ x : EuclideanSpace ℂ (PortSite W σ), ‖x‖ = 1 → ∃ n ∈ Nw, ‖x - n‖ ≤ 1 / 4)
    {a : ℝ} (ha : 0 < a) :
    layerLaw W b σ {ω | a ≤ ‖bondMatrix σ ω.2‖} ≤
      ENNReal.ofReal (Nu.card * Nw.card * Real.exp (-(a ^ 2 * W) / (4 * b))) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  refine (le_of_eq (layerLaw_bond_event W b σ {B | a ≤ ‖bondMatrix σ B‖})).trans
    ((bondMatrix_opNorm_tail_of_net σ Nu Nw hNu1 hNw1 hNu hNw ha).trans (le_of_eq ?_))
  rw [Real.coe_toNNReal _ (by positivity)]
  congr 3
  field_simp

end BlockBand.Layers
