module

public import BlockBand.DeterminantScore.Sector.LineCalculus
public import BlockBand.DeterminantScore.Sector.CoordinateFubini
public import BlockBand.Model.Construction.GaussianWeakIntegrationByParts
public import BlockBand.Window.Count.SharperFreshCount
public import BlockBand.LocalWindow.ProofCertificateTransfer

/-!
# Gaussian integration by parts for `Tr G R_η` under `GUE`

Setting: a finite index type `ι`, a deterministic Hermitian `K`, `η > 0`, `G ~ gueMeasure ι t`
(`E|G_ab|² = t`), `R(G) = (K + G - iη)⁻¹`.

* `gueLin t`: the real-linear sample map `x ↦ √(t/2)(X + X*)`, `X = (x_{·,0} + i x_{·,1})/√2`,
  from the standard real Gaussian vector on `(ι × ι) × Fin 2`; `gueMeasure_eq_map_gueLin`.
* `sum_gueDir_mul_gueDir`: the covariance `Σ_j (E_j)_{ab} (E_j)_{cd} = t δ_{ad} δ_{bc}` of the
  coordinate directions `E_j = gueLin t (e_j)`.
* `gaussian_ibp_of_line` (generic): `E[x_c f] = v_c E[g]` for a continuous `f` whose coordinate
  lines have derivative `g` everywhere (`g` continuous), under any product Gaussian, from the
  one-dimensional `gaussian_weak_integration_by_parts` and Fubini along `c`.
* **`integral_trace_mul_res`**: `E_G Tr(G R) = -t E_G (Tr R)²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedIBP

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open BlockBand.DeterminantScore.Sector
open scoped NNReal ComplexConjugate

/-!
## Gaussian integration by parts along a coordinate (generic)
-/

section Generic

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Gaussian IBP along a coordinate** (real Gaussian identity, for an
everywhere line-differentiable `f`): under `Measure.pi (gaussianReal 0 ∘ v)`,
`E[x_c f] = v_c E[g]` when `f, g` are continuous, `g(update x c s)` is the derivative of
`r ↦ f(update x c r)` at `s`, and `f`, `x_c f`, `g` are integrable. -/
theorem gaussian_ibp_of_line (v : σ → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f g : (σ → ℝ) → E) (c : σ) (hf : Continuous f)
    (hg : Continuous g)
    (hd : ∀ x s, HasDerivAt (fun r => f (Function.update x c r)) (g (Function.update x c s)) s)
    (hI0 : Integrable f (Measure.pi fun i => gaussianReal 0 (v i)))
    (hI1 : Integrable (fun x => x c • f x) (Measure.pi fun i => gaussianReal 0 (v i)))
    (hI2 : Integrable g (Measure.pi fun i => gaussianReal 0 (v i))) :
    (∫ x, x c • f x ∂Measure.pi fun i => gaussianReal 0 (v i)) =
      (v c : ℝ) • ∫ x, g x ∂Measure.pi fun i => gaussianReal 0 (v i) := by
  set ν : σ → Measure ℝ := fun i => gaussianReal 0 (v i)
  rw [integral_eq_iterated ν c _ hI1, integral_eq_iterated ν c _ hI2, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_integrable_line ν c _ hI0, ae_integrable_line ν c _ hI1,
    ae_integrable_line ν c _ hI2] with y h0 h1 h2
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = insertCoord c 0 y := ⟨_, rfl⟩
  have hins : ∀ s, insertCoord c s y = Function.update x0 c s :=
    fun s => hx0 ▸ insertCoord_eq_update c s y
  simp only [insertCoord_self] at h1 ⊢
  simp only [hins] at h0 h1 h2 ⊢
  have hcu : Continuous (Function.update x0 c) := (isClosedEmbedding_update x0 c).continuous
  have hweak : BlockBand.Model.Construction.HasRealWeakDerivative
      (fun r => f (Function.update x0 c r)) (fun r => g (Function.update x0 c r)) :=
    hasRealWeakDerivative_of_hasDerivAt_off_countable (hf.comp hcu)
      (hg.comp hcu).locallyIntegrable Set.countable_empty (fun s _ => hd x0 s)
  have h := BlockBand.Model.Construction.gaussian_weak_integration_by_parts 0 (v c) hweak h0 h2
    (by simpa only [sub_zero] using h1)
  simpa only [sub_zero] using h

end Generic

/-!
## `GUE` in real coordinates
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Real coordinates of the circular matrix entries. -/
abbrev GCoord (ι : Type) := (ι × ι) × Fin 2

/-- The `GUE` sample map from real standard coordinates. -/
def gueLin (t : ℝ≥0) (x : GCoord ι → ℝ) : Matrix ι ι ℂ :=
  gueSample t (circularBrownianCoordinates x)

/-- The standard real Gaussian vector on `GCoord ι`. -/
def stdGauss (ι : Type) [Fintype ι] : Measure (GCoord ι → ℝ) :=
  Measure.pi fun _ : GCoord ι => gaussianReal 0 1

instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (stdGauss ι) := by
  unfold stdGauss; infer_instance

theorem gueMeasure_eq_map_gueLin (t : ℝ≥0) :
    gueMeasure ι t = (stdGauss ι).map (gueLin t) := by
  unfold gueMeasure commonCircularIncrementLaw stdGauss gueLin
  rw [Measure.map_map (BlockBand.Window.Count.continuous_gueSample' t).measurable
    BlockBand.Window.Count.continuous_circularBrownianCoordinates'.measurable]
  rfl

theorem continuous_gueLin (t : ℝ≥0) : Continuous (gueLin (ι := ι) t) :=
  (BlockBand.Window.Count.continuous_gueSample' t).comp
    BlockBand.Window.Count.continuous_circularBrownianCoordinates'

theorem gueLin_apply (t : ℝ≥0) (x : GCoord ι → ℝ) (a b : ι) :
    gueLin t x a b = ((Real.sqrt t / 2 : ℝ) : ℂ) *
      ((x ((a, b), 0) : ℂ) + (x ((a, b), 1) : ℂ) * Complex.I +
        ((x ((b, a), 0) : ℂ) - (x ((b, a), 1) : ℂ) * Complex.I)) := by
  simp only [gueLin, gueSample, circularBrownianCoordinates, Matrix.of_apply]
  have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ((t : ℝ) / 2) = Real.sqrt t / Real.sqrt 2 := Real.sqrt_div' _ (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [hs]
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> field_simp <;>
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring

theorem gueLin_add (t : ℝ≥0) (x y : GCoord ι → ℝ) :
    gueLin t (x + y) = gueLin t x + gueLin t y := by
  ext a b; simp only [gueLin_apply, Pi.add_apply, Matrix.add_apply]; push_cast; ring

theorem gueLin_smul (t : ℝ≥0) (r : ℝ) (x : GCoord ι → ℝ) :
    gueLin t (r • x) = (r : ℂ) • gueLin t x := by
  ext a b; simp only [gueLin_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; push_cast; ring

theorem isHermitian_gueLin (t : ℝ≥0) (x : GCoord ι → ℝ) : (gueLin t x).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, gueLin_apply, star_mul', Complex.star_def, map_add, map_sub,
    map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The coordinate direction `E_j = gueLin t (e_j)`. -/
def gueDir (t : ℝ≥0) (j : GCoord ι) : Matrix ι ι ℂ := gueLin t (Pi.single j 1)

/-- `gueLin` as a real-linear map. -/
def gueLinMap (t : ℝ≥0) : (GCoord ι → ℝ) →ₗ[ℝ] Matrix ι ι ℂ where
  toFun := gueLin t
  map_add' := gueLin_add t
  map_smul' r x := by rw [gueLin_smul]; rfl

theorem gueLin_eq_sum (t : ℝ≥0) (x : GCoord ι → ℝ) :
    gueLin t x = ∑ j, (x j : ℂ) • gueDir t j := by
  have hx : x = ∑ j, x j • (Pi.single j (1 : ℝ) : GCoord ι → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  change gueLinMap t _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  change (x j) • gueLin t (Pi.single j 1) = _
  rw [Complex.coe_smul]; rfl

theorem gueLin_update (t : ℝ≥0) (x : GCoord ι → ℝ) (j : GCoord ι) (r : ℝ) :
    gueLin t (Function.update x j r) = gueLin t x + ((r - x j : ℝ) : ℂ) • gueDir t j := by
  have : Function.update x j r = x + (r - x j) • (Pi.single j (1 : ℝ) : GCoord ι → ℝ) := by
    ext k; by_cases hk : k = j
    · subst hk; simp
    · simp [hk, Function.update_of_ne hk]
  rw [this, gueLin_add, gueLin_smul]; rfl

/-- **Covariance of the coordinate directions**: `Σ_j (E_j)_{ab}(E_j)_{cd} = t δ_{ad} δ_{bc}`. -/
theorem sum_gueDir_mul_gueDir (t : ℝ≥0) (a b c d : ι) :
    ∑ j, gueDir t j a b * gueDir t j c d = if a = d ∧ b = c then (t : ℂ) else 0 := by
  have hE : ∀ (u : ι × ι) (k : Fin 2) (a b : ι), gueDir t (u, k) a b =
      ((Real.sqrt t / 2 : ℝ) : ℂ) * ((if k = 0 then 1 else Complex.I) * (if u = (a, b) then 1 else 0) +
        (if k = 0 then 1 else -Complex.I) * (if u = (b, a) then 1 else 0)) := by
    intro u k a b
    rw [gueDir, gueLin_apply]
    congr 1
    have e1 : ∀ (w : ι × ι) (l : Fin 2), (Pi.single (u, k) (1 : ℝ) : GCoord ι → ℝ) (w, l) =
        if (u, k) = (w, l) then 1 else 0 := by
      intro w l; rw [Pi.single_apply]; simp only [eq_comm]
    simp only [e1]
    fin_cases k <;> by_cases h1 : u = (a, b) <;> by_cases h2 : u = (b, a) <;>
      simp [h1, h2] <;> split_ifs <;> simp
  have hs : ((Real.sqrt t / 2 : ℝ) : ℂ) * ((Real.sqrt t / 2 : ℝ) : ℂ) = (t : ℂ) / 4 := by
    rw [← Complex.ofReal_mul]
    have : Real.sqrt t / 2 * (Real.sqrt t / 2) = (t : ℝ) / 4 := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (NNReal.coe_nonneg t)]; ring
    rw [this]; push_cast; ring
  have hs' : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = ((t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, hE]
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_true, ite_false, one_ne_zero]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
  rw [hs]
  by_cases h1 : a = d <;> by_cases h2 : b = c <;> by_cases h3 : a = c <;> by_cases h4 : b = d <;>
    simp [h1, h2, h3, h4, Prod.ext_iff, eq_comm] <;> (try split_ifs) <;>
    (try simp only [← hs']) <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf

/-!
## The resolvent and its coordinate derivatives
-/

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-- `R_η(G) = (K + G - iη)⁻¹`. -/
def res (K : Matrix ι ι ℂ) (η : ℝ) (G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (K + G - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹

theorem im_eta_I (η : ℝ) : ((η : ℂ) * Complex.I).im = η := by simp

theorem det_res_ne_zero {K G : Matrix ι ι ℂ} (hKG : (K + G).IsHermitian) {η : ℝ} (hη : η ≠ 0) :
    (K + G - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)).det ≠ 0 :=
  BlockBand.LocalWindow.ProofCertificate.det_sub_smul_ne_zero hKG (by rw [im_eta_I]; exact hη)

/-- Entries of the resolvent are bounded by `|η|⁻¹`. -/
theorem norm_res_apply_le {K G : Matrix ι ι ℂ} (hKG : (K + G).IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (a b : ι) : ‖res K η G a b‖ ≤ |η|⁻¹ := by
  have h := BlockBand.LocalWindow.ProofCertificate.norm_resolvent_le hKG
    (z := (η : ℂ) * Complex.I) (by rw [im_eta_I]; exact hη) (EuclideanSpace.single b 1)
  rw [im_eta_I, PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have he : res K η G a b = (T (res K η G) (EuclideanSpace.single b 1)) a := by
    change _ = (res K η G *ᵥ (Pi.single b 1 : ι → ℂ)) a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [he]
  exact PiLp.norm_apply_le _ _

theorem continuous_res {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) : Continuous fun x : GCoord ι → ℝ => res K η (gueLin t x) := by
  have hA : Continuous fun x : GCoord ι → ℝ =>
      K + gueLin t x - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) :=
    (continuous_const.add (continuous_gueLin t)).sub continuous_const
  have hdet : ∀ x : GCoord ι → ℝ,
      (K + gueLin t x - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)).det ≠ 0 :=
    fun x => det_res_ne_zero (hK.add (isHermitian_gueLin t x)) hη
  have : (fun x : GCoord ι → ℝ => res K η (gueLin t x)) = fun x =>
      (K + gueLin t x - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)).det⁻¹ •
        (K + gueLin t x - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)).adjugate := by
    funext x; rw [res, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (hA.matrix_det.inv₀ hdet).smul hA.matrix_adjugate

/-- **The resolvent along a coordinate line**: `∂_j R = -R E_j R`. -/
theorem hasDerivAt_res_line {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) (x : GCoord ι → ℝ) (j : GCoord ι) (s : ℝ) (a b : ι) :
    HasDerivAt (fun r => res K η (gueLin t (Function.update x j r)) a b)
      (-(res K η (gueLin t (Function.update x j s)) * gueDir t j *
        res K η (gueLin t (Function.update x j s))) a b) s := by
  set y := Function.update x j s
  set A := K + gueLin t y - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)
  have hy : ∀ r, Function.update x j r = Function.update y j r := fun r => by
    simp [y]
  have hline : ∀ r, res K η (gueLin t (Function.update x j r)) =
      (A + ((r - s : ℝ) : ℂ) • gueDir t j)⁻¹ := by
    intro r
    rw [hy, gueLin_update, res]
    simp only [y, Function.update_self, A]
    congr 1; abel
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr
    (det_res_ne_zero (hK.add (isHermitian_gueLin t y)) hη)
  have h0 := hasDerivAt_inv_affineLine A (gueDir t j) hu a b
  have h1 : HasDerivAt (fun r : ℝ => (A + ((r - s : ℝ) : ℂ) • gueDir t j)⁻¹ a b)
      (-(A⁻¹ * gueDir t j * A⁻¹) a b) s := by
    have h0' : HasDerivAt (fun r : ℝ => (A + (r : ℂ) • gueDir t j)⁻¹ a b)
        (-(A⁻¹ * gueDir t j * A⁻¹) a b) (s - s) := by rw [sub_self]; exact h0
    exact h0'.comp_sub_const s s
  simp only [hline]
  exact h1

/-- `f_j(x) = Tr(E_j R(G(x)))`. -/
def traceDirRes (K : Matrix ι ι ℂ) (η : ℝ) (t : ℝ≥0) (j : GCoord ι) (x : GCoord ι → ℝ) : ℂ :=
  (gueDir t j * res K η (gueLin t x)).trace

/-- `g_j(x) = -Tr(E_j R E_j R)`. -/
def traceDirResDeriv (K : Matrix ι ι ℂ) (η : ℝ) (t : ℝ≥0) (j : GCoord ι)
    (x : GCoord ι → ℝ) : ℂ :=
  -(gueDir t j * res K η (gueLin t x) * gueDir t j * res K η (gueLin t x)).trace

theorem hasDerivAt_traceDirRes_line {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ}
    (hη : η ≠ 0) (t : ℝ≥0) (j : GCoord ι) (x : GCoord ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r => traceDirRes K η t j (Function.update x j r))
      (traceDirResDeriv K η t j (Function.update x j s)) s := by
  set R := res K η (gueLin t (Function.update x j s))
  have h : HasDerivAt (fun r => ∑ a, ∑ b, gueDir t j a b *
      res K η (gueLin t (Function.update x j r)) b a)
      (∑ a, ∑ b, gueDir t j a b * (-(R * gueDir t j * R)) b a) s :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
      (hasDerivAt_res_line hK hη t x j s b a).const_mul _
  have e1 : (fun r => traceDirRes K η t j (Function.update x j r)) = fun r => ∑ a, ∑ b,
      gueDir t j a b * res K η (gueLin t (Function.update x j r)) b a := by
    funext r; simp [traceDirRes, Matrix.trace, Matrix.mul_apply]
  have e2 : traceDirResDeriv K η t j (Function.update x j s) =
      ∑ a, ∑ b, gueDir t j a b * (-(R * gueDir t j * R)) b a := by
    simp only [traceDirResDeriv, Matrix.trace, Matrix.diag, Matrix.neg_apply, mul_neg,
      Finset.sum_neg_distrib, R]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.mul_assoc, Matrix.mul_apply (M := gueDir t j)]
  rw [e1, e2]; exact h

theorem trace_mul_four (M N P Q : Matrix ι ι ℂ) :
    (M * N * P * Q).trace = ∑ a, ∑ d, ∑ c, ∑ b, M a b * N b c * P c d * Q d a := by
  simp [Matrix.trace, Matrix.mul_apply, Finset.sum_mul]

/-- `Σ_j Tr(E_j R E_j R) = t (Tr R)²` (the covariance contraction). -/
theorem sum_trace_gueDir_res (t : ℝ≥0) (R : Matrix ι ι ℂ) :
    ∑ j, (gueDir t j * R * gueDir t j * R).trace = (t : ℂ) * R.trace ^ 2 := by
  simp only [trace_mul_four]
  have h1 : ∀ a d c b, ∑ j, gueDir t j a b * R b c * gueDir t j c d * R d a =
      (if a = d ∧ b = c then (t : ℂ) else 0) * (R b c * R d a) := by
    intro a d c b
    rw [← sum_gueDir_mul_gueDir t a b c d, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, ∑ a, ∑ d, ∑ c, ∑ b, gueDir t j a b * R b c * gueDir t j c d * R d a =
      ∑ a, ∑ d, ∑ c, ∑ b, ∑ j, gueDir t j a b * R b c * gueDir t j c d * R d a := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
  rw [h2]
  simp only [h1]
  rw [Matrix.trace, sq, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single a (fun d hd => by
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (fun h => hd h.1.symm), zero_mul])]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_eq_single b (fun c hc => by rw [ite_eq_right (fun h => hc h.2.symm), zero_mul])]
  simp only [and_self, ite_true, Matrix.diag]; ring

theorem norm_apply_le_sum (M : Matrix ι ι ℂ) (a b : ι) : ‖M a b‖ ≤ ∑ a, ∑ b, ‖M a b‖ :=
  (Finset.single_le_sum (f := fun b => ‖M a b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖M a b‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))

/-- Crude bound `|Tr(M N)| ≤ |ι|² (Σ|M_ab|) r` when the entries of `N` are `≤ r`. -/
theorem norm_trace_mul_le (M N : Matrix ι ι ℂ) {r : ℝ} (hN : ∀ a b, ‖N a b‖ ≤ r) :
    ‖(M * N).trace‖ ≤ (Fintype.card ι : ℝ) ^ 2 * ((∑ a, ∑ b, ‖M a b‖) * r) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ a, ‖∑ b, M a b * N b a‖ ≤ (Fintype.card ι : ℝ) * ((∑ a, ∑ b, ‖M a b‖) * r) := by
    intro a
    refine (norm_sum_le _ _).trans ?_
    have : ∀ b, ‖M a b * N b a‖ ≤ (∑ a, ∑ b, ‖M a b‖) * r := fun b => by
      rw [norm_mul]; exact mul_le_mul (norm_apply_le_sum M a b) (hN b a) (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    refine (Finset.sum_le_sum fun b _ => this b).trans ?_
    simp
  refine (Finset.sum_le_sum fun a _ => h a).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring_nf; rfl

/-- Crude bound for `|Tr(M N P Q)|` when the entries of `N, Q` are `≤ r`. -/
theorem norm_trace_mul_four_le (M N P Q : Matrix ι ι ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hN : ∀ a b, ‖N a b‖ ≤ r) (hQ : ∀ a b, ‖Q a b‖ ≤ r) :
    ‖(M * N * P * Q).trace‖ ≤
      (Fintype.card ι : ℝ) ^ 4 * ((∑ a, ∑ b, ‖M a b‖) * r * (∑ a, ∑ b, ‖P a b‖) * r) := by
  rw [trace_mul_four]
  set B := (∑ a, ∑ b, ‖M a b‖) * r * (∑ a, ∑ b, ‖P a b‖) * r
  have hM0 : 0 ≤ ∑ a, ∑ b, ‖M a b‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hP0 : 0 ≤ ∑ a, ∑ b, ‖P a b‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hterm : ∀ a d c b, ‖M a b * N b c * P c d * Q d a‖ ≤ B := by
    intro a d c b
    simp only [norm_mul, B]
    gcongr
    · exact norm_apply_le_sum M a b
    · exact hN b c
    · exact norm_apply_le_sum P c d
    · exact hQ d a
  have hsum : ‖∑ a, ∑ d, ∑ c, ∑ b, M a b * N b c * P c d * Q d a‖ ≤ ∑ _a : ι, ∑ _d : ι, ∑ _c : ι, ∑ _b : ι, B :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun d _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun c _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b _ => hterm a d c b))))
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem measurable_res (K : Matrix ι ι ℂ) (η : ℝ) : Measurable (res K η) := by
  have : res K η = fun G => Ring.inverse (K + G - ((η : ℂ) * Complex.I) • 1).det •
      (K + G - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)).adjugate := by
    funext G; rw [res, Matrix.inv_def]
  rw [this]
  have hA : Continuous fun G : Matrix ι ι ℂ => K + G - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) :=
    (continuous_const.add continuous_id).sub continuous_const
  simp only [Ring.inverse_eq_inv']
  exact (measurable_inv.comp hA.matrix_det.measurable).smul hA.matrix_adjugate.measurable

theorem integrable_coord (j : GCoord ι) : Integrable (fun x : GCoord ι → ℝ => x j) (stdGauss ι) :=
  integrable_comp_eval (f := id) ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl)

/-- **Gaussian integration by parts for `Tr G R_η`**: for Hermitian `K` and
`η ≠ 0`, under `G ~ gueMeasure ι t`, `E Tr(G R) = -t E(Tr R)²`, `R = (K + G - iη)⁻¹`. -/
theorem integral_trace_mul_res {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) :
    ∫ G, (G * res K η G).trace ∂gueMeasure ι t =
      -(t : ℂ) * ∫ G, (res K η G).trace ^ 2 ∂gueMeasure ι t := by
  have hentry : ∀ a b : ι, Measurable fun G : Matrix ι ι ℂ => res K η G a b := fun a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (measurable_res K η))
  have hmeas1 : Measurable fun G : Matrix ι ι ℂ => (G * res K η G).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      (show Measurable fun G : Matrix ι ι ℂ => G a b from
        (measurable_pi_apply b).comp (measurable_pi_apply a)).mul (hentry b a)
  have hmeas2 : Measurable fun G : Matrix ι ι ℂ => (res K η G).trace ^ 2 := by
    simp only [Matrix.trace, Matrix.diag]
    exact (Finset.measurable_sum _ fun a _ => hentry a a).pow_const 2
  have hKG : ∀ x : GCoord ι → ℝ, (K + gueLin t x).IsHermitian :=
    fun x => hK.add (isHermitian_gueLin t x)
  have hR := continuous_res hK hη t
  have hRb : ∀ x : GCoord ι → ℝ, ∀ a b, ‖res K η (gueLin t x) a b‖ ≤ |η|⁻¹ :=
    fun x a b => norm_res_apply_le (hKG x) hη a b
  have hη0 : 0 ≤ |η|⁻¹ := inv_nonneg.mpr (abs_nonneg η)
  have hcf : ∀ j, Continuous (traceDirRes K η t j) := fun j =>
    (continuous_const.matrix_mul hR).matrix_trace
  have hcg : ∀ j, Continuous (traceDirResDeriv K η t j) := fun j =>
    ((((continuous_const.matrix_mul hR).matrix_mul continuous_const).matrix_mul hR).matrix_trace).neg
  have hbf : ∀ j x, ‖traceDirRes K η t j x‖ ≤
      (Fintype.card ι : ℝ) ^ 2 * ((∑ a, ∑ b, ‖gueDir t j a b‖) * |η|⁻¹) :=
    fun j x => norm_trace_mul_le _ _ (hRb x)
  have hbg : ∀ j x, ‖traceDirResDeriv K η t j x‖ ≤ (Fintype.card ι : ℝ) ^ 4 *
      ((∑ a, ∑ b, ‖gueDir t j a b‖) * |η|⁻¹ * (∑ a, ∑ b, ‖gueDir t j a b‖) * |η|⁻¹) :=
    fun j x => by rw [traceDirResDeriv, norm_neg]; exact norm_trace_mul_four_le _ _ _ _ hη0 (hRb x) (hRb x)
  have hIf : ∀ j, Integrable (traceDirRes K η t j) (stdGauss ι) := fun j =>
    Integrable.of_bound (hcf j).aestronglyMeasurable _ (ae_of_all _ (hbf j))
  have hIg : ∀ j, Integrable (traceDirResDeriv K η t j) (stdGauss ι) := fun j =>
    Integrable.of_bound (hcg j).aestronglyMeasurable _ (ae_of_all _ (hbg j))
  have hIxf : ∀ j, Integrable (fun x => x j • traceDirRes K η t j x) (stdGauss ι) := fun j =>
    (integrable_coord j).smul_bdd _ (hcf j).aestronglyMeasurable (ae_of_all _ (hbf j))
  have hibp : ∀ j, ∫ x, x j • traceDirRes K η t j x ∂stdGauss ι =
      ∫ x, traceDirResDeriv K η t j x ∂stdGauss ι := by
    intro j
    have h := gaussian_ibp_of_line (fun _ : GCoord ι => (1 : ℝ≥0)) _ _ j (hcf j) (hcg j)
      (fun x s => hasDerivAt_traceDirRes_line hK hη t j x s) (hIf j) (hIxf j) (hIg j)
    simpa [stdGauss] using h
  have hpt : ∀ x : GCoord ι → ℝ, (gueLin t x * res K η (gueLin t x)).trace =
      ∑ j, x j • traceDirRes K η t j x := by
    intro x
    rw [show (gueLin t x * res K η (gueLin t x)).trace =
        ((∑ j, (x j : ℂ) • gueDir t j) * res K η (gueLin t x)).trace by rw [← gueLin_eq_sum],
      Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, traceDirRes, Complex.coe_smul]
  have hpt2 : ∀ x : GCoord ι → ℝ, ∑ j, traceDirResDeriv K η t j x =
      -(t : ℂ) * (res K η (gueLin t x)).trace ^ 2 := by
    intro x
    simp only [traceDirResDeriv, Finset.sum_neg_distrib, sum_trace_gueDir_res, neg_mul]
  rw [gueMeasure_eq_map_gueLin, integral_map (continuous_gueLin t).aemeasurable
    hmeas1.aestronglyMeasurable, integral_map (continuous_gueLin t).aemeasurable
    hmeas2.aestronglyMeasurable]
  simp only [hpt]
  rw [integral_finsetSum _ (fun j _ => hIxf j)]
  simp only [hibp]
  rw [← integral_finsetSum _ (fun j _ => hIg j)]
  simp only [hpt2]
  rw [integral_const_mul]

end BlockBand.DeterminantScore.SelectedIBP
