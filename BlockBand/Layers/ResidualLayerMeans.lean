module

public import BlockBand.Layers.ResidualPair
public import BlockBand.Layers.CoreMeans
public import BlockBand.Layers.ResidualLayerStability

/-!
# Gaussian coordinates, Schwinger–Dyson equation and fluctuations of the residual pair layer

Law: `rpLaw` is the image of `gaussianProduct (rlVar W b s)` under `rlEmbed` (`rl_law_eq_map`).
Norms: `ℓ²` operator norm on matrices, modulus on `ℂ`, `L^p` of `gaussianProduct`.

The key simplification: `‖G‖ ≤ (s|Im a|)⁻¹` deterministically (`rl_norm_G_le`), so no absorption
or inverse-moment input is needed.

## Main results

* `rl_law_eq_map`, `rl_matrix_eq`: coordinates; `V - E - X - sa = C₀ + L x` with `L` linear.
* `rlS_eq`: the Gaussian contraction is `S(G) = diag(α tr_k G + β tr_{1-k} G)`,
  `α = W t_A = c - s/2`, `β = W t_B = b - s/2` (block-constant).
* `rl_weighted_le`: `Σᵢ vᵢ |Tr(K Λᵢ)|² ≤ 4² ‖K‖²`.
* `rl_mean_identity`: exact Schwinger–Dyson identity (`core_limit_identity`) for the means
  `m̄_j = E W⁻¹Tr P_j G`: `m̄_j = W⁻¹Tr P_j M̄ + E W⁻¹Tr P_j (M̄ diag(φ(g) - φ(m̄)) G)`,
  `M̄ = (H - diag σ(m̄))⁻¹`, `σ = rlShift s α β a`, `H = -E - X`.
* `rl_resid_bound`: `|m̄_j - W⁻¹Tr P_j M̄| ≤ 2 (α + β) A(K) A(1)`, `A(n) = Cg √2 (16 n/W) K²`
  (covariances of normalized traces, `core_cov_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open BlockBand.SourceProcess (circularBrownianCoordinates)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. Real Gaussian coordinates of the residual pair layer
-/

/-- Real coordinates: the two GUE blocks (`gueOfCoords`, variance `1`), then the bond. -/
abbrev RlCoord (W : ℕ) := (Fin 2 × GaussCoord W) ⊕ (Fin W × Fin W × Fin 2)

/-- Entry variance of the diagonal blocks, `(c - s/2)/W`. -/
def rlTA (W : ℕ) (b s : ℝ) : ℝ≥0 := Real.toNNReal ((1 - 2 * b - s / 2) / W)

/-- Entry variance of the internal bond, `(b - s/2)/W`. -/
def rlTB (W : ℕ) (b s : ℝ) : ℝ≥0 := Real.toNNReal ((b - s / 2) / W)

/-- Coordinate variances: `1` on block coordinates, `t_B/2` on bond coordinates. -/
def rlVar (W : ℕ) (b s : ℝ) : RlCoord W → ℝ≥0 :=
  Sum.elim (fun _ => 1) (fun _ => rlTB W b s / 2)

/-- The residual pair sample from real coordinates. -/
def rlEmbed (W : ℕ) (b s : ℝ) (x : RlCoord W → ℝ) : RpSample W :=
  (fun j => gueOfCoords W (rlTA W b s) (fun c => x (Sum.inl (j, c))),
    ginibreAssemble (fun c => x (Sum.inr c)))

theorem rl_measurable_embed (W : ℕ) (b s : ℝ) : Measurable (rlEmbed W b s) := by
  unfold rlEmbed
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun a => ?_
    exact (measurable_gueOfCoords W _).comp (by fun_prop)
  · exact measurable_ginibreAssemble.comp (by fun_prop)

/-- **The residual pair law in real Gaussian coordinates.** -/
theorem rl_law_eq_map (W : ℕ) (b s : ℝ) :
    rpLaw W b s = (gaussianProduct (rlVar W b s)).map (rlEmbed W b s) := by
  have h1 : (Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) (rlTA W b s)) =
      (whiteNoise (Fin 2 × GaussCoord W) 1).map
        (fun r a => gueOfCoords W (rlTA W b s) (fun c => r (a, c))) := by
    simp only [gueMeasure_eq_map]
    exact pi_map_whiteNoise 1 _ (measurable_gueOfCoords W _)
  have h3 : (whiteNoise (Fin 2 × GaussCoord W) 1).prod
      (whiteNoise (Fin W × Fin W × Fin 2) (rlTB W b s / 2)) =
      (gaussianProduct (rlVar W b s)).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : RlCoord W => ℝ)) :=
    ((measurePreserving_sumPiEquivProdPi
      (fun i : RlCoord W => gaussianReal 0 (rlVar W b s i))).map_eq).symm
  have hg : Measurable (fun (r : Fin 2 × GaussCoord W → ℝ) (a : Fin 2) =>
      gueOfCoords W (rlTA W b s) (fun c => r (a, c))) :=
    measurable_pi_iff.mpr fun a => (measurable_gueOfCoords W _).comp (by fun_prop)
  change (Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) (rlTA W b s)).prod
    (ginibreMeasure (Fin W) (Fin W) (rlTB W b s)) = _
  rw [h1, ginibreMeasure_eq_map, Measure.map_prod_map _ _ hg measurable_ginibreAssemble, h3,
    Measure.map_map (hg.prodMap measurable_ginibreAssemble) (MeasurableEquiv.measurable _)]
  rfl

/-!
## 2. The residual matrix is affine in the coordinates
-/

theorem rl_lin_add (W : ℕ) (b s : ℝ) (x y : RlCoord W → ℝ) :
    rpMatrix (rlEmbed W b s (x + y)) = rpMatrix (rlEmbed W b s x) + rpMatrix (rlEmbed W b s y) := by
  ext p q
  simp only [rpMatrix, rlEmbed, gueOfCoords, gueSample, circularBrownianCoordinates,
    ginibreAssemble, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> push_cast <;> (try simp only [map_add, map_mul, star_add, Complex.conj_ofReal,
    Complex.conj_I, Complex.star_def, map_div₀]) <;> ring

theorem rl_lin_smul (W : ℕ) (b s : ℝ) (r : ℝ) (x : RlCoord W → ℝ) :
    rpMatrix (rlEmbed W b s (r • x)) = r • rpMatrix (rlEmbed W b s x) := by
  ext p q
  simp only [rpMatrix, rlEmbed, gueOfCoords, gueSample, circularBrownianCoordinates,
    ginibreAssemble, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  split_ifs <;> push_cast <;> (try simp only [map_add, map_mul, star_add, star_mul',
    Complex.conj_ofReal, Complex.conj_I, Complex.star_def, map_div₀]) <;> ring

/-- The coordinate-linear part `x ↦ V(x)` as an `ℝ`-linear map. -/
def rlLinMap (W : ℕ) (b s : ℝ) :
    (RlCoord W → ℝ) →ₗ[ℝ] Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ where
  toFun x := rpMatrix (rlEmbed W b s x)
  map_add' := rl_lin_add W b s
  map_smul' := rl_lin_smul W b s

/-- The coordinate-linear part as a continuous linear map. -/
def rlLin (W : ℕ) (b s : ℝ) :
    (RlCoord W → ℝ) →L[ℝ] Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  LinearMap.toContinuousLinearMap (rlLinMap W b s)

theorem rlLin_apply (W : ℕ) (b s : ℝ) (x : RlCoord W → ℝ) :
    rlLin W b s x = rpMatrix (rlEmbed W b s x) := rfl

/-- The constant part `C₀ = -E - X - sa`. -/
def rlC0 {W : ℕ} (E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  cmpTopH E X - ((s : ℂ) * matchedA E) • 1

theorem rl_matrix_eq {W : ℕ} (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : RlCoord W → ℝ) :
    (rlC0 E s X + rlLin W b s x)⁻¹ = rpResolvent E s X (rlEmbed W b s x) := by
  rw [rpResolvent, rlLin_apply, rlC0, cmpTopH]
  congr 1
  abel

theorem rl_embed_herm (W : ℕ) (b s : ℝ) (x : RlCoord W → ℝ) :
    ∀ j, ((rlEmbed W b s x).1 j).IsHermitian := fun _ => gueOfCoords_isHermitian _ _ _

/-- The Hermitian part `V - E - X`. -/
theorem rl_herm_part {W : ℕ} (b E s : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (x : RlCoord W → ℝ) :
    (rlLin W b s x + cmpTopH E X).IsHermitian := by
  rw [rlLin_apply]
  exact (rp_rpMatrix_isHermitian _ (rl_embed_herm W b s x)).add (cmpTopH_isHermitian E hX)

theorem rl_C0_add {W : ℕ} (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : RlCoord W → ℝ) (c : ℂ) :
    rlC0 E s X + c • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + rlLin W b s x =
      (rlLin W b s x + cmpTopH E X) - diagonal (fun _ => (s : ℂ) * matchedA E - c) := by
  rw [rlC0, ← smul_one_eq_diagonal, sub_smul]
  abel

theorem rl_matchedA_im_nonpos (E : ℝ) : (matchedA E).im ≤ 0 := by
  have : (matchedA E).im = -Real.sqrt (4 - E ^ 2) / 2 := rfl
  rw [this]
  have := Real.sqrt_nonneg (4 - E ^ 2)
  linarith

/-- **Regularity** of the affine family (`CoreReg`), for `s ≥ 0`. -/
theorem rl_reg {W : ℕ} (b E : ℝ) {s : ℝ} (hs : 0 ≤ s)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    CoreReg (rlC0 E s X) (rlLin W b s) := by
  intro κ hκ x
  have hH := rl_herm_part b E s hX x
  have he : corePsi (rlC0 E s X) (rlLin W b s) κ x = (rlLin W b s x + cmpTopH E X) -
      diagonal (fun _ => (s : ℂ) * matchedA E - (κ : ℂ) * Complex.I) := rl_C0_add b E s X x _
  have him : ∀ p : Fin 2 × Fin W, κ ≤ -((fun _ => (s : ℂ) * matchedA E - (κ : ℂ) * Complex.I) p).im := by
    intro p
    simp only [Complex.sub_im, Complex.im_ofReal_mul, Complex.mul_I_im, Complex.ofReal_re]
    have := mul_nonpos_of_nonneg_of_nonpos hs (rl_matchedA_im_nonpos E)
    linarith
  have hneg : ∀ p : Fin 2 × Fin W,
      ((fun _ => (s : ℂ) * matchedA E - (κ : ℂ) * Complex.I) p).im < 0 :=
    fun p => by linarith [him p]
  rw [he, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.isUnit_iff_isUnit_det]
  exact ⟨isUnit_iff_ne_zero.mpr (cmp_det_ne_zero _ hH _ hneg),
    lct_norm_shifted_inv_le _ hH _ hκ him⟩

/-- The resolvent in coordinates. -/
def rlG {W : ℕ} (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (rlC0 E s X + rlLin W b s x)⁻¹

theorem rlG_eq {W : ℕ} (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : RlCoord W → ℝ) :
    rlG b E s X x = (rlLin W b s x + cmpTopH E X - diagonal (fun _ => (s : ℂ) * matchedA E))⁻¹ := by
  rw [rlG]
  congr 1
  have := rl_C0_add b E s X x 0
  rw [zero_smul, add_zero, sub_zero] at this
  exact this

theorem rl_measurable_G {W : ℕ} (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (rlG b E s X) :=
  measurable_matrix_inv.comp (continuous_const.add (rlLin W b s).continuous).measurable

/-- **Deterministic resolvent bound** `‖G‖ ≤ (s y)⁻¹` for `0 < y ≤ -Im a`. -/
theorem rl_norm_G_le {W : ℕ} (b E : ℝ) {s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (x : RlCoord W → ℝ) : ‖rlG b E s X x‖ ≤ (s * y)⁻¹ := by
  rw [rlG_eq]
  refine lct_norm_shifted_inv_le _ (rl_herm_part b E s hX x) _ (by positivity) fun _ => ?_
  rw [Complex.im_ofReal_mul]
  nlinarith

theorem rl_isUnit_G {W : ℕ} (b E : ℝ) {s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (hya : 0 < -(matchedA E).im) (x : RlCoord W → ℝ) :
    IsUnit (rlC0 E s X + rlLin W b s x).det := by
  have := rl_C0_add b E s X x 0
  rw [zero_smul, add_zero, sub_zero] at this
  rw [this]
  refine isUnit_iff_ne_zero.mpr (cmp_det_ne_zero _ (rl_herm_part b E s hX x) _ fun _ => ?_)
  rw [Complex.im_ofReal_mul]
  nlinarith

/-- Sign of the block traces: `Im W⁻¹Tr P_j G ≤ 0`. -/
theorem rl_im_blockTrace_G_nonpos {W : ℕ} (b E : ℝ) {s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (hya : 0 < -(matchedA E).im) (x : RlCoord W → ℝ) (j : Fin 2) :
    (blockTrace (rlG b E s X x) j).im ≤ 0 := by
  rw [cmp_im_blockTrace]
  have hneg : ∀ p : Fin 2 × Fin W, ((fun _ => (s : ℂ) * matchedA E) p).im < 0 := fun _ => by
    simp only [Complex.im_ofReal_mul]; nlinarith
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun z _ => ?_)
  have h := cmp_im_diag_row _ (rl_herm_part b E s hX x) _ hneg (j, z)
  rw [rlG_eq]
  have : 0 ≤ ∑ q, ‖(rlLin W b s x + cmpTopH E X -
      diagonal (fun _ : Fin 2 × Fin W => (s : ℂ) * matchedA E))⁻¹ (j, z) q‖ ^ 2 *
        (-((s : ℂ) * matchedA E).im) :=
    Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (by linarith [hneg q])
  linarith

/-!
## 3. The coordinate matrices and the Gaussian contraction
-/

/-- The coefficient `√(t_A/2)/√2` of a block coordinate matrix. -/
def rlCA (W : ℕ) (b s : ℝ) : ℂ := ((Real.sqrt ((rlTA W b s : ℝ) / 2) / Real.sqrt 2 : ℝ) : ℂ)

theorem rl_lin_A0 (W : ℕ) (b s : ℝ) (j : Fin 2) (α β : Fin W) :
    rlLin W b s (Pi.single (Sum.inl (j, ((α, β), 0))) 1) =
      rlCA W b s • (single (j, α) (j, β) 1 + single (j, β) (j, α) 1) := by
  ext p q
  rcases p with ⟨c, γ⟩
  rcases q with ⟨d, δ⟩
  simp [rlLin_apply, rpMatrix, rlEmbed, gueOfCoords, gueSample, circularBrownianCoordinates,
    ginibreAssemble, Pi.single_apply, Matrix.single_apply, rlCA]
  split_ifs <;> (try casesm* _ ∧ _) <;> subst_vars <;> simp_all <;> ring

theorem rl_lin_A1 (W : ℕ) (b s : ℝ) (j : Fin 2) (α β : Fin W) :
    rlLin W b s (Pi.single (Sum.inl (j, ((α, β), 1))) 1) =
      rlCA W b s • (single (j, α) (j, β) Complex.I + single (j, β) (j, α) (-Complex.I)) := by
  ext p q
  rcases p with ⟨c, γ⟩
  rcases q with ⟨d, δ⟩
  simp [rlLin_apply, rpMatrix, rlEmbed, gueOfCoords, gueSample, circularBrownianCoordinates,
    ginibreAssemble, Pi.single_apply, Matrix.single_apply, rlCA]
  split_ifs <;> (try casesm* _ ∧ _) <;> subst_vars <;> simp_all <;> first | (right; ring) | ring

theorem rl_lin_B0 (W : ℕ) (b s : ℝ) (α β : Fin W) :
    rlLin W b s (Pi.single (Sum.inr (α, β, 0)) 1) =
      single ((1 : Fin 2), α) ((0 : Fin 2), β) 1 + single ((0 : Fin 2), β) ((1 : Fin 2), α) 1 := by
  ext p q
  rcases p with ⟨c, γ⟩
  rcases q with ⟨d, δ⟩
  simp [rlLin_apply, rpMatrix, rlEmbed, gueOfCoords, gueSample, circularBrownianCoordinates,
    ginibreAssemble, Pi.single_apply, Matrix.single_apply]
  fin_cases c <;> fin_cases d <;> simp <;>
    split_ifs <;> (try casesm* _ ∧ _) <;> subst_vars <;> simp_all

theorem rl_lin_B1 (W : ℕ) (b s : ℝ) (α β : Fin W) :
    rlLin W b s (Pi.single (Sum.inr (α, β, 1)) 1) =
      single ((1 : Fin 2), α) ((0 : Fin 2), β) Complex.I +
        single ((0 : Fin 2), β) ((1 : Fin 2), α) (-Complex.I) := by
  ext p q
  rcases p with ⟨c, γ⟩
  rcases q with ⟨d, δ⟩
  simp [rlLin_apply, rpMatrix, rlEmbed, gueOfCoords, gueSample, circularBrownianCoordinates,
    ginibreAssemble, Pi.single_apply, Matrix.single_apply]
  fin_cases c <;> fin_cases d <;> simp <;>
    split_ifs <;> (try casesm* _ ∧ _) <;> subst_vars <;> simp_all

theorem rlCA_sq (W : ℕ) (b s : ℝ) :
    rlCA W b s * rlCA W b s * 2 = (((rlTA W b s : ℝ) / 2 : ℝ) : ℂ) := by
  have ht := (rlTA W b s).2
  have h1 : Real.sqrt ((rlTA W b s : ℝ) / 2) ^ 2 = (rlTA W b s : ℝ) / 2 :=
    Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have : Real.sqrt ((rlTA W b s : ℝ) / 2) / Real.sqrt 2 * (Real.sqrt ((rlTA W b s : ℝ) / 2) /
      Real.sqrt 2) * 2 = (rlTA W b s : ℝ) / 2 := by
    field_simp
    nlinarith [h1, h2]
  rw [rlCA]
  exact_mod_cast this

theorem rl_pairA (W : ℕ) (b s : ℝ) (G : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2)
    (α β : Fin W) :
    ∑ t : Fin 2, (rlVar W b s (Sum.inl (j, ((α, β), t))) : ℝ) •
      (rlLin W b s (Pi.single (Sum.inl (j, ((α, β), t))) 1) * G *
        rlLin W b s (Pi.single (Sum.inl (j, ((α, β), t))) 1)) =
      (((rlTA W b s : ℝ) / 2 : ℝ) : ℂ) •
        (single (j, α) (j, α) (G (j, β) (j, β)) + single (j, β) (j, β) (G (j, α) (j, α))) := by
  rw [Fin.sum_univ_two]
  simp only [rlVar, Sum.elim_inl, NNReal.coe_one, one_smul]
  rw [rl_lin_A0, rl_lin_A1]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_add, meq_sandwich]
  rw [← rlCA_sq]

theorem rl_pairB (W : ℕ) (b s : ℝ) (G : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (α β : Fin W) :
    ∑ t : Fin 2, (rlVar W b s (Sum.inr (α, β, t)) : ℝ) •
      (rlLin W b s (Pi.single (Sum.inr (α, β, t)) 1) * G *
        rlLin W b s (Pi.single (Sum.inr (α, β, t)) 1)) =
      ((rlTB W b s : ℝ) : ℂ) •
        (single ((1 : Fin 2), α) ((1 : Fin 2), α) (G ((0 : Fin 2), β) ((0 : Fin 2), β)) +
          single ((0 : Fin 2), β) ((0 : Fin 2), β) (G ((1 : Fin 2), α) ((1 : Fin 2), α))) := by
  rw [Fin.sum_univ_two, rl_lin_B0, rl_lin_B1]
  simp only [rlVar, Sum.elim_inr]
  rw [← smul_add, meq_sandwich, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- The block projection `P_j`. -/
def rlProj {W : ℕ} (j : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal (fun p => if p.1 = j then 1 else 0)

/-- Unnormalized block trace. -/
def rlTr {W : ℕ} (G : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) : ℂ :=
  ∑ α : Fin W, G (j, α) (j, α)

theorem rl_sum_single {W : ℕ} (j : Fin 2) :
    ∑ α : Fin W, (single ((j, α) : Fin 2 × Fin W) ((j, α) : Fin 2 × Fin W) (1 : ℂ) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = rlProj j := by
  ext p q
  rcases p with ⟨c, γ⟩
  rcases q with ⟨d, δ⟩
  simp only [rlProj, Matrix.sum_apply, single_apply, diagonal_apply, Prod.mk.injEq]
  by_cases hcd : c = d <;> by_cases hγδ : γ = δ <;> by_cases hcj : c = j
  all_goals simp_all [eq_comm]
  norm_cast
  symm
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨rfl, rfl⟩
  exact hγδ rfl

/-- **The Gaussian contraction**, unnormalized form. -/
theorem rlS_sum (W : ℕ) (b s : ℝ) (G : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    coreS (rlVar W b s) (rlLin W b s) G =
      ∑ j : Fin 2, (((rlTA W b s : ℝ) : ℂ) * rlTr G j) • rlProj j +
        ((rlTB W b s : ℝ) : ℂ) • (rlTr G 0 • rlProj 1 + rlTr G 1 • rlProj 0) := by
  unfold coreS
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp only [rl_pairA, rl_pairB, ← Finset.smul_sum]
  congr 1
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := meq_double_sum G (fun α : Fin W => ((j, α) : Fin 2 × Fin W)) (fun β => (j, β))
    simp only at h
    rw [h, rl_sum_single, ← add_smul, smul_smul]
    congr 1
    unfold rlTr
    push_cast
    ring
  · have h := meq_double_sum G (fun α : Fin W => (((1 : Fin 2), α) : Fin 2 × Fin W))
      (fun β => ((0 : Fin 2), β))
    rw [h, rl_sum_single, rl_sum_single]
    rfl

/-- The block-constant self-energy `φ(v)_k = α v_k + β v_{1-k}`. -/
def rlPhi (α β : ℝ) (v : Fin 2 → ℂ) : Fin 2 → ℂ := fun k => (α : ℂ) * v k + (β : ℂ) * v (1 - k)

/-- `α = c - s/2`. -/
def rlAlpha (b s : ℝ) : ℝ := 1 - 2 * b - s / 2

/-- `β = b - s/2`. -/
def rlBeta (b s : ℝ) : ℝ := b - s / 2

theorem rl_W_TA {W : ℕ} (hW : 0 < W) {b s : ℝ} (h : 0 ≤ rlAlpha b s) :
    (W : ℝ) * (rlTA W b s : ℝ) = rlAlpha b s := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  unfold rlAlpha at h
  rw [rlTA, Real.coe_toNNReal _ (div_nonneg h hW'.le)]
  unfold rlAlpha; field_simp

theorem rl_W_TB {W : ℕ} (hW : 0 < W) {b s : ℝ} (h : 0 ≤ rlBeta b s) :
    (W : ℝ) * (rlTB W b s : ℝ) = rlBeta b s := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  unfold rlBeta at h
  rw [rlTB, Real.coe_toNNReal _ (div_nonneg h hW'.le)]
  unfold rlBeta; field_simp

/-- **The Gaussian contraction is block-constant**: `S(G) = diag(φ(tr G))`. -/
theorem rlS_eq {W : ℕ} (hW : 0 < W) {b s : ℝ} (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
    (G : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    coreS (rlVar W b s) (rlLin W b s) G =
      diagonal (cmpExt (rlPhi (rlAlpha b s) (rlBeta b s) (fun k => blockTrace G k))) := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  have hA : ((rlAlpha b s : ℝ) : ℂ) = (W : ℂ) * ((rlTA W b s : ℝ) : ℂ) := by
    rw [← rl_W_TA hW hα]; push_cast; ring
  have hB : ((rlBeta b s : ℝ) : ℂ) = (W : ℂ) * ((rlTB W b s : ℝ) : ℂ) := by
    rw [← rl_W_TB hW hβ]; push_cast; ring
  rw [rlS_sum]
  ext ⟨c, γ⟩ ⟨d, δ⟩
  simp only [rlProj, rlPhi, cmpExt, blockTrace, rlTr, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.smul_apply, diagonal_apply, smul_eq_mul, hA, hB]
  fin_cases c <;> fin_cases d <;> simp <;> (try split_ifs) <;> (try simp) <;> field_simp

/-!
## 4. The gradient constant
-/

theorem rl_trace_single {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℂ) (P Q : n)
    (u w : ℂ) : (K * (single P Q u + single Q P w)).trace = K Q P * u + K P Q * w := by
  rw [Matrix.mul_add, Matrix.trace_add]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem rl_trace_sq_le {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℂ) (P Q : n)
    (c u w : ℂ) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ‖(K * (c • (single P Q u + single Q P w))).trace‖ ^ 2 ≤
      ‖c‖ ^ 2 * (2 * (‖K Q P‖ ^ 2 + ‖K P Q‖ ^ 2)) := by
  rw [Matrix.mul_smul, Matrix.trace_smul, rl_trace_single, smul_eq_mul, norm_mul, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := tfl_norm_sq_add_le (K Q P) (K P Q) u w 1 (by rw [hu]; norm_num) (by rw [hw]; norm_num)
  linarith

theorem rl_sub_sum_le {W : ℕ} (g : Fin 2 × Fin W → Fin 2 × Fin W → ℝ) (hg : ∀ x y, 0 ≤ g x y)
    (i j : Fin 2) : ∑ α : Fin W, ∑ β : Fin W, g (i, α) (j, β) ≤ ∑ x, ∑ y, g x y := by
  rw [Fintype.sum_prod_type]
  refine (Finset.single_le_sum (f := fun i' => ∑ α : Fin W, ∑ y, g (i', α) y)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _ _)
    (Finset.mem_univ i)).trans' ?_
  refine Finset.sum_le_sum fun α _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun j' => ∑ β : Fin W, g (i, α) (j', β))
    (fun _ _ => Finset.sum_nonneg fun _ _ => hg _ _) (Finset.mem_univ j)

theorem rlCA_norm_sq (W : ℕ) (b s : ℝ) : ‖rlCA W b s‖ ^ 2 = (rlTA W b s : ℝ) / 4 := by
  have ht := (rlTA W b s).2
  rw [rlCA, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  ring

/-- **Weighted coordinate traces**: `Σᵢ vᵢ |Tr(K Λᵢ)|² ≤ 4² ‖K‖²` (for `W t_A, W t_B ≤ 1`). -/
theorem rl_weighted_le {W : ℕ} {b s : ℝ} (hA : (W : ℝ) * (rlTA W b s : ℝ) ≤ 1)
    (hB : (W : ℝ) * (rlTB W b s : ℝ) ≤ 1) (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ i, (rlVar W b s i : ℝ) * ‖(K * rlLin W b s (Pi.single i 1)).trace‖ ^ 2 ≤ 4 ^ 2 * ‖K‖ ^ 2 := by
  set HS := ∑ x, ∑ y, ‖K x y‖ ^ 2 with hHS
  have hHSle : HS ≤ 2 * W * ‖K‖ ^ 2 := by
    have := tfl_hs_le K
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  have hg : ∀ x y, 0 ≤ ‖K x y‖ ^ 2 := fun _ _ => sq_nonneg _
  have htA := (rlTA W b s).2
  have htB := (rlTB W b s).2
  rw [Fintype.sum_sum_type]
  have hblk : ∑ i : Fin 2 × GaussCoord W, (rlVar W b s (Sum.inl i) : ℝ) *
      ‖(K * rlLin W b s (Pi.single (Sum.inl i) 1)).trace‖ ^ 2 ≤ 2 * (rlTA W b s : ℝ) * HS := by
    have h1 : ∀ i : Fin 2 × GaussCoord W, (rlVar W b s (Sum.inl i) : ℝ) *
        ‖(K * rlLin W b s (Pi.single (Sum.inl i) 1)).trace‖ ^ 2 ≤
        (rlTA W b s : ℝ) / 4 * (2 * (‖K (i.1, i.2.1.2) (i.1, i.2.1.1)‖ ^ 2 +
          ‖K (i.1, i.2.1.1) (i.1, i.2.1.2)‖ ^ 2)) := by
      rintro ⟨j, ⟨⟨α, β⟩, t⟩⟩
      simp only [rlVar, Sum.elim_inl, NNReal.coe_one, one_mul]
      fin_cases t
      · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, rl_lin_A0, ← rlCA_norm_sq W b s]
        exact rl_trace_sq_le K _ _ _ _ _ (by simp) (by simp)
      · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, rl_lin_A1, ← rlCA_norm_sq W b s]
        exact rl_trace_sq_le K _ _ _ _ _ (by simp) (by simp)
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    have e1 := tfl_diag_blocks_le (fun x y => ‖K x y‖ ^ 2) hg
    have e2 : ∑ a : Fin 2, ∑ α : Fin W, ∑ β : Fin W, ‖K (a, β) (a, α)‖ ^ 2 ≤ HS := by
      have := tfl_diag_blocks_le (fun x y => ‖K y x‖ ^ 2) (fun _ _ => sq_nonneg _)
      refine this.trans (le_of_eq ?_)
      exact Finset.sum_comm
    simp only [Fin.sum_univ_two] at e1 e2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, nsmul_eq_mul] at *
    nlinarith
  have hbond : ∑ i : Fin W × Fin W × Fin 2, (rlVar W b s (Sum.inr i) : ℝ) *
      ‖(K * rlLin W b s (Pi.single (Sum.inr i) 1)).trace‖ ^ 2 ≤ 4 * (rlTB W b s : ℝ) * HS := by
    have h1 : ∀ i : Fin W × Fin W × Fin 2, (rlVar W b s (Sum.inr i) : ℝ) *
        ‖(K * rlLin W b s (Pi.single (Sum.inr i) 1)).trace‖ ^ 2 ≤
        (rlTB W b s : ℝ) / 2 * (2 * (‖K ((0 : Fin 2), i.2.1) ((1 : Fin 2), i.1)‖ ^ 2 +
          ‖K ((1 : Fin 2), i.1) ((0 : Fin 2), i.2.1)‖ ^ 2)) := by
      rintro ⟨α, β, t⟩
      simp only [rlVar, Sum.elim_inr, NNReal.coe_div, NNReal.coe_ofNat]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      fin_cases t
      · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, rl_lin_B0]
        have := rl_trace_sq_le K ((1 : Fin 2), α) ((0 : Fin 2), β) 1 1 1 (by simp) (by simp)
        simpa using this
      · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, rl_lin_B1]
        have := rl_trace_sq_le K ((1 : Fin 2), α) ((0 : Fin 2), β) 1 Complex.I (-Complex.I)
          (by simp) (by simp)
        simpa using this
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    have e1 : ∑ α : Fin W, ∑ β : Fin W, ‖K ((0 : Fin 2), β) ((1 : Fin 2), α)‖ ^ 2 ≤ HS := by
      have := rl_sub_sum_le (fun x y => ‖K y x‖ ^ 2) (fun _ _ => sq_nonneg _) 1 0
      refine this.trans (le_of_eq ?_)
      exact Finset.sum_comm
    have e2 : ∑ α : Fin W, ∑ β : Fin W, ‖K ((1 : Fin 2), α) ((0 : Fin 2), β)‖ ^ 2 ≤ HS :=
      rl_sub_sum_le (fun x y => ‖K x y‖ ^ 2) hg 1 0
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, nsmul_eq_mul] at *
    nlinarith
  have hK2 := sq_nonneg ‖K‖
  have : 2 * (rlTA W b s : ℝ) * HS ≤ 4 * ‖K‖ ^ 2 := by
    calc 2 * (rlTA W b s : ℝ) * HS ≤ 2 * (rlTA W b s : ℝ) * (2 * W * ‖K‖ ^ 2) := by gcongr
      _ = 4 * ((W : ℝ) * (rlTA W b s : ℝ)) * ‖K‖ ^ 2 := by ring
      _ ≤ 4 * 1 * ‖K‖ ^ 2 := by gcongr
      _ = 4 * ‖K‖ ^ 2 := by ring
  have : 4 * (rlTB W b s : ℝ) * HS ≤ 8 * ‖K‖ ^ 2 := by
    calc 4 * (rlTB W b s : ℝ) * HS ≤ 4 * (rlTB W b s : ℝ) * (2 * W * ‖K‖ ^ 2) := by gcongr
      _ = 8 * ((W : ℝ) * (rlTB W b s : ℝ)) * ‖K‖ ^ 2 := by ring
      _ ≤ 8 * 1 * ‖K‖ ^ 2 := by gcongr
      _ = 8 * ‖K‖ ^ 2 := by ring
  linarith

/-!
## 5. Fluctuations of normalized traces
-/

section Fluct

variable {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}

/-- The normalized trace `W⁻¹ Tr(D G(x))`. -/
def rlF (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) : ℂ :=
  (((W : ℝ)⁻¹ : ℝ) : ℂ) * (D * rlG b E s X x).trace

theorem rl_measurable_F (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Measurable (rlF b E s X D) := by
  have hc : Continuous (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      (((W : ℝ)⁻¹ : ℝ) : ℂ) * (D * M).trace) :=
    continuous_const.mul (continuous_const.matrix_mul continuous_id).matrix_trace
  exact hc.measurable.comp (rl_measurable_G b E s X)

theorem rl_norm_F_le (hW : 0 < W) (D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {K : ℝ} (hG : ∀ x, ‖rlG b E s X x‖ ≤ K) (x : RlCoord W → ℝ) :
    ‖rlF b E s X D x‖ ≤ 2 * (‖D‖ * K) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [rlF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 := tfl_trace_le (D * rlG b E s X x)
  have h2 : ‖D * rlG b E s X x‖ ≤ ‖D‖ * K :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hG x) (norm_nonneg _))
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1
  push_cast at h1
  calc (W : ℝ)⁻¹ * ‖(D * rlG b E s X x).trace‖ ≤ (W : ℝ)⁻¹ * (2 * W * (‖D‖ * K)) := by
        gcongr; exact h1.trans (by gcongr)
    _ = 2 * (‖D‖ * K) := by field_simp

theorem rl_TA_le {b s : ℝ} (hW : 0 < W) (hα : 0 ≤ rlAlpha b s) (hα1 : rlAlpha b s ≤ 1) :
    (W : ℝ) * (rlTA W b s : ℝ) ≤ 1 := by rw [rl_W_TA hW hα]; exact hα1

theorem rl_TB_le {b s : ℝ} (hW : 0 < W) (hβ : 0 ≤ rlBeta b s) (hβ1 : rlBeta b s ≤ 1) :
    (W : ℝ) * (rlTB W b s : ℝ) ≤ 1 := by rw [rl_W_TB hW hβ]; exact hβ1

/-- **Fluctuation bound** for `W⁻¹Tr(D G)`, every `p ≥ 1`:
`‖F - EF‖_p ≤ Cg √p (16 ‖D‖/W) K²`, `K = (s y)⁻¹`. -/
theorem rl_fluct {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
    (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {p : ℝ}
    (hp : 1 ≤ p) :
    eLpNorm (fun x => rlF b E s X D x - ∫ x', rlF b E s X D x' ∂gaussianProduct (rlVar W b s))
        (ENNReal.ofReal p) (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (16 * ‖D‖ / W) * (s * y)⁻¹ ^ 2) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hinv : ∀ᵐ x ∂gaussianProduct (rlVar W b s), IsUnit (rlC0 E s X + rlLin W b s x).det :=
    ae_of_all _ fun x => rl_isUnit_G b E hs hX (lt_of_lt_of_le hy hya) x
  have hmom : eLpNorm (fun x => ‖(rlC0 E s X + rlLin W b s x)⁻¹‖) (ENNReal.ofReal (2 * p))
      (gaussianProduct (rlVar W b s)) ≤ ENNReal.ofReal (s * y)⁻¹ := by
    have hb : ∀ᵐ x ∂gaussianProduct (rlVar W b s), ‖‖rlG b E s X x‖‖ ≤ (s * y)⁻¹ :=
      ae_of_all _ fun x => by rw [norm_norm]; exact rl_norm_G_le b E hs hX hy hya x
    have h1 := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal (2 * p))
      (rl_measurable_G b E s X).norm.aestronglyMeasurable hb
    rw [measure_univ, ENNReal.one_rpow, one_mul] at h1
    exact h1
  have h := core_fluctuation (rlVar W b s) hCg hgr (rl_reg b E hs.le hX) (Γ := 4) (by norm_num)
    (rl_weighted_le (rl_TA_le hW hα hα1) (rl_TB_le hW hβ hβ1)) (W : ℝ)⁻¹ D hp
    (by positivity) hinv hmom
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [abs_of_pos (inv_pos.mpr hW')]
  ring

end Fluct

/-!
## 6. Block traces and pair traces as normalized traces
-/

section Traces

variable {W : ℕ}

theorem rl_norm_proj_le (j : Fin 2) : ‖(rlProj j : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ 1 := by
  rw [rlProj, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

theorem rl_blockTrace_proj (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    blockTrace N j = (((W : ℝ)⁻¹ : ℝ) : ℂ) * (rlProj j * N).trace := by
  unfold blockTrace rlProj
  push_cast
  congr 1
  rw [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases j <;> simp [diagonal_mul]

theorem rl_cmpPair_proj (M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j k : Fin 2) :
    cmpPair M N j k = (((W : ℝ)⁻¹ : ℝ) : ℂ) * (rlProj j * M * rlProj k * N).trace := by
  unfold cmpPair rlProj
  push_cast
  congr 1
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have e : ∀ i : Fin 2 × Fin W, (((diagonal fun p : Fin 2 × Fin W => if p.1 = j then (1 : ℂ) else 0) *
      M * diagonal fun p : Fin 2 × Fin W => if p.1 = k then (1 : ℂ) else 0) * N) i i =
      ∑ q : Fin 2 × Fin W, (if i.1 = j then 1 else 0) * M i q * (if q.1 = k then 1 else 0) *
        N q i := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_diagonal, diagonal_mul]
  rw [Finset.sum_congr rfl fun i _ => e i, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases j <;> fin_cases k <;> simp

end Traces

/-!
## 7. The Schwinger–Dyson mean equation
-/

section Mean

variable {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}

/-- The normalized block trace as a continuous linear map. -/
def rlTrCLM (W : ℕ) (j : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => blockTrace M j
      map_add' := fun M N => by
        simp only [blockTrace, Matrix.add_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c M => by
        simp only [blockTrace, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }

theorem rlTrCLM_apply (j : Fin 2) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    rlTrCLM W j M = blockTrace M j := rfl

/-- The mean normalized block traces `m̄_j = E W⁻¹Tr P_j G`. -/
def rlMean (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) : ℂ :=
  ∫ x, blockTrace (rlG b E s X x) j ∂gaussianProduct (rlVar W b s)

theorem rl_C0_sub (E s α β : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (m : Fin 2 → ℂ) :
    rlC0 E s X - diagonal (cmpExt (rlPhi α β m)) =
      cmpTopH E X - diagonal (cmpExt (rlShift s α β (matchedA E) m)) := by
  ext p q
  simp only [rlC0, Matrix.sub_apply, Matrix.smul_apply, diagonal_apply, Matrix.one_apply, cmpExt,
    rlPhi, rlShift, smul_eq_mul]
  split_ifs <;> ring

theorem rl_integrable_G (hs : 0 < s) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) :
    Integrable (rlG b E s X) (gaussianProduct (rlVar W b s)) :=
  Integrable.of_bound (rl_measurable_G b E s X).aestronglyMeasurable (s * y)⁻¹
    (ae_of_all _ fun x => rl_norm_G_le b E hs hX hy hya x)

theorem rl_mean_im_nonpos (hs : 0 < s) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (k : Fin 2) : (rlMean b E s X k).im ≤ 0 := by
  have hgi : Integrable (fun x => blockTrace (rlG b E s X x) k) (gaussianProduct (rlVar W b s)) :=
    (rlTrCLM W k).integrable_comp (rl_integrable_G hs hX hy hya)
  rw [rlMean, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hgi]
  exact integral_nonpos fun x =>
    rl_im_blockTrace_G_nonpos b E hs hX (lt_of_lt_of_le hy hya) x k

/-- **Exact Schwinger–Dyson identity for the block traces.** With
`M̄ = (H - diag σ(m̄))⁻¹`, `H = -E - X`, `σ = rlShift s α β a`:
`m̄_j = W⁻¹Tr P_j M̄ + E W⁻¹Tr P_j (M̄ diag(φ(g) - φ(m̄)) G)`. -/
theorem rl_mean_identity (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s)
    (hβ : 0 ≤ rlBeta b s) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (j : Fin 2) :
    rlMean b E s X j =
      blockTrace (cmpInv (cmpTopH E X)
        (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (rlMean b E s X))) j +
      ∫ x, blockTrace (cmpInv (cmpTopH E X)
          (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (rlMean b E s X)) *
        diagonal (cmpExt (rlPhi (rlAlpha b s) (rlBeta b s) (fun k => blockTrace (rlG b E s X x) k) -
          rlPhi (rlAlpha b s) (rlBeta b s) (rlMean b E s X))) * rlG b E s X x) j
        ∂gaussianProduct (rlVar W b s) := by
  set μ := gaussianProduct (rlVar W b s) with hμ
  set G := rlG b E s X with hGdef
  set m := rlMean b E s X with hmdef
  set α := rlAlpha b s
  set β := rlBeta b s
  set K := (s * y)⁻¹ with hK
  set H := cmpTopH E X with hH
  set σ := rlShift s α β (matchedA E) m with hσdef
  set Mb := cmpInv H σ with hMb
  set Dm : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := diagonal (cmpExt (rlPhi α β m)) with hDm
  set C0 := rlC0 E s X with hC0
  set v := rlVar W b s
  set L := rlLin W b s
  have hGb : ∀ x, ‖G x‖ ≤ K := fun x => rl_norm_G_le b E hs hX hy hya x
  have hGm : Measurable G := rl_measurable_G b E s X
  have hGi : Integrable G μ := rl_integrable_G hs hX hy hya
  have hinv : ∀ᵐ x ∂μ, IsUnit (C0 + L x).det :=
    ae_of_all _ fun x => rl_isUnit_G b E hs hX (lt_of_lt_of_le hy hya) x
  have hG2 : Integrable (fun x => ‖(C0 + L x)⁻¹‖ ^ 2) μ :=
    Integrable.of_bound (hGm.norm.pow_const 2).aestronglyMeasurable (K ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hGb x) 2)
  have hid := core_limit_identity v (rl_reg b E hs.le hX) hinv hG2
  change C0 * ∫ x, G x ∂μ - ∫ x, coreS v L (G x) * G x ∂μ = 1 at hid
  have hSi : Integrable (fun x => coreS v L (G x) * G x) μ := by
    refine Integrable.of_bound ((core_continuous_S_mul v L).comp_aestronglyMeasurable
      hGm.aestronglyMeasurable) (coreCS v L * K ^ 2) (ae_of_all _ fun x => ?_)
    have h1 : ‖coreS v L (G x) * G x‖ ≤ coreCS v L * ‖G x‖ ^ 2 :=
      calc ‖coreS v L (G x) * G x‖ ≤ ‖coreS v L (G x)‖ * ‖G x‖ := norm_mul_le _ _
        _ ≤ coreCS v L * ‖G x‖ * ‖G x‖ := by gcongr; exact core_norm_S_le v L _
        _ = coreCS v L * ‖G x‖ ^ 2 := by ring
    have h2 : ‖G x‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hGb x) 2
    have := coreCS_nonneg v L
    nlinarith
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  have hσ : ∀ k, (σ k).im < 0 := fun k => by
    have h := rlShift_im s α β (matchedA E) m k
    have h1 := rl_mean_im_nonpos (b := b) hs hX hy hya k
    have h2 := rl_mean_im_nonpos (b := b) hs hX hy hya (1 - k)
    have : 0 < s * -(matchedA E).im := mul_pos hs hya0
    nlinarith [mul_nonneg hα (neg_nonneg.mpr h1), mul_nonneg hβ (neg_nonneg.mpr h2)]
  have hMD : Mb * (C0 - Dm) = 1 := by
    rw [hC0, hDm, rl_C0_sub, hMb, cmpInv]
    exact cmp_inv_mul H (cmpTopH_isHermitian E hX) (cmpExt σ) fun p => hσ p.1
  set Gb := ∫ x, G x ∂μ with hGb'
  set SGG := ∫ x, coreS v L (G x) * G x ∂μ with hSGG
  have hkey : Gb = Mb + (Mb * SGG - Mb * (Dm * Gb)) := by
    have h1 : Gb = Mb * (C0 - Dm) * Gb := by rw [hMD, Matrix.one_mul]
    have h2 : C0 * Gb = 1 + SGG := by rw [← hid]; abel
    have h3 : Gb = Mb * (C0 * Gb - Dm * Gb) := by
      conv_lhs => rw [h1]
      rw [Matrix.mul_assoc, Matrix.sub_mul]
    calc Gb = Mb * (C0 * Gb - Dm * Gb) := h3
      _ = Mb + (Mb * SGG - Mb * (Dm * Gb)) := by rw [h2]; noncomm_ring
  have hpull1 : Mb * SGG = ∫ x, Mb * (coreS v L (G x) * G x) ∂μ :=
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Mb).integral_comp_comm
      hSi).symm
  have hpull2 : Mb * (Dm * Gb) = ∫ x, Mb * (Dm * G x) ∂μ := by
    have e1 : Dm * Gb = ∫ x, Dm * G x ∂μ :=
      ((ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Dm).integral_comp_comm
        hGi).symm
    rw [e1]
    exact ((ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      Mb).integral_comp_comm (hGi.const_mul Dm)).symm
  have hI1 : Integrable (fun x => Mb * (coreS v L (G x) * G x)) μ := hSi.const_mul Mb
  have hI2 : Integrable (fun x => Mb * (Dm * G x)) μ := (hGi.const_mul Dm).const_mul Mb
  have hsub : Mb * SGG - Mb * (Dm * Gb) =
      ∫ x, (Mb * (coreS v L (G x) * G x) - Mb * (Dm * G x)) ∂μ := by
    rw [hpull1, hpull2, integral_sub hI1 hI2]
  have hm : m j = blockTrace Gb j := by
    rw [hmdef, rlMean, ← rlTrCLM_apply, ← (rlTrCLM W j).integral_comp_comm hGi]
    rfl
  have hI3 : Integrable (fun x => Mb * (coreS v L (G x) * G x) - Mb * (Dm * G x)) μ :=
    hI1.sub hI2
  rw [hm, hkey, ← rlTrCLM_apply, map_add, hsub,
    ← (rlTrCLM W j).integral_comp_comm hI3, rlTrCLM_apply]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [rlTrCLM_apply]
  congr 1
  have hds : ∀ u w : Fin 2 × Fin W → ℂ, (diagonal (u - w) : Matrix (Fin 2 × Fin W) _ ℂ) =
      diagonal u - diagonal w := fun u w => (diagonal_sub u w).symm
  rw [rlS_eq hW hα hβ, ← cmpExt_sub, hds, ← hDm]
  noncomm_ring

end Mean

/-!
## 8. The residual of the mean equation
-/

section Resid

variable {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}

theorem rl_memLp_F (hW : 0 < W) (hs : 0 < s) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : ℝ≥0∞) :
    MemLp (rlF b E s X D) q (gaussianProduct (rlVar W b s)) :=
  MemLp.of_bound (rl_measurable_F b E s X D).aestronglyMeasurable (2 * (‖D‖ * (s * y)⁻¹))
    (ae_of_all _ fun x => rl_norm_F_le hW D (fun x => rl_norm_G_le b E hs hX hy hya x) x)

theorem rl_integrable_FF (hW : 0 < W) (hs : 0 < s) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (D₁ D₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (c : ℂ) :
    Integrable (fun x => rlF b E s X D₁ x * (rlF b E s X D₂ x - c))
      (gaussianProduct (rlVar W b s)) :=
  (rl_memLp_F hW hs hX hy hya D₁ 2).integrable_mul
    ((rl_memLp_F hW hs hX hy hya D₂ 2).sub (memLp_const c))

/-- **Covariance of two normalized traces** from their `L²` fluctuations. -/
theorem rl_cov (hW : 0 < W) (hs : 0 < s) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (D₁ D₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {A₁ A₂ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h₁ : eLpNorm (fun x => rlF b E s X D₁ x - ∫ x', rlF b E s X D₁ x' ∂gaussianProduct (rlVar W b s))
      2 (gaussianProduct (rlVar W b s)) ≤ ENNReal.ofReal A₁)
    (h₂ : eLpNorm (fun x => rlF b E s X D₂ x - ∫ x', rlF b E s X D₂ x' ∂gaussianProduct (rlVar W b s))
      2 (gaussianProduct (rlVar W b s)) ≤ ENNReal.ofReal A₂) :
    ‖∫ x, rlF b E s X D₁ x * (rlF b E s X D₂ x -
        ∫ x', rlF b E s X D₂ x' ∂gaussianProduct (rlVar W b s)) ∂gaussianProduct (rlVar W b s)‖ ≤
      A₁ * A₂ := by
  set μ := gaussianProduct (rlVar W b s)
  set f := rlF b E s X D₁
  set g := rlF b E s X D₂
  have hf := rl_memLp_F hW hs hX hy hya D₁ 2 (b := b)
  have hg := rl_memLp_F hW hs hX hy hya D₂ 2 (b := b)
  have hc := core_cov_le hf hg hA₁ hA₂ h₁ h₂
  have e : ∫ x, f x * (g x - ∫ x', g x' ∂μ) ∂μ = (∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
    have h1 : (fun x => f x * (g x - ∫ x', g x' ∂μ)) =
        fun x => f x * g x - f x * ∫ x', g x' ∂μ := by funext x; ring
    have i1 : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
    have i2 : Integrable (fun x => f x * ∫ x', g x' ∂μ) μ := (hf.integrable one_le_two).mul_const _
    rw [h1, integral_sub i1 i2, integral_mul_const]
  rw [e]
  exact hc

/-- The fluctuation scale `A(D) = Cg √2 (16 ‖D‖ / W) K²`. -/
def rlA (Cg : ℝ) (W : ℕ) (nD K : ℝ) : ℝ := Cg * Real.sqrt 2 * (16 * nD / W) * K ^ 2

theorem rl_fluct2 {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
    (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {nD : ℝ}
    (hnD : ‖D‖ ≤ nD) :
    eLpNorm (fun x => rlF b E s X D x - ∫ x', rlF b E s X D x' ∂gaussianProduct (rlVar W b s))
      2 (gaussianProduct (rlVar W b s)) ≤ ENNReal.ofReal (rlA Cg W nD (s * y)⁻¹) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h := rl_fluct hCg hgr hW hs hα hβ hα1 hβ1 hX hy hya D (p := 2) one_le_two
  rw [show ENNReal.ofReal 2 = 2 by norm_num] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold rlA
  gcongr

/-- **The residual of the mean equation**: `|e_j| ≤ 2 (α + β) A(K) A(1)`. -/
theorem rl_resid_bound {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
    (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1) (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (j : Fin 2) :
    ‖rlMean b E s X j - blockTrace (cmpInv (cmpTopH E X)
        (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (rlMean b E s X))) j‖ ≤
      2 * (rlAlpha b s + rlBeta b s) *
        (rlA Cg W (s * y)⁻¹ (s * y)⁻¹ * rlA Cg W 1 (s * y)⁻¹) := by
  set μ := gaussianProduct (rlVar W b s) with hμ
  set G := rlG b E s X with hGdef
  set m := rlMean b E s X with hmdef
  set α := rlAlpha b s
  set β := rlBeta b s
  set K := (s * y)⁻¹ with hK
  set Mb := cmpInv (cmpTopH E X) (rlShift s α β (matchedA E) m) with hMb
  have hK0 : 0 < K := by positivity
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  -- the norm of `M̄`
  have hMbK : ‖Mb‖ ≤ K := by
    rw [hMb, cmpInv]
    refine lct_norm_shifted_inv_le _ (cmpTopH_isHermitian E hX) _ (by positivity) fun p => ?_
    have h := rlShift_im s α β (matchedA E) m p.1
    have h1 := rl_mean_im_nonpos (b := b) hs hX hy hya p.1
    have h2 := rl_mean_im_nonpos (b := b) hs hX hy hya (1 - p.1)
    simp only [cmpExt]
    have := mul_le_mul_of_nonneg_left hya hs.le
    nlinarith [mul_nonneg hα (neg_nonneg.mpr h1), mul_nonneg hβ (neg_nonneg.mpr h2)]
  -- the two families of normalized traces
  set f : Fin 2 → (RlCoord W → ℝ) → ℂ := fun k => rlF b E s X (rlProj k) with hf
  set h : Fin 2 → (RlCoord W → ℝ) → ℂ := fun k => rlF b E s X (rlProj j * Mb * rlProj k) with hh
  have hfg : ∀ k x, blockTrace (G x) k = f k x := fun k x => by
    rw [rl_blockTrace_proj]; rfl
  have hmf : ∀ k, m k = ∫ x, f k x ∂μ := fun k => by
    rw [hmdef, rlMean]
    exact integral_congr_ae (ae_of_all _ fun x => hfg k x)
  have hpair : ∀ k x, cmpPair Mb (G x) j k = h k x := fun k x => by
    rw [rl_cmpPair_proj]; rfl
  -- fluctuations
  set Ag := rlA Cg W 1 K with hAg
  set Ah := rlA Cg W K K with hAh
  have hAg0 : 0 ≤ Ag := by rw [hAg, rlA]; positivity
  have hAh0 : 0 ≤ Ah := by rw [hAh, rlA]; positivity
  have hflf : ∀ k, eLpNorm (fun x => f k x - ∫ x', f k x' ∂μ) 2 μ ≤ ENNReal.ofReal Ag :=
    fun k => rl_fluct2 hCg hgr hW hs hα hβ hα1 hβ1 hX hy hya _ (rl_norm_proj_le k)
  have hflh : ∀ k, eLpNorm (fun x => h k x - ∫ x', h k x' ∂μ) 2 μ ≤ ENNReal.ofReal Ah := by
    intro k
    refine rl_fluct2 hCg hgr hW hs hα hβ hα1 hβ1 hX hy hya _ ?_
    calc ‖rlProj j * Mb * rlProj k‖ ≤ ‖rlProj j * Mb‖ * ‖(rlProj k : Matrix (Fin 2 × Fin W) _ ℂ)‖ :=
          norm_mul_le _ _
      _ ≤ (‖(rlProj j : Matrix (Fin 2 × Fin W) _ ℂ)‖ * ‖Mb‖) * 1 :=
          mul_le_mul (norm_mul_le _ _) (rl_norm_proj_le k) (norm_nonneg _) (by positivity)
      _ ≤ (1 * K) * 1 := by gcongr; exact rl_norm_proj_le j
      _ = K := by ring
  have hcov : ∀ k l, ‖∫ x, h k x * (f l x - m l) ∂μ‖ ≤ Ah * Ag := fun k l => by
    rw [hmf l]
    exact rl_cov hW hs hX hy hya _ _ hAh0 hAg0 (hflh k) (hflf l)
  have hint : ∀ k l, Integrable (fun x => h k x * (f l x - m l)) μ := fun k l =>
    rl_integrable_FF hW hs hX hy hya _ _ _
  -- the identity
  have hid := rl_mean_identity hW hs hα hβ hX hy hya j (b := b)
  rw [← hmdef] at hid
  have hpt : ∀ x, blockTrace (Mb * diagonal (cmpExt (rlPhi α β (fun k => blockTrace (G x) k) -
      rlPhi α β m)) * G x) j =
      (α : ℂ) * (h 0 x * (f 0 x - m 0)) + (β : ℂ) * (h 0 x * (f 1 x - m 1)) +
        ((α : ℂ) * (h 1 x * (f 1 x - m 1)) + (β : ℂ) * (h 1 x * (f 0 x - m 0))) := fun x => by
    rw [cmp_blockTrace_mul_diag_mul, Fin.sum_univ_two, hpair, hpair]
    simp only [rlPhi, Pi.sub_apply, hfg]
    have e0 : (1 : Fin 2) - 0 = 1 := rfl
    have e1 : (1 : Fin 2) - 1 = 0 := rfl
    rw [e0, e1]
    ring
  have hres : rlMean b E s X j - blockTrace Mb j =
      (α : ℂ) * ∫ x, h 0 x * (f 0 x - m 0) ∂μ + (β : ℂ) * ∫ x, h 0 x * (f 1 x - m 1) ∂μ +
        ((α : ℂ) * ∫ x, h 1 x * (f 1 x - m 1) ∂μ + (β : ℂ) * ∫ x, h 1 x * (f 0 x - m 0) ∂μ) := by
    have i1 : Integrable (fun x => (α : ℂ) * (h 0 x * (f 0 x - m 0))) μ := (hint 0 0).const_mul _
    have i2 : Integrable (fun x => (β : ℂ) * (h 0 x * (f 1 x - m 1))) μ := (hint 0 1).const_mul _
    have i3 : Integrable (fun x => (α : ℂ) * (h 1 x * (f 1 x - m 1))) μ := (hint 1 1).const_mul _
    have i4 : Integrable (fun x => (β : ℂ) * (h 1 x * (f 0 x - m 0))) μ := (hint 1 0).const_mul _
    have i12 : Integrable (fun x => (α : ℂ) * (h 0 x * (f 0 x - m 0)) +
      (β : ℂ) * (h 0 x * (f 1 x - m 1))) μ := i1.add i2
    have i34 : Integrable (fun x => (α : ℂ) * (h 1 x * (f 1 x - m 1)) +
      (β : ℂ) * (h 1 x * (f 0 x - m 0))) μ := i3.add i4
    rw [← hmdef, hid, add_sub_cancel_left, integral_congr_ae (ae_of_all _ hpt),
      integral_add i12 i34, integral_add i1 i2, integral_add i3 i4,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hres]
  have hn : ∀ (r : ℝ) (z : ℂ), 0 ≤ r → ‖z‖ ≤ Ah * Ag → ‖(r : ℂ) * z‖ ≤ r * (Ah * Ag) :=
    fun r z hr hz => by rw [cmp_norm_real_mul hr]; exact mul_le_mul_of_nonneg_left hz hr
  have t1 := hn α _ hα (hcov 0 0)
  have t2 := hn β _ hβ (hcov 0 1)
  have t3 := hn α _ hα (hcov 1 1)
  have t4 := hn β _ hβ (hcov 1 0)
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
  have e : 2 * (α + β) * (Ah * Ag) =
      α * (Ah * Ag) + β * (Ah * Ag) + (α * (Ah * Ag) + β * (Ah * Ag)) := by ring
  rw [e]
  gcongr

end Resid

end BlockBand.Layers
