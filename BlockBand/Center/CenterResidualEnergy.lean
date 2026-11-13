module

public import BlockBand.Center.DysonCenterFamily

/-!
# The residual energy derivative of the center and its regularity

* **`FullEnergyTraceBound`** (the definition; the bound is proved from `ConditionalBlockGUECount`
  and `GaussianLpGradient` as `fullEnergyTraceBound_holds`):
  `sup_{E ∈ I} max_k ‖ε'_{e,k}(E)‖_{L^q} ≤ C_q n/√W`, with `ε'` the
  Lean `deriv` in `E`, under the law of the extension (the residual `H^{(e)} = H - G_e` of
  the edge splitting).
* Deterministic regularity: on the bond-regular set (`CsmBondGood`: banded ring matrix with
  invertible bond blocks `H_{j,j+1}`), no eigenvector of `H` vanishes on the pair
  (`csm_unique_continuation`), hence the full matrix `H^{(e)} - E - ζ P_S` is invertible for
  every real `E` and `Im ζ > 0` (`csm_ctrFull_det_ne_zero`), and `E ↦ ε_{e,k}(E)` is
  differentiable on `(-2, 2)` (`csm_differentiableAt_eps`).
* `csm_ae_det_ginibre_ne_zero`, `csm_ae_bondGood`: the bond-regular set has full physical
  probability (Ginibre bonds are a.s. invertible: the determinant is a nonzero polynomial in
  the real Gaussian coordinates).
* `csmDeriv`: a jointly Borel version of `∂_E ε_{e,k}` (limit of difference quotients), equal
  to `deriv` wherever `ε_{e,k}` is differentiable.
* On an extension carrying the edge splitting: `csm_ae_good` (`H`, `H^{(e)}` Hermitian, `H`
  bond-regular a.s.), `csm_isPairSplitting` (the split state of `H^{(e)}` is a pair splitting
  law at `s = min(c,b)`, so `residualPair` applies to it), `csm_ae_det_ext`
  (no exterior pole at a deterministic energy, via `rsl_splitting_unique` and the a.s.
  invertibility of the Gaussian path).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. The residual trace `ε_{e,k}` and the obligation `FullEnergyTraceBound`
-/

section Eps

variable (p : Parameters) (i : ZMod p.n)

/-- `ε_{e,k}(E) = W⁻¹ Tr P_k ℛ_e(s ā(E)) - ā(E)` (as in the tagged trace lemma, `μ = ā`, `s = min(c,b)`;
`ℛ_e` the full compressed inverse, equal to `R_e⁰ = (K_e - sμ)⁻¹` off the exterior poles). -/
def csmEps (Hres : p.SiteMatrix) (k : ZMod p.n) (E : ℝ) : ℂ :=
  pairBlockTrace p i (compressedResolvent p i Hres E ((splitS p : ℂ) * conj (matchedA E))) k -
    conj (matchedA E)

end Eps

/-- **The full energy trace bound** of the tagged trace lemma, used in the domain clause of
the physical center theorem. It is a definition here, not a theorem.

Statement. `b ∈ (0, 1/2)`, the interval `I = bulkInterval κ` (`κ > 0`), `T` and the moment
order `q ≥ 1` are fixed first; then there are `C_q` and `W₀`; for every parameter set with
`p.b = b`, `n ≤ TW` (and `n ≥ 4`, built into `Parameters`), `W > W₀`, every model, adjacent
pair `S_e = {i, i+1}`, extension `X` carrying the edge splitting `G` (`IsCenterSplitting`:
`G = G_e ~ GUE_{2W}(s/(2W))` independent of `H^{(e)} = H - G_e`, `H = X.Hm` with the exact
physical law), every deterministic `E ∈ I` and both blocks `k ∈ {i, i+1}`:
`‖∂_E ε_{e,k}(E)‖_{L^q(X.P)} ≤ C_q n / √W`, where
`ε_{e,k}(E) = W⁻¹ Tr P_k ℛ_e(E, s ā(E)) - ā(E)` is built from `H^{(e)}` (`csmEps`, written out
below) and `∂_E` is Lean's `deriv` in `E` (the full energy derivative, including the
`E`-dependence of `μ = ā(E)` and of the spectral parameter `s μ`).

Law: `X.P` (equivalently the physical law of `H`, the residual being `H - G_e`). The supremum
over `E` is outside the moment (deterministic energies). Compared with the paper, the moment
order is restricted to `q ≥ 1` and a width threshold `W₀` is allowed; both weaken the
statement. -/
def FullEnergyTraceBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq W₀ : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (X : PairExtension p model)
        (G : X.Ω → PairMatrix p i), IsCenterSplitting X G →
      ∀ E ∈ bulkInterval κ, ∀ k : ZMod p.n, (k = i ∨ k = i + 1) →
        eLpNorm (fun ω => deriv (fun E' : ℝ =>
            pairBlockTrace p i (compressedResolvent p i (X.Hm ω - embedPair p i (G ω)) E'
              ((splitS p : ℂ) * conj (matchedA E'))) k - conj (matchedA E')) E)
          (ENNReal.ofReal q) X.P ≤
        ENNReal.ofReal (Cq * p.n / Real.sqrt p.W)

/-!
## 2. Bond regularity and unique continuation
-/

section Bonds

variable {p : Parameters}

/-- The bond block `B_j = H_{j, j+1}`. -/
def csmBond (H : p.SiteMatrix) (j : ZMod p.n) : Matrix (Fin p.W) (Fin p.W) ℂ :=
  Matrix.of fun a c => H (j, a) (j + 1, c)

/-- The bond-regular set: a banded ring matrix whose bond blocks are all invertible. -/
def CsmBondGood (H : p.SiteMatrix) : Prop :=
  IsRingBanded p H ∧ ∀ j : ZMod p.n, (csmBond H j).det ≠ 0

/-- **Unique continuation along the ring**: on the bond-regular set, an eigenvector vanishing on
the pair `{i, i+1}` is zero. -/
theorem csm_unique_continuation {H : p.SiteMatrix} (hH : CsmBondGood H) (i : ZMod p.n)
    (v : p.Site → ℂ) (E : ℂ) (hS : ∀ x : p.Site, (x.1 = i ∨ x.1 = i + 1) → v x = 0)
    (hv : H *ᵥ v = E • v) : v = 0 := by
  have key : ∀ m : ℕ, (∀ a, v (i + m, a) = 0) ∧ (∀ a, v (i + m + 1, a) = 0) := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      exact ⟨fun a => hS _ (Or.inl rfl), fun a => hS _ (Or.inr rfl)⟩
    | succ m ih =>
      set j : ZMod p.n := i + m + 1 with hj
      have hcast : i + ((m + 1 : ℕ) : ZMod p.n) = j := by push_cast; ring
      rw [hcast]
      refine ⟨ih.2, ?_⟩
      have hjm : j - 1 = i + m := by rw [hj]; ring
      have hrow : ∀ a, (csmBond H j *ᵥ fun c => v (j + 1, c)) a = 0 := by
        intro a
        have h1 : (H *ᵥ v) (j, a) = 0 := by
          rw [hv, Pi.smul_apply, ih.2 a, smul_zero]
        rw [← h1, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single (j + 1)]
        · rfl
        · intro b _ hb
          refine Finset.sum_eq_zero fun c _ => ?_
          by_cases hbj : b = j
          · rw [hbj, ih.2 c, mul_zero]
          · by_cases hbm : b = j - 1
            · rw [hbm, hjm, ih.1 c, mul_zero]
            · rw [hH.1 (j, a) (b, c) (by
                rintro (h | h | h)
                · exact hbj h
                · exact hb h
                · exact hbm h), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h0 := Matrix.eq_zero_of_mulVec_eq_zero (hH.2 j) (funext hrow)
      intro a
      exact congrFun h0 a
  funext x
  have hx : i + (((x.1 - i).val : ℕ) : ZMod p.n) = x.1 := by
    rw [ZMod.natCast_zmod_val]; ring
  have := (key (x.1 - i).val).1 x.2
  rw [hx] at this
  exact this

/-- `embedPair G` annihilates vectors vanishing on the pair. -/
theorem csm_embedPair_mulVec {i : ZMod p.n} (G : PairMatrix p i) (v : p.Site → ℂ)
    (hS : ∀ x : p.Site, (x.1 = i ∨ x.1 = i + 1) → v x = 0) : embedPair p i G *ᵥ v = 0 := by
  funext x
  rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : y.1 = i ∨ y.1 = i + 1
  · rw [hS y hy, mul_zero]
  · have : embedPair p i G x y = 0 := by
      unfold embedPair
      split_ifs <;> rfl
    rw [this, zero_mul]

/-- **Invertibility of the full matrix**: for `H^{(e)} = H - G_e` Hermitian with `H` bond-regular,
`H^{(e)} - E - ζ P_S` is invertible for every real `E` and `Im ζ > 0`. -/
theorem csm_ctrFull_det_ne_zero {i : ZMod p.n} {H : p.SiteMatrix} (hH : CsmBondGood H)
    (G : PairMatrix p i) (hherm : (H - embedPair p i G).IsHermitian) (E : ℝ) {ζ : ℂ}
    (hζ : 0 < ζ.im) : (ctrFull p i (H - embedPair p i G) E ζ).det ≠ 0 := by
  set Hres := H - embedPair p i G with hHres
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  set d : p.Site → ℂ := fun x => if x.1 = i ∨ x.1 = i + 1 then 1 else 0 with hd
  have hP : pairProjector p i *ᵥ v = fun x => d x * v x := by
    unfold pairProjector
    funext x
    exact Matrix.mulVec_diagonal _ _ _
  have hfull : ctrFull p i Hres E ζ *ᵥ v =
      Hres *ᵥ v - (E : ℂ) • v - ζ • (pairProjector p i *ᵥ v) := by
    unfold ctrFull
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hq := congrArg (fun w => (star v ⬝ᵥ w).im) hv
  simp only [hfull, dotProduct_zero, Complex.zero_im] at hq
  rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, hP] at hq
  have hA : (star v ⬝ᵥ Hres *ᵥ v).im = 0 := by
    have := hherm.star_dotProduct_mulVec_comm v v
    have h2 := congrArg Complex.im this
    rw [Complex.star_def, Complex.conj_im] at h2
    linarith
  have hN : (star v ⬝ᵥ v).im = 0 := by
    simp only [dotProduct, Pi.star_apply, Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj]; rfl
  set s : ℝ := ∑ x, (if x.1 = i ∨ x.1 = i + 1 then Complex.normSq (v x) else 0) with hs
  have hD : (star v ⬝ᵥ fun x => d x * v x) = (s : ℂ) := by
    simp only [dotProduct, Pi.star_apply, hs, Complex.ofReal_sum, hd]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · rw [one_mul, Complex.star_def, mul_comm, Complex.mul_conj]
    · simp
  rw [hD, Complex.sub_im, Complex.sub_im, hA, smul_eq_mul, smul_eq_mul, Complex.mul_im,
    Complex.mul_im, hN] at hq
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_sub,
    sub_zero] at hq
  have hs0 : s = 0 := by
    have hq' : ζ.im * s = 0 := by linarith
    rcases mul_eq_zero.mp hq' with h | h
    · exact absurd h hζ.ne'
    · exact h
  have hvS : ∀ x : p.Site, (x.1 = i ∨ x.1 = i + 1) → v x = 0 := by
    intro x hx
    have hx0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl)).mp hs0 x (Finset.mem_univ _)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hx)] at hx0
    exact Complex.normSq_eq_zero.mp hx0
  have hPv : pairProjector p i *ᵥ v = 0 := by
    rw [hP]
    funext x
    by_cases hx : x.1 = i ∨ x.1 = i + 1
    · rw [hvS x hx, mul_zero]; rfl
    · simp [hd, hx]
  have hres : Hres *ᵥ v = (E : ℂ) • v := by
    have := hfull
    rw [hv, hPv, smul_zero, sub_zero] at this
    exact (sub_eq_zero.mp this.symm)
  have hHv : H *ᵥ v = (E : ℂ) • v := by
    have : H = Hres + embedPair p i G := by rw [hHres]; abel
    rw [this, Matrix.add_mulVec, hres, csm_embedPair_mulVec G v hvS, add_zero]
  exact hv0 (csm_unique_continuation hH i v E hvS hHv)

end Bonds

/-!
## 3. The bond-regular set has full physical probability
-/

section BondLaw

/-- **Ginibre blocks are a.s. invertible** (`t > 0`): `det B` is a nonzero polynomial in the
real Gaussian coordinates (it is `1` at the identity), whose zero set is Lebesgue-null. -/
theorem csm_ae_det_ginibre_ne_zero (W : ℕ) {t : ℝ≥0} (ht : t ≠ 0) :
    ∀ᵐ B ∂ginibreMeasure (Fin W) (Fin W) t, B.det ≠ 0 := by
  let P : Matrix (Fin W) (Fin W) (MvPolynomial (Fin W × Fin W × Fin 2) ℂ) :=
    fun x y => MvPolynomial.X (x, y, 0) + MvPolynomial.X (x, y, 1) * MvPolynomial.C Complex.I
  have hev : ∀ r : Fin W × Fin W × Fin 2 → ℝ,
      MvPolynomial.eval (fun j => (r j : ℂ)) P.det =
        (BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r).det := by
    intro r
    rw [RingHom.map_det]
    congr 1
    ext x y
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp [P, BlockBand.Layers.ginibreAssemble]
  set Q := BlockBand.Parameters.mvPolynomialNormSq P.det
  have hQx : ∀ r, MvPolynomial.eval r Q =
      Complex.normSq (BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r).det := by
    intro r
    rw [BlockBand.Parameters.eval_mvPolynomialNormSq, hev]
  have hQ : Q ≠ 0 := by
    intro h0
    let r₀ : Fin W × Fin W × Fin 2 → ℝ := fun j => if j.1 = j.2.1 ∧ j.2.2 = 0 then 1 else 0
    have hr₀ : BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r₀ = 1 := by
      ext x y
      by_cases h : x = y
      · subst h; simp [BlockBand.Layers.ginibreAssemble, r₀]
      · simp [BlockBand.Layers.ginibreAssemble, r₀, h, Matrix.one_apply_ne h]
    have h := hQx r₀
    rw [h0, map_zero, hr₀, Matrix.det_one, Complex.normSq_one] at h
    exact zero_ne_one h
  have hnull := BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype Q hQ
  have ht2 : t / 2 ≠ 0 := by
    intro h; apply ht
    have := congrArg (fun u : ℝ≥0 => u * 2) h
    simpa using this
  have hac := BlockBand.Parameters.pi_absolutelyContinuous_volume
    (fun _ : Fin W × Fin W × Fin 2 => gaussianReal 0 (t / 2))
    (fun _ => gaussianReal_absolutelyContinuous 0 ht2)
  have hmeasS : MeasurableSet {B : Matrix (Fin W) (Fin W) ℂ | B.det = 0} :=
    measurableSet_eq_fun (continuous_id.matrix_det).measurable measurable_const
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [BlockBand.Layers.ginibreMeasure_eq_map, Measure.map_apply
    BlockBand.Layers.measurable_ginibreAssemble hmeasS]
  apply hac
  convert hnull using 2
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hQx, Complex.normSq_eq_zero]

variable {p : Parameters}

theorem csm_measurableSet_bondGood : MeasurableSet {H : p.SiteMatrix | CsmBondGood H} := by
  have h1 : MeasurableSet {H : p.SiteMatrix | IsRingBanded p H} := by
    have : {H : p.SiteMatrix | IsRingBanded p H} = ⋂ x : p.Site, ⋂ y : p.Site,
        {H : p.SiteMatrix | ¬ (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) → H x y = 0} := by
      ext H; simp [IsRingBanded]
    rw [this]
    refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
    by_cases hc : (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1)
    · have : {H : p.SiteMatrix | ¬ (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) → H x y = 0} =
          Set.univ := by
        ext H; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact fun h => absurd hc h
      rw [this]; exact MeasurableSet.univ
    · have : {H : p.SiteMatrix | ¬ (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) → H x y = 0} =
          {H : p.SiteMatrix | H x y = 0} := by
        ext H; simp only [Set.mem_ofPred_eq]; exact ⟨fun h => h hc, fun h _ => h⟩
      rw [this]
      exact measurableSet_eq_fun ((measurable_pi_apply y).comp (measurable_pi_apply x))
        measurable_const
  have h2 : ∀ j : ZMod p.n, MeasurableSet {H : p.SiteMatrix | (csmBond H j).det ≠ 0} := by
    intro j
    have hm : Measurable (fun H : p.SiteMatrix => (csmBond H j).det) := by
      refine (continuous_id.matrix_det).measurable.comp ?_
      refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun c => ?_
      exact BlockBand.Layers.pg_entry measurable_id _ _
    exact (measurableSet_eq_fun hm measurable_const).compl
  have : {H : p.SiteMatrix | CsmBondGood H} =
      {H : p.SiteMatrix | IsRingBanded p H} ∩ ⋂ j, {H : p.SiteMatrix | (csmBond H j).det ≠ 0} := by
    ext H; simp [CsmBondGood]
  rw [this]
  exact h1.inter (MeasurableSet.iInter h2)

/-- The assembled ring is banded with bond blocks `ω.2 j`. -/
theorem csm_bondGood_rngAssemble (ω : BlockBand.Layers.RngSample p)
    (hω : ∀ j, (ω.2 j).det ≠ 0) : CsmBondGood (BlockBand.Layers.rngAssemble p ω) := by
  refine ⟨fun x y hxy => ?_, fun j => ?_⟩
  · refine BlockBand.Layers.rngAssemble_far ω x y (fun h => hxy (Or.inl h.symm))
      (fun h => hxy (Or.inr (Or.inl h))) (fun h => hxy (Or.inr (Or.inr ?_)))
    rw [h]; ring
  · have : csmBond (BlockBand.Layers.rngAssemble p ω) j = ω.2 j := by
      ext a c
      exact BlockBand.Layers.rngAssemble_succ ω j a c
    rw [this]
    exact hω j

/-- **The bond-regular set has full physical probability.** -/
theorem csm_ae_bondGood (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), CsmBondGood H := by
  rw [BlockBand.Layers.rng_law_eq_map model,
    ae_map_iff BlockBand.Layers.rng_measurable_assemble.aemeasurable csm_measurableSet_bondGood]
  have hb : Real.toNNReal (p.b / p.W) ≠ 0 := by
    have : (0 : ℝ) < p.b / p.W := div_pos p.b_pos (by exact_mod_cast p.W_pos)
    exact (Real.toNNReal_pos.mpr this).ne'
  have hbonds : ∀ᵐ ω ∂BlockBand.Layers.rngLaw p, ∀ j, (ω.2 j).det ≠ 0 := by
    have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure p.W t
    refine Filter.eventually_all.mpr fun j => ?_
    have h := ((measurePreserving_eval (fun _ : ZMod p.n =>
        ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W))) j).comp
      (measurePreserving_snd (μ := Measure.pi fun _ : ZMod p.n =>
        gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W)))
        (ν := Measure.pi fun _ : ZMod p.n =>
          ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W)))))
    exact h.quasiMeasurePreserving.ae (csm_ae_det_ginibre_ne_zero p.W hb)
  filter_upwards [hbonds] with ω hω
  exact csm_bondGood_rngAssemble ω hω

end BondLaw

/-!
## 4. Differentiability of `ε_{e,k}` in the energy
-/

section Deriv

theorem csm_differentiableAt_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ℝ → Matrix ι ι ℂ)
    {E₀ : ℝ} (hM : ∀ a b, DifferentiableAt ℝ (fun E => M E a b) E₀) :
    DifferentiableAt ℝ (fun E => (M E).det) E₀ := by
  simp only [Matrix.det_apply]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (DifferentiableAt.fun_finsetProd fun j _ => hM _ _).const_mul _

theorem csm_differentiableAt_inv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℂ) {E₀ : ℝ} (hM : ∀ a b, DifferentiableAt ℝ (fun E => M E a b) E₀)
    (hdet : (M E₀).det ≠ 0) (x y : ι) : DifferentiableAt ℝ (fun E => (M E)⁻¹ x y) E₀ := by
  have h : (fun E => (M E)⁻¹ x y) =
      fun E => ((M E).det)⁻¹ * ((M E).updateRow y (Pi.single x 1)).det := by
    funext E
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
      Matrix.adjugate_apply]
  rw [h]
  refine ((csm_differentiableAt_det M hM).fun_inv hdet).mul (csm_differentiableAt_det _ ?_)
  intro a b
  simp only [Matrix.updateRow_apply]
  by_cases hab : a = y
  · simp only [hab, ↓reduceIte]
    exact differentiableAt_const _
  · simp only [hab, ↓reduceIte]
    exact hM a b

theorem csm_conj_matchedA_eq (E : ℝ) :
    conj (matchedA E) = ((-E / 2 : ℝ) : ℂ) + ((Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [matchedA]
  · simp [matchedA]; ring

theorem csm_conj_matchedA_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (conj (matchedA E)).im := by
  rw [csm_conj_matchedA_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  have h4 : 0 < 4 - E ^ 2 := by
    have := abs_lt.mp hE
    nlinarith
  have := Real.sqrt_pos.mpr h4
  linarith

theorem csm_differentiableAt_ofReal (E₀ : ℝ) : DifferentiableAt ℝ (fun E : ℝ => (E : ℂ)) E₀ :=
  (hasDerivAt_id E₀).ofReal_comp.differentiableAt

theorem csm_differentiableAt_conj_matchedA {E₀ : ℝ} (hE : |E₀| < 2) :
    DifferentiableAt ℝ (fun E => conj (matchedA E)) E₀ := by
  have h : (fun E => conj (matchedA E)) = fun E : ℝ =>
      ((-E / 2 : ℝ) : ℂ) + ((Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I :=
    funext csm_conj_matchedA_eq
  rw [h]
  have h4 : 4 - E₀ ^ 2 ≠ 0 := by
    have := abs_lt.mp hE
    nlinarith
  have h1 : DifferentiableAt ℝ (fun E : ℝ => -E / 2) E₀ := by fun_prop
  have h2 : DifferentiableAt ℝ (fun E : ℝ => Real.sqrt (4 - E ^ 2) / 2) E₀ :=
    ((DifferentiableAt.sqrt (f := fun E : ℝ => 4 - E ^ 2) (by fun_prop) h4).div_const 2)
  exact (h1.hasDerivAt.ofReal_comp.differentiableAt).add
    ((h2.hasDerivAt.ofReal_comp.differentiableAt).mul_const _)

variable {p : Parameters} {i : ZMod p.n}

/-- **`ε_{e,k}` is differentiable** at every `E` in `(-2, 2)` where the full matrix is
invertible. -/
theorem csm_differentiableAt_eps {Hres : p.SiteMatrix} (k : ZMod p.n) {E₀ : ℝ} (hE : |E₀| < 2)
    (hdet : (ctrFull p i Hres E₀ ((splitS p : ℂ) * conj (matchedA E₀))).det ≠ 0) :
    DifferentiableAt ℝ (csmEps p i Hres k) E₀ := by
  have hμ := csm_differentiableAt_conj_matchedA hE
  have hEc := csm_differentiableAt_ofReal E₀
  have hM : ∀ a b, DifferentiableAt ℝ
      (fun E => ctrFull p i Hres E ((splitS p : ℂ) * conj (matchedA E)) a b) E₀ := by
    intro a b
    simp only [ctrFull, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((differentiableAt_const _).sub (hEc.mul_const _)).sub
      (((differentiableAt_const _).mul hμ).mul_const _)
  unfold csmEps pairBlockTrace
  refine DifferentiableAt.sub ?_ hμ
  refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun x _ => ?_) _
  by_cases hx : x.1.1 = k
  · simp only [hx, ↓reduceIte]
    exact csm_differentiableAt_inv_apply _ hM hdet x.1 x.1
  · simp only [hx, ↓reduceIte]
    exact differentiableAt_const _

variable (p i) in
/-- A jointly Borel version of `∂_E ε_{e,k}`: the limit of the difference quotients at
`E + 1/(n+1)` (Lean's `limUnder`, junk where there is no limit). -/
def csmDeriv (Hres : p.SiteMatrix) (k : ZMod p.n) (E : ℝ) : ℂ :=
  limUnder atTop (fun n : ℕ => slope (csmEps p i Hres k) E (E + 1 / ((n : ℝ) + 1)))

theorem csm_tendsto_slope {f : ℝ → ℂ} {E : ℝ} (hf : DifferentiableAt ℝ f E) :
    Tendsto (fun n : ℕ => slope f E (E + 1 / ((n : ℝ) + 1))) atTop (𝓝 (deriv f E)) := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hf.hasDerivAt
  refine h1.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩)
  · have := (tendsto_const_nhds (x := E)).add (tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa using this
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    intro h
    linarith

theorem csm_csmDeriv_eq {Hres : p.SiteMatrix} {k : ZMod p.n} {E : ℝ}
    (hf : DifferentiableAt ℝ (csmEps p i Hres k) E) :
    csmDeriv p i Hres k E = deriv (csmEps p i Hres k) E :=
  (csm_tendsto_slope hf).limUnder_eq

variable (i) in
theorem csm_measurable_eps (k : ZMod p.n) :
    Measurable (fun x : p.SiteMatrix × ℝ => csmEps p i x.1 k x.2) := by
  have hμ : Continuous (fun x : p.SiteMatrix × ℝ => conj (matchedA x.2)) :=
    Complex.continuous_conj.comp (ctr_continuous_matchedA.comp continuous_snd)
  have harg : Measurable (fun x : p.SiteMatrix × ℝ =>
      (x, (splitS p : ℂ) * conj (matchedA x.2))) :=
    measurable_id.prodMk (continuous_const.mul hμ).measurable
  have hR : Measurable (fun x : p.SiteMatrix × ℝ =>
      compressedResolvent p i x.1 x.2 ((splitS p : ℂ) * conj (matchedA x.2))) :=
    Measurable.comp
      (g := fun y : (p.SiteMatrix × ℝ) × ℂ => compressedResolvent p i y.1.1 y.1.2 y.2)
      (f := fun x : p.SiteMatrix × ℝ => (x, (splitS p : ℂ) * conj (matchedA x.2)))
      ctr_measurable_compressed harg
  have hT : Measurable (fun x : p.SiteMatrix × ℝ => pairBlockTrace p i
      (compressedResolvent p i x.1 x.2 ((splitS p : ℂ) * conj (matchedA x.2))) k) :=
    Measurable.comp (g := fun M : PairMatrix p i => pairBlockTrace p i M k)
      (f := fun x : p.SiteMatrix × ℝ =>
        compressedResolvent p i x.1 x.2 ((splitS p : ℂ) * conj (matchedA x.2)))
      (ctr_continuous_pairBlockTrace k).measurable hR
  unfold csmEps
  exact hT.sub hμ.measurable

variable (i) in
theorem csm_measurable_csmDeriv (k : ZMod p.n) :
    Measurable (fun x : p.SiteMatrix × ℝ => csmDeriv p i x.1 k x.2) := by
  have hterm : ∀ n : ℕ, StronglyMeasurable (fun x : p.SiteMatrix × ℝ =>
      slope (csmEps p i x.1 k) x.2 (x.2 + 1 / ((n : ℝ) + 1))) := by
    intro n
    refine Measurable.stronglyMeasurable ?_
    simp only [slope_def_module]
    have h1 : Measurable (fun x : p.SiteMatrix × ℝ => csmEps p i x.1 k (x.2 + 1 / ((n : ℝ) + 1))) :=
      Measurable.comp (g := fun x : p.SiteMatrix × ℝ => csmEps p i x.1 k x.2)
        (f := fun x : p.SiteMatrix × ℝ => (x.1, x.2 + 1 / ((n : ℝ) + 1)))
        (csm_measurable_eps i k) (measurable_fst.prodMk (measurable_snd.add_const _))
    exact ((measurable_snd.add_const _).sub measurable_snd).inv.smul (h1.sub (csm_measurable_eps i k))
  exact (StronglyMeasurable.limUnder (l := atTop) hterm).measurable

end Deriv

/-!
## 5. The residual-pair observable and the center residual
-/

section Obs

variable {p : Parameters} {i : ZMod p.n}

theorem csm_pairBlockTrace_conjTranspose (N : PairMatrix p i) (k : ZMod p.n) :
    pairBlockTrace p i Nᴴ k = conj (pairBlockTrace p i N k) := by
  unfold pairBlockTrace
  rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Matrix.conjTranspose_apply, Complex.star_def]
  · rw [map_zero]

theorem csm_edgeSchur_isHermitian {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) :
    (edgeSchur p i Hres E).IsHermitian := by
  have h := ctr_edgeSchur_add_isHermitian (i := i) hH E
  have hE1 : ((E : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  have := h.sub hE1
  rwa [add_sub_cancel_right] at this

/-- **The anchor**: off the exterior poles, `|ε_{e,k}(E)|` is the residual-pair
observable `|W⁻¹ Tr P_k (K_e(E) - s a)⁻¹ - a|` at the split state of `H^{(e)}` (the conjugate
traces have the same modulus, `K_e` being Hermitian).
-/
theorem csm_norm_eps_eq_obs {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0) (k : ZMod p.n) :
    ‖csmEps p i Hres k E‖ =
      ‖pairBlockTrace p i ((pairResidual p i (BlockBand.Layers.rslUnassemble i Hres) E -
        ((splitS p : ℂ) * matchedA E) • 1)⁻¹) k - matchedA E‖ := by
  unfold csmEps
  rw [ctr_compressed_eq_schur hH hdet]
  have hK := csm_edgeSchur_isHermitian (i := i) hH E
  have hrel : edgeSchur p i Hres E - ((splitS p : ℂ) * conj (matchedA E)) • 1 =
      (pairResidual p i (BlockBand.Layers.rslUnassemble i Hres) E -
        ((splitS p : ℂ) * matchedA E) • 1)ᴴ := by
    change _ = (edgeSchur p i Hres E - ((splitS p : ℂ) * matchedA E) • 1)ᴴ
    rw [Matrix.conjTranspose_sub, hK.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, map_mul, Complex.conj_ofReal]
  rw [hrel, ← Matrix.conjTranspose_nonsing_inv, csm_pairBlockTrace_conjTranspose, ← map_sub,
    Complex.norm_conj]

theorem csm_centerResidual_le (Hres : p.SiteMatrix) (E : ℝ) :
    centerResidual p i Hres E ≤ ‖csmEps p i Hres i E‖ + ‖csmEps p i Hres (i + 1) E‖ := by
  change Real.sqrt (‖csmEps p i Hres i E‖ ^ 2 + ‖csmEps p i Hres (i + 1) E‖ ^ 2) ≤ _
  have ha := norm_nonneg (csmEps p i Hres i E)
  have hb := norm_nonneg (csmEps p i Hres (i + 1) E)
  rw [← Real.sqrt_sq (add_nonneg ha hb)]
  exact Real.sqrt_le_sqrt (by nlinarith)

end Obs

/-!
## 6. Almost-sure properties on an extension carrying the edge splitting
-/

section Extension

variable {p : Parameters} {model : p.GaussianRingModel} {i : ZMod p.n}

theorem csm_isProb_ext (X : PairExtension p model) : IsProbabilityMeasure X.P := by
  constructor
  have h := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) X.map_eq
  rw [Measure.map_apply X.measurable_Hm MeasurableSet.univ, Set.preimage_univ] at h
  rw [h, measure_univ]

theorem csm_measurable_res (X : PairExtension p model) {G : X.Ω → PairMatrix p i}
    (hG : Measurable G) : Measurable (fun ω => X.Hm ω - embedPair p i (G ω)) := by
  have hB : Measurable (fun ω => embedPair p i (G ω)) := (ctr_measurable_embedPair i).comp hG
  exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
    (BlockBand.Layers.pg_entry X.measurable_Hm x y).sub (BlockBand.Layers.pg_entry hB x y)

theorem csm_ae_ext_of_law (X : PairExtension p model) {q : p.SiteMatrix → Prop}
    (h : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), q H) : ∀ᵐ ω ∂X.P, q (X.Hm ω) := by
  have h' : ∀ᵐ H ∂(X.P.map X.Hm), q H := by rw [X.map_eq]; exact h
  exact ae_of_ae_map X.measurable_Hm.aemeasurable h'

/-- On an extension carrying the splitting: `H`, `G_e` and `H^{(e)}` are a.s. Hermitian and `H`
is a.s. bond-regular. -/
theorem csm_ae_good (X : PairExtension p model) {G : X.Ω → PairMatrix p i}
    (hG : IsCenterSplitting X G) :
    ∀ᵐ ω ∂X.P, (X.Hm ω).IsHermitian ∧ (X.Hm ω - embedPair p i (G ω)).IsHermitian ∧
      CsmBondGood (X.Hm ω) := by
  have h1 := csm_ae_ext_of_law X model.isPhysical.1
  have h2 := csm_ae_ext_of_law X (csm_ae_bondGood model)
  have hGl : ∀ᵐ g ∂(X.P.map G), (g : PairMatrix p i).IsHermitian := by
    rw [hG.2.1.map_eq]; exact ctr_ae_gue_isHermitian _
  have h3 := ae_of_ae_map hG.1.aemeasurable hGl
  filter_upwards [h1, h2, h3] with ω hH hB hGh
  refine ⟨hH, ?_, hB⟩
  change (_ - _)ᴴ = _
  rw [Matrix.conjTranspose_sub, hH.eq, ctr_embedPair_conjTranspose, hGh.eq]

theorem csm_assemble_unassemble {H : p.SiteMatrix} (hH : H.IsHermitian) (G : PairMatrix p i) :
    assemble p i (BlockBand.Layers.rslUnassemble i H) G = H + embedPair p i G := by
  rw [BlockBand.Layers.rsl_assemble_add, ctr_assemble_zero_left]
  congr 1
  ext x y
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1
  · exact (BlockBand.Layers.rsl_assemble_pp i _ 0 ⟨x, hx⟩ ⟨y, hy⟩).trans (by
      simp [BlockBand.Layers.rslUnassemble, pairBlock])
  · exact (BlockBand.Layers.rsl_assemble_pe i _ 0 ⟨x, hx⟩ ⟨y, hy⟩).trans (hH.apply x y)
  · exact BlockBand.Layers.rsl_assemble_ep i _ 0 ⟨x, hx⟩ ⟨y, hy⟩
  · exact BlockBand.Layers.rsl_assemble_ee i _ 0 ⟨x, hx⟩ ⟨y, hy⟩

/-- The law of the split state `(H_R, C, V)` of `H^{(e)}` on an extension. -/
def csmSplitLaw (X : PairExtension p model) (G : X.Ω → PairMatrix p i) :
    Measure (SplitState p i) :=
  X.P.map (fun ω => BlockBand.Layers.rslUnassemble i (X.Hm ω - embedPair p i (G ω)))

/-- **The split state of `H^{(e)}` is a splitting law** (at
`s = min(c,b)`), by the independence of `G_e` and `H^{(e)}`. -/
theorem csm_isPairSplitting (X : PairExtension p model) {G : X.Ω → PairMatrix p i}
    (hG : IsCenterSplitting X G) : IsPairSplitting p i model (splitS p) (csmSplitLaw X G) := by
  have := csm_isProb_ext X
  have hR := csm_measurable_res X hG.1
  have hS : Measurable (fun ω => BlockBand.Layers.rslUnassemble i (X.Hm ω - embedPair p i (G ω))) :=
    (BlockBand.Layers.rsl_measurable_unassemble i).comp hR
  have hind : IndepFun (fun ω => BlockBand.Layers.rslUnassemble i (X.Hm ω - embedPair p i (G ω)))
      G X.P :=
    hG.2.2.comp (BlockBand.Layers.rsl_measurable_unassemble i) measurable_id
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable hG.1.aemeasurable).mp hind
  unfold IsPairSplitting csmSplitLaw
  rw [← hG.2.1.map_eq, ← hprod, Measure.map_map (BlockBand.Layers.rsl_measurable_assemble i)
    (hS.prodMk hG.1), ← X.map_eq]
  apply Measure.map_congr
  filter_upwards [csm_ae_good X hG] with ω hω
  simp only [Function.comp_apply]
  rw [csm_assemble_unassemble hω.2.1, sub_add_cancel]

/-- **No exterior pole at a deterministic energy**: `det(H^{(e)}_R - E) ≠ 0` a.s. (the split law
is the residual-pair law, whose exterior is a Gaussian path). -/
theorem csm_ae_det_ext (X : PairExtension p model) {G : X.Ω → PairMatrix p i}
    (hG : IsCenterSplitting X G) (E : ℝ) :
    ∀ᵐ ω ∂X.P, (exteriorBlock p i (X.Hm ω - embedPair p i (G ω)) - (E : ℂ) • 1).det ≠ 0 := by
  have hsplit := csm_isPairSplitting X hG
  have hrsl := BlockBand.Layers.rsl_isPairSplitting i model ctr_splitS_pos.le (ctr_splitS_le_c p)
    (ctr_splitS_le_b p)
  have heq := BlockBand.Layers.rsl_splitting_unique i hsplit hrsl
  have hmeas : MeasurableSet {σ : SplitState p i | (σ.1 - (E : ℂ) • 1).det ≠ 0} := by
    have hfst : Measurable (fun σ : SplitState p i => σ.1) := measurable_fst
    have hdetm : Measurable (fun M : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ => M.det) :=
      (continuous_id.matrix_det).measurable
    have hm : Measurable (fun σ : SplitState p i => (σ.1 - (E : ℂ) • 1).det) :=
      hdetm.comp (measurable_pi_iff.mpr fun x =>
        measurable_pi_iff.mpr fun y => (BlockBand.Layers.pg_entry hfst x y).sub measurable_const)
    exact (measurableSet_eq_fun hm measurable_const).compl
  have hlaw : ∀ᵐ σ ∂csmSplitLaw X G, (σ.1 - (E : ℂ) • 1).det ≠ 0 := by
    rw [heq, ae_map_iff (BlockBand.Layers.rp_measurable_splitAssemble i).aemeasurable hmeas]
    have : IsProbabilityMeasure (pathLaw p.W (p.n - 2) p.b) :=
      BlockBand.Layers.pg_isProbabilityMeasure_pathLaw _ _ _
    have : IsProbabilityMeasure (BlockBand.Layers.rpLaw p.W p.b (splitS p)) :=
      BlockBand.Layers.rp_isProbabilityMeasure_rpLaw _ _ _
    have : SFinite (pathLaw p.W (p.n - 2) p.b) := inferInstance
    have : SFinite (BlockBand.Layers.rpLaw p.W p.b (splitS p)) := inferInstance
    have hpath := (Measure.quasiMeasurePreserving_snd
      (μ := BlockBand.Layers.rpLaw p.W p.b (splitS p))
      (ν := pathLaw p.W (p.n - 2) p.b)).ae
      (BlockBand.Layers.ae_isUnit_det_pathMatrix p.W (p.n - 2) p.b_lt_half E)
    filter_upwards [hpath] with x hx
    have h1 : (BlockBand.Layers.rpSplitAssemble i x).1 - (E : ℂ) • 1 =
        (pathMatrix x.2 - (E : ℂ) • 1).submatrix (BlockBand.Layers.rpExtEquiv i).symm
          (BlockBand.Layers.rpExtEquiv i).symm := by
      rw [show (pathMatrix x.2 - (E : ℂ) • 1).submatrix (BlockBand.Layers.rpExtEquiv i).symm
          (BlockBand.Layers.rpExtEquiv i).symm = (pathMatrix x.2).submatrix
            (BlockBand.Layers.rpExtEquiv i).symm (BlockBand.Layers.rpExtEquiv i).symm -
          (E : ℂ) • (1 : Matrix (Fin (p.n - 2) × Fin p.W) (Fin (p.n - 2) × Fin p.W) ℂ).submatrix
            (BlockBand.Layers.rpExtEquiv i).symm (BlockBand.Layers.rpExtEquiv i).symm from rfl,
        Matrix.submatrix_one_equiv]
      rfl
    rw [h1, Matrix.det_submatrix_equiv_self]
    exact hx.ne_zero
  have hS : Measurable (fun ω => BlockBand.Layers.rslUnassemble i (X.Hm ω - embedPair p i (G ω))) :=
    (BlockBand.Layers.rsl_measurable_unassemble i).comp (csm_measurable_res X hG.1)
  exact ae_of_ae_map hS.aemeasurable hlaw

end Extension

end BlockBand.Center
