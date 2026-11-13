module

public import BlockBand.Layers.CompensatedRing
public import BlockBand.RankLocation.RankLocationLaw

/-!
# The physical count of the rank-location theorem

Law and domain: the exact physical law `model.law` (`IsPhysicalGaussianRingLaw`; raw `H`, row
variance one), every admissible `p` with `p.b = b`, `n ≤ TW`, deterministic `E ∈ bulkInterval κ`;
the removed block is `k = 0`. Norms: `L^q(model.law)`, `q ≥ 1` real. Constants depend on
`b, κ, T` (and `q`) only.

* `rkl_mp_update`: resampling one coordinate of a product law is measure preserving,
  `(x, a) ↦ update x i a : Π ν ⊗ ν → Π ν`. With `rng_law_eq_map` this gives the joint law
  `(rest, A_k) ~ rngLaw ⊗ GUE_W(c/W)` of the ring and a fresh copy of the removed block
  (`rkl_mp_psi`); the one-block complement `Σ` is a function of the rest (`rkl_S_psi`).
* `rkl_count_split`: Schur inertia on `Site = R ⊕ {k}`, for Hermitian `H` with
  `det(H_R - E) ≠ 0`: `N_H(E) = N_-(H_R - E) + N_-(A_k - E - Σ)` (`Σ` reindexed to `Fin W`).
* `rkl_ae_det_HR_rng`: `det(H_R - E) ≠ 0` almost surely (Schur determinant through the split
  `rng_HR_submatrix` and `rng_ae_invertible`).
* `rkl_physical_count_moment`, `rkl_physical_count_mean`: the two physical count clauses, from
  `FreshCountContract` (mean on its regular set `d ≤ d_*`, fluctuation conditionally on the
  rest), `RingCompensatedPhaseContract` (`Ξ_{n-1}`) and `MatchedTracesContract.commonPort`
  (`L^{2q}` moments of `d`); off the regular set `|E_A N_- - Θ - (cW/2π) Im a²| ≤ 3W ≤ 3W d²/d_*²`;
  small `W` (below the admissible range of `commonPort`) by the trivial bound `|N_H - NF| ≤ N`.
* `rkl_physicalCount_holds`: `RklPhysicalCount`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.RankLocation

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Layers
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount gueMeasure)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## 1. Resampling one coordinate of a product law
-/

section Update

/-- **Resampling one coordinate** of a product of probability laws is measure preserving:
`(x, a) ↦ update x i a` carries `(Π_j ν) ⊗ ν` to `Π_j ν`. -/
theorem rkl_mp_update {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (i : ι) :
    MeasurePreserving (fun x : (ι → X) × X => Function.update x.1 i x.2)
      ((Measure.pi fun _ : ι => ν).prod ν) (Measure.pi fun _ : ι => ν) := by
  refine ⟨measurable_update', ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : (ι → X) × X => Function.update x.1 i x.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, a⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hupd : ∀ j, ν (Function.update s i Set.univ j) =
      Function.update (fun j => ν (s j)) i 1 j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [hupd]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    ← Finset.mul_prod_erase Finset.univ (fun j => ν (s j)) (Finset.mem_univ i), mul_comm,
    Finset.sdiff_singleton_eq_erase]

end Update

/-!
## 2. The removed block as a fresh independent GUE block
-/

section Resample

variable {p : Parameters}

/-- The law `GUE_W(c/W)` of a diagonal block. -/
abbrev rklGue (p : Parameters) : Measure (Matrix (Fin p.W) (Fin p.W) ℂ) :=
  gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W))

instance rkl_isProbabilityMeasure_gue : IsProbabilityMeasure (rklGue p) :=
  isProbabilityMeasure_gueMeasure p.W _

/-- Replace the diagonal block `k` of a ring sample by `A`. -/
def rklPhi (k : ZMod p.n) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) : RngSample p :=
  (Function.update x.1.1 k x.2, x.1.2)

theorem rkl_measurable_phi (k : ZMod p.n) : Measurable (rklPhi (p := p) k) :=
  (measurable_update'.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)).prodMk
    (measurable_snd.comp measurable_fst)

/-- `(rest, A) ↦ rest with block k replaced by A` carries `rngLaw ⊗ GUE_W(c/W)` to `rngLaw`. -/
theorem rkl_mp_phi (k : ZMod p.n) :
    MeasurePreserving (rklPhi (p := p) k) ((rngLaw p).prod (rklGue p)) (rngLaw p) := by
  set μb := Measure.pi fun _ : ZMod p.n => rklGue p
  set μB := Measure.pi fun _ : ZMod p.n =>
    ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W))
  have h1 := measurePreserving_prodAssoc μb μB (rklGue p)
  have h2 := (MeasurePreserving.id μb).prod
    (Measure.measurePreserving_swap (μ := μB) (ν := rklGue p))
  have h3 := (measurePreserving_prodAssoc μb (rklGue p) μB).symm
  have h4 := (rkl_mp_update (rklGue p) k).prod (MeasurePreserving.id μB)
  have hall := h4.comp (h3.comp (h2.comp h1))
  unfold rngLaw
  convert hall using 1
  funext x
  rfl

/-- The assembled ring with block `k` resampled. -/
def rklPsi (k : ZMod p.n) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) : p.SiteMatrix :=
  rngAssemble p (rklPhi k x)

theorem rkl_mp_psi (model : p.GaussianRingModel) (k : ZMod p.n) :
    MeasurePreserving (rklPsi k) ((rngLaw p).prod (rklGue p)) (model.law : Measure p.SiteMatrix) :=
  (⟨rng_measurable_assemble, (rng_law_eq_map model).symm⟩ :
    MeasurePreserving (rngAssemble p) (rngLaw p) (model.law : Measure p.SiteMatrix)).comp
    (rkl_mp_phi k)

theorem rkl_HR_psi (k : ZMod p.n) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) :
    rngHR k (rklPsi k x) = rngHR k (rngAssemble p x.1) := by
  ext u v
  simp only [rngHR, rklPsi, rklPhi, rngAssemble]
  split_ifs with h
  · rw [Function.update_of_ne (h ▸ u.2)]
  all_goals rfl

theorem rkl_C_psi (k : ZMod p.n) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) :
    rngC k (rklPsi k x) = rngC k (rngAssemble p x.1) := by
  ext u v
  simp only [rngC, rklPsi, rklPhi, rngAssemble]
  split_ifs with h
  · rw [Function.update_of_ne u.2]
  all_goals rfl

theorem rkl_oneBlockComplement_psi (k : ZMod p.n) (E : ℝ)
    (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) :
    oneBlockComplement p k (rklPsi k x) E = oneBlockComplement p k (rngAssemble p x.1) E := by
  rw [rng_oneBlockComplement_eq, rng_oneBlockComplement_eq, rkl_HR_psi, rkl_C_psi]

/-- The block `k` coordinates `Fin W ≃ {x : Site // x.1 = k}`. -/
def rklBlockEquiv (k : ZMod p.n) : Fin p.W ≃ BlockSite p k where
  toFun a := ⟨(k, a), rfl⟩
  invFun x := x.1.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j, a⟩, h⟩
    simp only at h
    subst h
    rfl

/-- The diagonal block `k` of a site matrix. -/
def rklD (k : ZMod p.n) (H : p.SiteMatrix) : Matrix (Fin p.W) (Fin p.W) ℂ :=
  fun a b => H (k, a) (k, b)

theorem rkl_D_psi (k : ZMod p.n) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) :
    rklD k (rklPsi k x) = x.2 := by
  ext a b
  simp [rklD, rklPsi, rklPhi, rngAssemble]

/-- The one-block complement `Σ` at block `k`, reindexed to `Fin W`. -/
def rklS (k : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : Matrix (Fin p.W) (Fin p.W) ℂ :=
  (oneBlockComplement p k H E).submatrix (rklBlockEquiv k) (rklBlockEquiv k)

theorem rkl_S_psi (k : ZMod p.n) (E : ℝ) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) :
    rklS k E (rklPsi k x) = rklS k E (rngAssemble p x.1) := by
  rw [rklS, rklS, rkl_oneBlockComplement_psi]

theorem rkl_measurable_S (k : ZMod p.n) (E : ℝ) : Measurable (rklS (p := p) k E) :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => by
    change Measurable (fun H => oneBlockComplement p k H E (rklBlockEquiv k a) (rklBlockEquiv k b))
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (cph_measurable_oneBlockComplement k E))

theorem rkl_oneBlockComplement_isHermitian {k : ZMod p.n} {H : p.SiteMatrix}
    (hH : H.IsHermitian) (E : ℝ) : (oneBlockComplement p k H E).IsHermitian := by
  rw [rng_oneBlockComplement_eq]
  exact isHermitian_conjTranspose_mul_mul _ (cph_rngHR_isHermitian hH E).inv

theorem rkl_S_isHermitian {k : ZMod p.n} {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    (rklS k E H).IsHermitian :=
  (rkl_oneBlockComplement_isHermitian hH E).submatrix _

end Resample

/-!
## 3. Schur inertia on `Site = R ⊕ {k}`
-/

section Split

variable {p : Parameters}

/-- `Site ≃ R ⊕ {k}`. -/
def rklSiteSplit (k : ZMod p.n) : OffBlockSite p k ⊕ BlockSite p k ≃ p.Site :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl (fun x : p.Site => x.1 = k))

/-- The diagonal block `k` on `BlockSite`. -/
def rklDk (k : ZMod p.n) (H : p.SiteMatrix) : Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  fun x y => H x.1 y.1

theorem rkl_submatrix_split {k : ZMod p.n} {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    (H - (E : ℂ) • 1).submatrix (rklSiteSplit k) (rklSiteSplit k) =
      fromBlocks (rngHR k H - (E : ℂ) • 1) (rngC k H) (rngC k H)ᴴ (rklDk k H - (E : ℂ) • 1) := by
  ext (u | u) (v | v)
  · simp [rklSiteSplit, rngHR, one_apply, Subtype.ext_iff]
  · have huv : u.1 ≠ v.1 := fun h => u.2 (h ▸ v.2)
    simp [rklSiteSplit, rngC, one_apply, huv]
  · have huv : u.1 ≠ v.1 := fun h => v.2 (h ▸ u.2)
    simp [rklSiteSplit, rngC, one_apply, huv, ← hH.apply u.1 v.1]
  · simp [rklSiteSplit, rklDk, one_apply, Subtype.ext_iff]

/-- **Schur inertia**: for Hermitian `H` with `det(H_R - E) ≠ 0`,
`N_H(E) = N_-(H_R - E) + N_-(A_k - E - Σ)`. -/
theorem rkl_count_split {k : ZMod p.n} {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ)
    (hdet : (rngHR k H - (E : ℂ) • 1).det ≠ 0) :
    physicalCount p H E = negativeCount (rngHR k H - (E : ℂ) • 1) +
      negativeCount (rklD k H - (E : ℂ) • 1 - rklS k E H) := by
  have hM : (H - (E : ℂ) • 1).IsHermitian := cph_isHermitian_sub hH E
  have hMs := hM.submatrix (rklSiteSplit k)
  rw [rkl_submatrix_split hH E] at hMs
  have key := negativeCount_fromBlocks_schur11 hMs hdet
  rw [← rkl_submatrix_split hH E] at key
  have hDk : (rklDk k H - (E : ℂ) • 1 - (rngC k H)ᴴ * (rngHR k H - (E : ℂ) • 1)⁻¹ *
      rngC k H).IsHermitian := by
    obtain ⟨-, -, -, hR⟩ := isHermitian_fromBlocks_iff.mp hMs
    exact hR.sub (isHermitian_conjTranspose_mul_mul _ (cph_rngHR_isHermitian hH E).inv)
  have hre : (rklDk k H - (E : ℂ) • 1 - (rngC k H)ᴴ * (rngHR k H - (E : ℂ) • 1)⁻¹ *
      rngC k H).submatrix (rklBlockEquiv k) (rklBlockEquiv k) =
      rklD k H - (E : ℂ) • 1 - rklS k E H := by
    ext a b
    simp [rklDk, rklD, rklS, rng_oneBlockComplement_eq, rklBlockEquiv, one_apply]
  unfold physicalCount
  rw [← cph_negativeCount_submatrix (rklSiteSplit k) hM, key, ← hre,
    cph_negativeCount_submatrix (rklBlockEquiv k) hDk]

end Split

/-!
## 4. Almost-sure invertibility of `H_R - E`
-/

section Invertible

variable {p : Parameters}

theorem rkl_measurable_det_HR (k : ZMod p.n) (E : ℝ) :
    Measurable (fun H : p.SiteMatrix => (rngHR k H - (E : ℂ) • 1).det) :=
  (continuous_id.matrix_det).measurable.comp ((cph_measurable_rngHR k).sub measurable_const)

/-- `det(H_R - E) ≠ 0` for `H = rngAssemble ω` on the a.s. event of `rng_ae_invertible`
(Schur determinant formula in the layer ⊕ path decomposition `rng_HR_submatrix`). -/
theorem rkl_det_HR_ne_zero (ω : RngSample p) (k : ZMod p.n) (E : ℝ)
    (hH : IsUnit (pathMatrix (rngSplit k ω).2 - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag (rngSplit k ω).1.1 - (E : ℂ) • 1 -
      pathSchur E (rngSplit k ω).2).det) :
    (rngHR k (rngAssemble p ω) - (E : ℂ) • 1).det ≠ 0 := by
  rw [← det_submatrix_equiv_self (rngSiteEquiv k), rng_HR_submatrix]
  let _ := invertibleOfIsUnitDet _ hH
  rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  exact mul_ne_zero hH.ne_zero hS.ne_zero

theorem rkl_ae_det_HR_rng (k : ZMod p.n) (E : ℝ) :
    ∀ᵐ ω ∂rngLaw p, (rngHR k (rngAssemble p ω) - (E : ℂ) • 1).det ≠ 0 := by
  filter_upwards [(rng_mp_split k).quasiMeasurePreserving.ae (rng_ae_invertible p.b_lt_half E)]
    with ω hω
  exact rkl_det_HR_ne_zero ω k E hω.1 hω.2

/-- The good event on `rngLaw ⊗ GUE`: Hermitian blocks, Hermitian fresh block, invertible
`H_R - E`. -/
theorem rkl_ae_good (k : ZMod p.n) (E : ℝ) :
    ∀ᵐ x ∂(rngLaw p).prod (rklGue p), (∀ j, (x.1.1 j).IsHermitian) ∧ x.2.IsHermitian ∧
      (rngHR k (rngAssemble p x.1) - (E : ℂ) • 1).det ≠ 0 := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := rngLaw p) (ν := rklGue p)).ae
    rng_ae_blocks_isHermitian
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := rngLaw p) (ν := rklGue p)).ae
    (rng_ae_isHermitian_gue (p := p) (Real.toNNReal ((1 - 2 * p.b) / p.W)))
  have h3 := (Measure.quasiMeasurePreserving_fst (μ := rngLaw p) (ν := rklGue p)).ae
    (rkl_ae_det_HR_rng k E)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  exact ⟨hx1, hx2, hx3⟩

theorem rkl_psi_isHermitian {k : ZMod p.n} {x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ}
    (h1 : ∀ j, (x.1.1 j).IsHermitian) (h2 : x.2.IsHermitian) : (rklPsi k x).IsHermitian := by
  refine rngAssemble_isHermitian _ fun j => ?_
  by_cases hj : j = k
  · subst hj; simpa [rklPhi] using h2
  · simpa [rklPhi, Function.update_of_ne hj] using h1 j

end Invertible

/-!
## 5. The four terms of the count
-/

section Terms

variable {p : Parameters}

/-- `E_A N_-(A - E - Σ)`, the conditional mean of the fresh count. -/
def rklGf (k : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : ℝ :=
  ∫ A, (negativeCount (A - (E : ℂ) • 1 - rklS k E H) : ℝ) ∂rklGue p

/-- `Θ_{z₀}(Σ)` (Borel version). -/
def rklTheta (k : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : ℝ :=
  cphPhase (commonZ p.b E) (rklS k E H)

/-- `(cW/2π) Im a²`. -/
def rklKc (p : Parameters) (E : ℝ) : ℝ :=
  (1 - 2 * p.b) * p.W / (2 * Real.pi) * ((matchedA E) ^ 2).im

/-- The fresh-count mean error `E_A N_- - Θ_{z₀}(Σ) - (cW/2π) Im a²`. -/
def rklY (k : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : ℝ :=
  rklGf k E H - rklTheta k E H - rklKc p E

/-- The common-port residual `d = |W⁻¹ Tr(z₀ - Σ)⁻¹ - a|`. -/
def rklDist (k : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : ℝ :=
  ‖oneBlockTrace p k ((commonZ p.b E • 1 - oneBlockComplement p k H E)⁻¹) - matchedA E‖

/-- The centered fresh count, conditionally on the rest. -/
def rklV (k : ZMod p.n) (E : ℝ) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) : ℝ :=
  (negativeCount (x.2 - (E : ℂ) • 1 - rklS k E (rngAssemble p x.1)) : ℝ) -
    rklGf k E (rngAssemble p x.1)

theorem rkl_measurable_negCount_S (k : ZMod p.n) (E : ℝ) :
    Measurable (fun y : p.SiteMatrix × Matrix (Fin p.W) (Fin p.W) ℂ =>
      (negativeCount (y.2 - (E : ℂ) • 1 - rklS k E y.1) : ℝ)) :=
  cph_measurable_negativeCount.comp
    ((measurable_snd.sub measurable_const).sub ((rkl_measurable_S k E).comp measurable_fst))

theorem rkl_measurable_Gf (k : ZMod p.n) (E : ℝ) : Measurable (rklGf (p := p) k E) :=
  ((rkl_measurable_negCount_S k E).stronglyMeasurable.integral_prod_right'
    (ν := rklGue p)).measurable

theorem rkl_measurable_Theta (k : ZMod p.n) (E : ℝ) : Measurable (rklTheta (p := p) k E) :=
  (cph_measurable_phase _).comp (rkl_measurable_S k E)

theorem rkl_measurable_Y (k : ZMod p.n) (E : ℝ) : Measurable (rklY (p := p) k E) :=
  ((rkl_measurable_Gf k E).sub (rkl_measurable_Theta k E)).sub measurable_const

theorem rkl_measurable_V (k : ZMod p.n) (E : ℝ) : Measurable (rklV (p := p) k E) :=
  ((rkl_measurable_negCount_S k E).comp
      ((rng_measurable_assemble.comp measurable_fst).prodMk measurable_snd)).sub
    ((rkl_measurable_Gf k E).comp (rng_measurable_assemble.comp measurable_fst))

theorem rkl_measurable_Dist (k : ZMod p.n) (E : ℝ) : Measurable (rklDist (p := p) k E) :=
  rng_measurable_oneBlockObs k E _

theorem rkl_negCount_le (M : Matrix (Fin p.W) (Fin p.W) ℂ) :
    (negativeCount M : ℝ) ≤ p.W := by
  have := cph_negativeCount_le M
  rw [Fintype.card_fin] at this
  exact_mod_cast this

theorem rkl_abs_Gf_le (k : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : |rklGf k E H| ≤ p.W := by
  have h := norm_integral_le_of_norm_le_const (μ := rklGue p)
    (f := fun A => (negativeCount (A - (E : ℂ) • 1 - rklS k E H) : ℝ)) (C := (p.W : ℝ))
    (Filter.Eventually.of_forall fun A => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact rkl_negCount_le _)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

theorem rkl_commonZ_im_nonneg {E : ℝ} (hE : |E| ≤ 2) : 0 ≤ (commonZ p.b E).im := by
  rw [commonZ_im hE]
  have h1 : (matchedA E).im ≤ 0 := by
    simp only [matchedA]
    have := Real.sqrt_nonneg (4 - E ^ 2)
    linarith
  have h2 : 0 ≤ 1 - 2 * p.b := by linarith [p.b_lt_half]
  nlinarith

theorem rkl_abs_Theta_le (k : ZMod p.n) {E : ℝ} (hE : |E| ≤ 2) (H : p.SiteMatrix) :
    |rklTheta k E H| ≤ p.W := by
  have := cph_abs_phase_le (rkl_commonZ_im_nonneg (p := p) hE) (rklS k E H)
  rwa [Fintype.card_fin] at this

theorem rkl_abs_Kc_le {E : ℝ} (hE : |E| ≤ 2) : |rklKc p E| ≤ p.W := by
  have hE2 : E ^ 2 ≤ 4 := by nlinarith [abs_le.mp hE, sq_abs E]
  have hn := normSq_matchedA hE2
  have him : |((matchedA E) ^ 2).im| ≤ 1 := by
    have := Complex.abs_im_le_norm ((matchedA E) ^ 2)
    rwa [norm_pow, Complex.sq_norm, hn] at this
  have hb1 : 0 ≤ 1 - 2 * p.b := by linarith [p.b_lt_half]
  have hb2 : 1 - 2 * p.b ≤ 1 := by linarith [p.b_pos]
  have hW : (0 : ℝ) ≤ p.W := Nat.cast_nonneg _
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  unfold rklKc
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 - 2 * p.b) * p.W / (2 * Real.pi))]
  calc (1 - 2 * p.b) * p.W / (2 * Real.pi) * |((matchedA E) ^ 2).im|
      ≤ (1 - 2 * p.b) * p.W / (2 * Real.pi) * 1 :=
        mul_le_mul_of_nonneg_left him (by positivity)
    _ ≤ p.W := by
        rw [mul_one, div_le_iff₀ (by linarith)]
        nlinarith

end Terms

/-!
## 6. The exact decomposition and the fresh-count mean on its regular set
-/

section Decomp

variable {p : Parameters}

theorem rkl_cphPhase_S {k : ZMod p.n} {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) (z : ℂ) :
    cphPhase z (oneBlockComplement p k H E) = cphPhase z (rklS k E H) := by
  rw [← cph_phaseCount_eq (rkl_oneBlockComplement_isHermitian hH E),
    ← cph_phaseCount_eq (rkl_S_isHermitian hH E), rklS, cph_phaseCount_submatrix]

/-- **The decomposition** of the count, on the good event:
`N_H - N F = (Ξ - c₀) + (N_- - E_A N_-) + (E_A N_- - Θ - (cW/2π) Im a²) + (c₀ + (cW/2π) Im a²)`
for every constant `c₀` (later `c₀ = E Ξ`), with `H = rklPsi k x`. -/
theorem rkl_count_decomp (k : ZMod p.n) (E c₀ : ℝ)
    {x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ} (h1 : ∀ j, (x.1.1 j).IsHermitian)
    (h2 : x.2.IsHermitian) (h3 : (rngHR k (rngAssemble p x.1) - (E : ℂ) • 1).det ≠ 0) :
    (physicalCount p (rklPsi k x) E : ℝ) =
      (cphXiM p k E (rklPsi k x) - c₀) + rklV k E x + rklY k E (rklPsi k x) +
        (c₀ + rklKc p E) := by
  have hH := rkl_psi_isHermitian (k := k) h1 h2
  have hdet : (rngHR k (rklPsi k x) - (E : ℂ) • 1).det ≠ 0 := by rw [rkl_HR_psi]; exact h3
  have hXi : cphXiM p k E (rklPsi k x) =
      (negativeCount (rngHR k (rklPsi k x) - (E : ℂ) • 1) : ℝ) + rklTheta k E (rklPsi k x) := by
    unfold cphXiM rklTheta
    rw [← cph_negativeCount_eq_rawSum, rkl_cphPhase_S hH]
  have hGf : rklGf k E (rklPsi k x) = rklGf k E (rngAssemble p x.1) := by
    unfold rklGf; rw [rkl_S_psi]
  rw [rkl_count_split hH E hdet, rkl_D_psi, rkl_S_psi, hXi]
  unfold rklY rklV
  rw [hGf]
  push_cast
  ring

theorem rkl_trace_inv_submatrix {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (z : ℂ) (M : Matrix ι ι ℂ) :
    ((z • 1 - M.submatrix e e)⁻¹).trace = ((z • 1 - M)⁻¹).trace := by
  have h1 : z • (1 : Matrix κ κ ℂ) - M.submatrix e e = (z • 1 - M).submatrix e e := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [h1, inv_submatrix_equiv]
  unfold Matrix.trace
  exact Equiv.sum_comp e (fun i => ((z • 1 - M)⁻¹) i i)

theorem rkl_z0_eq {E : ℝ} (hE : |E| ≤ 2) :
    -(E : ℂ) - ((1 - 2 * p.b : ℝ) : ℂ) * matchedA E = commonZ p.b E := by
  rw [commonZ_eq hE]; push_cast; ring

theorem rkl_abs_Y_le_three (k : ZMod p.n) {E : ℝ} (hE : |E| ≤ 2) (H : p.SiteMatrix) :
    |rklY k E H| ≤ 3 * p.W := by
  unfold rklY
  have := rkl_abs_Gf_le k E H
  have := rkl_abs_Theta_le k hE H
  have := rkl_abs_Kc_le (p := p) hE
  have := abs_sub (rklGf k E H - rklTheta k E H) (rklKc p E)
  have := abs_sub (rklGf k E H) (rklTheta k E H)
  linarith

/-- The fresh count lemma (mean) with `F = Σ`, and the deterministic `O(W)` bound off its regular
set: `|E_A N_- - Θ_{z₀}(Σ) - (cW/2π) Im a²| ≤ C₁ (W d² + W^{2/5} log 2W)` for every Hermitian
`H` (`d = rklDist`), `C₁ = max(C, 3/d_*²)`. -/
theorem rkl_abs_Y_le (hfc : FreshCountContract) {b κ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (p : Parameters), p.b = b → ∀ (k : ZMod p.n) (E : ℝ),
      E ∈ bulkInterval κ → ∀ H : p.SiteMatrix, H.IsHermitian →
        |rklY k E H| ≤ C₁ * (p.W * rklDist k E H ^ 2 +
          (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := by
  obtain ⟨dstar, C, hd, hmean⟩ := hfc.mean b hb0 hb1 κ hκ
  refine ⟨max C (3 / dstar ^ 2), le_max_of_le_right (by positivity), ?_⟩
  intro p hpb k E hE H hH
  subst hpb
  have hE2 : |E| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ hE).le
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hL : 0 ≤ (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hX : 0 ≤ p.W * rklDist k E H ^ 2 + (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) := by
    positivity
  have hF := rkl_S_isHermitian (k := k) hH E
  have hdist : ‖(p.W : ℂ)⁻¹ * (((-(E : ℂ) - ((1 - 2 * p.b : ℝ) : ℂ) * matchedA E) • 1 -
      rklS k E H)⁻¹).trace - matchedA E‖ = rklDist k E H := by
    rw [rkl_z0_eq hE2, rklS, rkl_trace_inv_submatrix]
    rfl
  have hphase : phaseCount (-(E : ℂ) - ((1 - 2 * p.b : ℝ) : ℂ) * matchedA E) (rklS k E H) =
      rklTheta k E H := by
    rw [rkl_z0_eq hE2, cph_phaseCount_eq hF]; rfl
  by_cases hreg : rklDist k E H ≤ dstar
  · have h := hmean p.W p.W_pos (rklS k E H) hF E hE (by rw [hdist]; exact hreg)
    simp only [hdist, hphase] at h
    calc |rklY k E H| ≤ C * (p.W * rklDist k E H ^ 2 +
          (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  · rw [not_le] at hreg
    have h3 := rkl_abs_Y_le_three k hE2 H
    have hsq : dstar ^ 2 ≤ rklDist k E H ^ 2 := pow_le_pow_left₀ hd.le hreg.le 2
    have h4 : 3 * (p.W : ℝ) ≤ 3 / dstar ^ 2 * (p.W * rklDist k E H ^ 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) p.W]
    calc |rklY k E H| ≤ 3 / dstar ^ 2 * (p.W * rklDist k E H ^ 2) := h3.trans h4
      _ ≤ 3 / dstar ^ 2 * (p.W * rklDist k E H ^ 2 +
          (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hX

end Decomp

/-!
## 7. Moment bounds of the terms
-/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem rkl_eLpNorm_le_iff {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {r : ℝ} (hr : 0 < r)
    {c : ℝ≥0∞} : eLpNorm f (ENNReal.ofReal r) μ ≤ c ↔ ∫⁻ x, ‖f x‖ₑ ^ r ∂μ ≤ c ^ r := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hr.le, one_div, ENNReal.rpow_inv_le_iff hr]

/-- From an a.e. bound `|Y| ≤ C₁ (W d² + L)` and `‖d‖_{2r} ≤ D`: `‖Y‖_r ≤ C₁ W D² + C₁ L`. -/
theorem rkl_eLpNorm_le_of_sq [IsProbabilityMeasure μ] {Y d : Ω → ℝ}
    (hY : AEStronglyMeasurable Y μ) (hd : AEStronglyMeasurable d μ) (hd0 : ∀ x, 0 ≤ d x)
    {C₁ W L D r : ℝ} (hr : 1 ≤ r) (hC₁ : 0 ≤ C₁) (hW : 0 ≤ W) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hbound : ∀ᵐ x ∂μ, |Y x| ≤ C₁ * (W * d x ^ 2 + L))
    (hmom : eLpNorm d (ENNReal.ofReal (2 * r)) μ ≤ ENNReal.ofReal D) :
    eLpNorm Y (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (C₁ * W * D ^ 2 + C₁ * L) := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by simpa using ENNReal.ofReal_le_ofReal hr
  have hsq : AEStronglyMeasurable (fun x => d x ^ 2) μ := hd.pow 2
  calc eLpNorm Y (ENNReal.ofReal r) μ
      ≤ eLpNorm (fun x => (C₁ * W) • d x ^ 2 + C₁ * L) (ENNReal.ofReal r) μ := by
        refine eLpNorm_mono_ae_real hY (hbound.mono fun x hx => ?_)
        rw [Real.norm_eq_abs, smul_eq_mul]; linarith
    _ ≤ eLpNorm (fun x => (C₁ * W) • d x ^ 2) (ENNReal.ofReal r) μ +
        eLpNorm (fun _ => C₁ * L) (ENNReal.ofReal r) μ :=
        eLpNorm_add_le hr1
    _ = ENNReal.ofReal (C₁ * W) * eLpNorm (fun x => d x ^ 2) (ENNReal.ofReal r) μ +
        ENNReal.ofReal (C₁ * L) := by
        rw [show (fun x => (C₁ * W) • d x ^ 2) = (C₁ * W) • (fun x => d x ^ 2) from rfl,
          eLpNorm_const_smul, cph_eLpNorm_const _ (by linarith), Real.enorm_eq_ofReal_abs,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ ENNReal.ofReal (C₁ * W) * ENNReal.ofReal (D ^ 2) + ENNReal.ofReal (C₁ * L) := by
        gcongr
        have h2 := eLpNorm_norm_rpow d hd (p := ENNReal.ofReal r) (μ := μ)
          (show (0 : ℝ) < 2 by norm_num)
        have hfun : (fun x => ‖d x‖ ^ (2 : ℝ)) = fun x => d x ^ 2 := by
          funext x; rw [Real.norm_eq_abs, abs_of_nonneg (hd0 x), Real.rpow_two]
        rw [hfun, ← ENNReal.ofReal_mul (by linarith), mul_comm r 2] at h2
        rw [h2, show D ^ 2 = D ^ (2 : ℝ) by rw [Real.rpow_two],
          ← ENNReal.ofReal_rpow_of_nonneg hD (by norm_num)]
        exact ENNReal.rpow_le_rpow hmom (by norm_num)
    _ = ENNReal.ofReal (C₁ * W * D ^ 2 + C₁ * L) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]

/-- Integral form: `|∫ Y| ≤ C₁ W D² + C₁ L` from `|Y| ≤ C₁ (W d² + L)` and `‖d‖_2 ≤ D`. -/
theorem rkl_abs_integral_le_of_sq [IsProbabilityMeasure μ] {Y d : Ω → ℝ} (hYi : Integrable Y μ)
    {C₁ W L D : ℝ} (hC₁ : 0 ≤ C₁) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hbound : ∀ᵐ x ∂μ, |Y x| ≤ C₁ * (W * d x ^ 2 + L))
    (hmom : eLpNorm d (ENNReal.ofReal (2 * (1 : ℕ))) μ ≤ ENNReal.ofReal D) :
    |∫ x, Y x ∂μ| ≤ C₁ * W * D ^ 2 + C₁ * L := by
  have hmem : MemLp d (ENNReal.ofReal (2 * (1 : ℕ))) μ :=
    lt_of_le_of_lt hmom ENNReal.ofReal_lt_top
  have hmem2 : MemLp d 2 μ := by simpa using hmem
  have hint : ∫ x, d x ^ (2 * 1) ∂μ ≤ D ^ (2 * 1) :=
    cph_integral_le_of_eLpNorm le_rfl hmem hD hmom
  have hsqi := hmem2.integrable_sq
  have hbi : Integrable (fun x => C₁ * (W * d x ^ 2 + L)) μ :=
    ((hsqi.const_mul W).add (integrable_const L)).const_mul C₁
  calc |∫ x, Y x ∂μ| ≤ ∫ x, |Y x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C₁ * (W * d x ^ 2 + L) ∂μ := integral_mono_ae hYi.abs hbi hbound
    _ = C₁ * (W * ∫ x, d x ^ 2 ∂μ + L) := by
        rw [integral_const_mul, integral_add (hsqi.const_mul W) (integrable_const L),
          integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ C₁ * (W * D ^ 2 + L) := by
        have : ∫ x, d x ^ 2 ∂μ ≤ D ^ 2 := by simpa using hint
        gcongr
    _ = C₁ * W * D ^ 2 + C₁ * L := by ring

end Moments

section ScalarBounds

/-- `W^{2/5} log(2W) ≤ 20 √W` for `W ≥ 1`. -/
theorem rkl_log_bound {W : ℝ} (hW : 1 ≤ W) :
    W ^ (2 / 5 : ℝ) * Real.log (2 * W) ≤ 20 * Real.sqrt W := by
  have hW0 : 0 < W := by linarith
  have h1 := Real.log_le_rpow_div (x := 2 * W) (by linarith) (show (0 : ℝ) < 1 / 10 by norm_num)
  have h2 : (2 * W) ^ (1 / 10 : ℝ) ≤ 2 * W ^ (1 / 10 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hW0.le]
    gcongr
    calc (2 : ℝ) ^ (1 / 10 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h3 : Real.log (2 * W) ≤ 20 * W ^ (1 / 10 : ℝ) := by
    calc Real.log (2 * W) ≤ (2 * W) ^ (1 / 10 : ℝ) / (1 / 10) := h1
      _ ≤ (2 * W ^ (1 / 10 : ℝ)) / (1 / 10) := by gcongr
      _ = 20 * W ^ (1 / 10 : ℝ) := by ring
  calc W ^ (2 / 5 : ℝ) * Real.log (2 * W) ≤ W ^ (2 / 5 : ℝ) * (20 * W ^ (1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 20 * (W ^ (2 / 5 : ℝ) * W ^ (1 / 10 : ℝ)) := by ring
    _ = 20 * Real.sqrt W := by
        rw [← Real.rpow_add hW0, Real.sqrt_eq_rpow]
        norm_num

/-- The deterministic constants: `(n-1)F_sc + ℓ + bh + ch/2 = nF_sc`, as
`(n-1)WF + W(ℓ + bh) + (cW/2π) Im a² = N F` for `-2 ≤ E ≤ 2` (`F_sc = ℓ + h/2`). -/
theorem rkl_constants (p : Parameters) {E : ℝ} (hE : E ∈ Set.Icc (-2 : ℝ) 2) :
    ((p.n : ℝ) - 1) * p.W * semicircleCDF E + p.W * (phaseEll E + p.b * phaseH E) +
        rklKc p E = p.N * semicircleCDF E := by
  have hF := semicircleCDF_eq_phase hE
  have hpi := Real.pi_pos.ne'
  unfold rklKc
  rw [show phaseH E = ((matchedA E) ^ 2).im / Real.pi from rfl] at hF ⊢
  rw [hF, BlockBand.Parameters.N, Nat.cast_mul]
  field_simp
  ring

end ScalarBounds

/-!
## 8. The fresh centered count and the count identity
-/

section Fresh

variable {p : Parameters}

theorem rkl_abs_V_le (k : ZMod p.n) (E : ℝ) (x : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ) :
    |rklV k E x| ≤ 2 * p.W := by
  unfold rklV
  have h1 := rkl_negCount_le (x.2 - (E : ℂ) • 1 - rklS k E (rngAssemble p x.1))
  have h0 : (0 : ℝ) ≤ negativeCount (x.2 - (E : ℂ) • 1 - rklS k E (rngAssemble p x.1)) :=
    Nat.cast_nonneg _
  have h2 := rkl_abs_Gf_le k E (rngAssemble p x.1)
  rw [abs_le] at h2 ⊢
  constructor <;> linarith

/-- **The fresh count lemma (fluctuation), conditionally on the rest**: `‖N_- - E_A N_-‖_q ≤ C_q √W`
under `rngLaw ⊗ GUE_W(c/W)`, with `F = Σ(rest)` Hermitian a.s. -/
theorem rkl_eLpNorm_V (hfc : FreshCountContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {q : ℝ} (hq : 1 ≤ q) :
    ∃ Cv : ℝ, ∀ (p : Parameters), p.b = b → ∀ (k : ZMod p.n) (E : ℝ),
      eLpNorm (rklV k E) (ENNReal.ofReal q) ((rngLaw p).prod (rklGue p)) ≤
        ENNReal.ofReal (Cv * Real.sqrt p.W) := by
  obtain ⟨Cv, hfl⟩ := hfc.fluctuation b hb0 hb1 q hq
  refine ⟨Cv, fun p hpb k E => ?_⟩
  subst hpb
  have hq0 : 0 < q := by linarith
  rw [rkl_eLpNorm_le_iff (rkl_measurable_V k E).aestronglyMeasurable hq0,
    lintegral_prod _ ((rkl_measurable_V k E).enorm.pow_const q).aemeasurable]
  calc ∫⁻ ω, ∫⁻ A, ‖rklV k E (ω, A)‖ₑ ^ q ∂rklGue p ∂rngLaw p
      ≤ ∫⁻ _ω, ENNReal.ofReal (Cv * Real.sqrt p.W) ^ q ∂rngLaw p := by
        refine lintegral_mono_ae ?_
        filter_upwards [rng_ae_blocks_isHermitian] with ω hω
        have hF := rkl_S_isHermitian (k := k) (rngAssemble_isHermitian ω hω) E
        have h := hfl p.W p.W_pos _ hF E
        have hmeas : AEStronglyMeasurable (fun A : Matrix (Fin p.W) (Fin p.W) ℂ =>
            (negativeCount (A - (E : ℂ) • 1 - rklS k E (rngAssemble p ω)) : ℝ) -
              rklGf k E (rngAssemble p ω)) (rklGue p) :=
          ((cph_measurable_negativeCount.comp ((measurable_id.sub measurable_const).sub
            measurable_const)).sub measurable_const).aestronglyMeasurable
        exact (rkl_eLpNorm_le_iff hmeas hq0).mp h
    _ = ENNReal.ofReal (Cv * Real.sqrt p.W) ^ q := by
        rw [lintegral_const, measure_univ, mul_one]

theorem rkl_integral_V (k : ZMod p.n) (E : ℝ) :
    ∫ x, rklV k E x ∂(rngLaw p).prod (rklGue p) = 0 := by
  rw [integral_prod _ (cph_integrable_of_bound (rkl_measurable_V k E).aestronglyMeasurable
    (rkl_abs_V_le k E))]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hi : Integrable (fun A : Matrix (Fin p.W) (Fin p.W) ℂ =>
      (negativeCount (A - (E : ℂ) • 1 - rklS k E (rngAssemble p ω)) : ℝ)) (rklGue p) :=
    cph_integrable_of_bound (cph_measurable_negativeCount.comp ((measurable_id.sub
      measurable_const).sub measurable_const)).aestronglyMeasurable
      (fun A => by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact rkl_negCount_le _)
  change ∫ A, ((negativeCount (A - (E : ℂ) • 1 - rklS k E (rngAssemble p ω)) : ℝ) -
    rklGf k E (rngAssemble p ω)) ∂rklGue p = 0
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
  unfold rklGf
  ring

theorem rkl_measurable_count (E : ℝ) :
    Measurable (fun H : p.SiteMatrix => (physicalCount p H E : ℝ)) :=
  cph_measurable_negativeCount.comp (measurable_id.sub measurable_const)

theorem rkl_count_le (H : p.SiteMatrix) (E : ℝ) : (physicalCount p H E : ℝ) ≤ p.N := by
  have := cph_negativeCount_le (H - (E : ℂ) • 1)
  rw [BlockBand.Model.Construction.physicalSite_card] at this
  exact_mod_cast this

theorem rkl_abs_count_sub_le (H : p.SiteMatrix) (E : ℝ) :
    |(physicalCount p H E : ℝ) - p.N * semicircleCDF E| ≤ p.N := by
  have h1 := rkl_count_le H E
  have h0 : (0 : ℝ) ≤ physicalCount p H E := Nat.cast_nonneg _
  have hF0 := semicircleCDF_nonneg E
  have hF1 := semicircleCDF_le_one E
  have hN : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

/-- **The count identity in mean**: `E N_H - N F = E Y + (E Ξ + (cW/2π) Im a² - N F)`. -/
theorem rkl_integral_count (model : p.GaussianRingModel) (k : ZMod p.n) {E : ℝ} (hE : |E| ≤ 2) :
    (∫ H, (physicalCount p H E : ℝ) ∂(model.law : Measure p.SiteMatrix)) - p.N * semicircleCDF E =
      (∫ H, rklY k E H ∂(model.law : Measure p.SiteMatrix)) +
        ((∫ H, ringCompensatedPhase p k H E ∂(model.law : Measure p.SiteMatrix)) + rklKc p E -
          p.N * semicircleCDF E) := by
  set c₀ := ∫ H, ringCompensatedPhase p k H E ∂(model.law : Measure p.SiteMatrix)
  have hmp := rkl_mp_psi model k
  have hz0 := rkl_commonZ_im_nonneg (p := p) hE
  have hXi : ∫ H, cphXiM p k E H ∂(model.law : Measure p.SiteMatrix) = c₀ :=
    (integral_congr_ae (cph_xi_ae_eq model k E)).symm
  have hiXi : Integrable (fun x => cphXiM p k E (rklPsi k x) - c₀) ((rngLaw p).prod (rklGue p)) :=
    cph_integrable_of_bound (((cph_measurable_xiM k E).comp hmp.measurable).sub_const
      c₀).aestronglyMeasurable (B := 2 * (p.n * p.W) + |c₀|) fun x => by
      have := cph_abs_xiM_le (k := k) hz0 (rklPsi k x)
      have := abs_sub (cphXiM p k E (rklPsi k x)) c₀
      linarith
  have hiV : Integrable (rklV k E) ((rngLaw p).prod (rklGue p)) :=
    cph_integrable_of_bound (rkl_measurable_V k E).aestronglyMeasurable (rkl_abs_V_le k E)
  have hiY : Integrable (fun x => rklY k E (rklPsi k x)) ((rngLaw p).prod (rklGue p)) :=
    cph_integrable_of_bound ((rkl_measurable_Y k E).comp hmp.measurable).aestronglyMeasurable
      fun x => rkl_abs_Y_le_three k hE _
  have h1 : ∫ H, (physicalCount p H E : ℝ) ∂(model.law : Measure p.SiteMatrix) =
      ∫ x, (physicalCount p (rklPsi k x) E : ℝ) ∂(rngLaw p).prod (rklGue p) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (rkl_measurable_count E).aestronglyMeasurable]
  have h2 : ∫ x, (physicalCount p (rklPsi k x) E : ℝ) ∂(rngLaw p).prod (rklGue p) =
      ∫ x, ((cphXiM p k E (rklPsi k x) - c₀) + rklV k E x + rklY k E (rklPsi k x) +
        (c₀ + rklKc p E)) ∂(rngLaw p).prod (rklGue p) := by
    refine integral_congr_ae ?_
    filter_upwards [rkl_ae_good k E] with x hx
    exact rkl_count_decomp k E c₀ hx.1 hx.2.1 hx.2.2
  have hiXi0 : Integrable (fun x => cphXiM p k E (rklPsi k x)) ((rngLaw p).prod (rklGue p)) :=
    cph_integrable_of_bound ((cph_measurable_xiM k E).comp hmp.measurable).aestronglyMeasurable
      (B := 2 * (p.n * p.W)) fun x => cph_abs_xiM_le (k := k) hz0 (rklPsi k x)
  have hXiP : ∫ x, cphXiM p k E (rklPsi k x) ∂(rngLaw p).prod (rklGue p) = c₀ := by
    rw [← hXi, ← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (cph_measurable_xiM k E).aestronglyMeasurable]
  have h3 : ∫ x, (cphXiM p k E (rklPsi k x) - c₀) ∂(rngLaw p).prod (rklGue p) = 0 := by
    rw [integral_sub hiXi0 (integrable_const c₀), hXiP, integral_const, probReal_univ, one_smul,
      sub_self]
  have h4 : ∫ x, rklY k E (rklPsi k x) ∂(rngLaw p).prod (rklGue p) =
      ∫ H, rklY k E H ∂(model.law : Measure p.SiteMatrix) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (rkl_measurable_Y k E).aestronglyMeasurable]
  have hA : Integrable (fun x => cphXiM p k E (rklPsi k x) - c₀ + rklV k E x)
      ((rngLaw p).prod (rklGue p)) := hiXi.add hiV
  have hB : Integrable (fun x => cphXiM p k E (rklPsi k x) - c₀ + rklV k E x +
      rklY k E (rklPsi k x)) ((rngLaw p).prod (rklGue p)) := hA.add hiY
  rw [h1, h2, integral_add hB (integrable_const _), integral_add hA hiY, integral_add hiXi hiV, h3,
    rkl_integral_V, h4, integral_const, probReal_univ, one_smul]
  ring

end Fresh

/-!
## 9. The physical count clauses
-/

section Physical

theorem rkl_ofReal_add4_le {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d ≤ e) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d ≤
      ENNReal.ofReal e := by
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (by positivity) hc,
    ← ENNReal.ofReal_add (by positivity) hd]
  exact ENNReal.ofReal_le_ofReal h

/-- `|E Ξ + (cW/2π) Im a² - N F| ≤ C n/W` from the `Ξ` mean (`RingCompensatedPhaseContract`)
and the constant identity `rkl_constants`. -/
theorem rkl_abs_const_le {p : Parameters} {E C : ℝ} (hE : |E| ≤ 2) {c₀ : ℝ}
    (hm : |c₀ - ((p.n : ℝ) - 1) * p.W * semicircleCDF E - p.W * (phaseEll E + p.b * phaseH E)| ≤
      C * p.n / p.W) :
    |c₀ + rklKc p E - p.N * semicircleCDF E| ≤ C * p.n / p.W := by
  have hc := rkl_constants p (abs_le.mp hE)
  have : c₀ + rklKc p E - p.N * semicircleCDF E =
      c₀ - ((p.n : ℝ) - 1) * p.W * semicircleCDF E - p.W * (phaseEll E + p.b * phaseH E) := by
    linarith
  rw [this]; exact hm

/-- **The physical count bound** under the physical law:
`‖N_H(E) - N F_sc(E)‖_q ≤ C_q √W`, uniformly in `p` with `p.b = b`, `n ≤ TW`, `E ∈ I`. -/
theorem rkl_physical_count_moment (hfc : FreshCountContract)
    (hring : RingCompensatedPhaseContract) (hmt : MatchedTracesContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (E : ℝ), E ∈ bulkInterval κ →
      eLpNorm (fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E) (ENNReal.ofReal q)
          (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal (Cq * Real.sqrt p.W) := by
  intro b hb0 hb1 κ T hκ q hq
  obtain ⟨Cx, hx⟩ := hring.fluctuation b hb0 hb1 κ T hκ q hq
  obtain ⟨Cm, hm⟩ := hring.mean b hb0 hb1 κ T hκ
  obtain ⟨Cv, hv⟩ := rkl_eLpNorm_V hfc hb0 hb1 hq
  obtain ⟨C₁, hC₁, hY⟩ := rkl_abs_Y_le hfc hb0 hb1 hκ
  obtain ⟨ε₀, C₅, hε₀, hcp⟩ := hmt.commonPort b hb0 hb1 κ T hκ
  have hq0 : 0 < q := by linarith
  set R : ℝ := 2 * q / ε₀ with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨|Cx| * Real.sqrt |T| + |Cv| + C₁ * C₅ ^ 2 * (2 * q) + C₁ * 20 + |Cm| * |T| +
    |T| * R * Real.sqrt R, ?_⟩
  intro p hpb hn model E hE
  have hE2 : |E| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ hE).le
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hsW : 1 ≤ Real.sqrt p.W := Real.one_le_sqrt.mpr hW1
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hTW : (p.n : ℝ) ≤ |T| * p.W :=
    hn.trans (mul_le_mul_of_nonneg_right (le_abs_self T) hW0.le)
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have hpos : 0 ≤ |Cx| * Real.sqrt |T| + |Cv| + C₁ * C₅ ^ 2 * (2 * q) + C₁ * 20 + |Cm| * |T| :=
    by positivity
  by_cases hlarge : 2 * q ≤ ε₀ * p.W
  · set k : ZMod p.n := 0
    set c₀ := ∫ H, ringCompensatedPhase p k H E ∂(model.law : Measure p.SiteMatrix)
    have hmp := rkl_mp_psi model k
    rw [← eLpNorm_comp_measurePreserving ((rkl_measurable_count E).sub_const
      _).aestronglyMeasurable hmp]
    have hdec : ((fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E) ∘ rklPsi k) =ᵐ[
        (rngLaw p).prod (rklGue p)]
        (((fun x => cphXiM p k E (rklPsi k x) - c₀) + rklV k E) +
          (fun x => rklY k E (rklPsi k x))) +
          fun _ => c₀ + rklKc p E - p.N * semicircleCDF E := by
      filter_upwards [rkl_ae_good k E] with x hx
      simp only [Function.comp_apply, Pi.add_apply]
      rw [rkl_count_decomp k E c₀ hx.1 hx.2.1 hx.2.2]
      ring
    rw [eLpNorm_congr_ae hdec]
    have h1 : eLpNorm (fun x => cphXiM p k E (rklPsi k x) - c₀) (ENNReal.ofReal q)
        ((rngLaw p).prod (rklGue p)) ≤ ENNReal.ofReal (Cx * Real.sqrt p.n) := by
      rw [show (fun x => cphXiM p k E (rklPsi k x) - c₀) =
          (fun H => cphXiM p k E H - c₀) ∘ rklPsi k from rfl,
        eLpNorm_comp_measurePreserving ((cph_measurable_xiM k E).sub_const
          c₀).aestronglyMeasurable hmp]
      have hae : (fun H => cphXiM p k E H - c₀) =ᵐ[(model.law : Measure p.SiteMatrix)]
          fun H => ringCompensatedPhase p k H E - c₀ := by
        filter_upwards [cph_xi_ae_eq model k E] with H hH
        rw [hH]
      rw [eLpNorm_congr_ae hae]
      exact hx p hpb hn model k E hE
    have h2 := hv p hpb k E
    have hL : 0 ≤ (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    set D := |C₅| * Real.sqrt (2 * q) / p.W with hDdef
    have hD : 0 ≤ D := by positivity
    have hmom : eLpNorm (rklDist k E) (ENNReal.ofReal (2 * q)) (model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal D := by
      have hcp' := hcp p hpb hn model k E hE (2 * q) (by linarith) hlarge
      rw [← hpb] at hcp'
      refine hcp'.trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.sqrt_nonneg _)) hW0.le
    have h3 : eLpNorm (fun x => rklY k E (rklPsi k x)) (ENNReal.ofReal q)
        ((rngLaw p).prod (rklGue p)) ≤
        ENNReal.ofReal (C₁ * p.W * D ^ 2 +
          C₁ * ((p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W))) := by
      rw [show (fun x => rklY k E (rklPsi k x)) = rklY k E ∘ rklPsi k from rfl,
        eLpNorm_comp_measurePreserving (rkl_measurable_Y k E).aestronglyMeasurable hmp]
      refine rkl_eLpNorm_le_of_sq (rkl_measurable_Y k E).aestronglyMeasurable
        (rkl_measurable_Dist k E).aestronglyMeasurable (fun H => norm_nonneg _) hq hC₁ hW0.le hL hD
        ?_ hmom
      filter_upwards [cph_ring_ae_herm model] with H hH
      exact hY p hpb k E hE H hH
    have h4 : eLpNorm (fun _ : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ =>
        c₀ + rklKc p E - p.N * semicircleCDF E) (ENNReal.ofReal q) ((rngLaw p).prod (rklGue p)) =
        ENNReal.ofReal |c₀ + rklKc p E - p.N * semicircleCDF E| := cph_eLpNorm_const _ hq0
    have h4' : |c₀ + rklKc p E - p.N * semicircleCDF E| ≤ Cm * p.n / p.W := by
      have := hm p hpb hn model k E hE
      rw [← hpb] at this
      exact rkl_abs_const_le hE2 this
    -- real inequalities
    have ea : Cx * Real.sqrt p.n ≤ |Cx| * Real.sqrt |T| * Real.sqrt p.W := by
      calc Cx * Real.sqrt p.n ≤ |Cx| * Real.sqrt p.n :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
        _ ≤ |Cx| * Real.sqrt (|T| * p.W) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTW) (abs_nonneg _)
        _ = |Cx| * Real.sqrt |T| * Real.sqrt p.W := by
            rw [Real.sqrt_mul (abs_nonneg T)]; ring
    have eb : Cv * Real.sqrt p.W ≤ |Cv| * Real.sqrt p.W :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
    have hDsq : (p.W : ℝ) * D ^ 2 = C₅ ^ 2 * (2 * q) / p.W := by
      rw [hDdef, div_pow, mul_pow, sq_abs, Real.sq_sqrt (by linarith)]
      field_simp
    have ec : C₁ * p.W * D ^ 2 + C₁ * ((p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) ≤
        C₁ * C₅ ^ 2 * (2 * q) * Real.sqrt p.W + C₁ * 20 * Real.sqrt p.W := by
      have hc1 : C₁ * p.W * D ^ 2 ≤ C₁ * C₅ ^ 2 * (2 * q) * Real.sqrt p.W := by
        rw [mul_assoc, hDsq]
        have : C₅ ^ 2 * (2 * q) / p.W ≤ C₅ ^ 2 * (2 * q) * Real.sqrt p.W :=
          (div_le_self (by positivity) hW1).trans (le_mul_of_one_le_right (by positivity) hsW)
        calc C₁ * (C₅ ^ 2 * (2 * q) / p.W) ≤ C₁ * (C₅ ^ 2 * (2 * q) * Real.sqrt p.W) :=
              mul_le_mul_of_nonneg_left this hC₁
          _ = _ := by ring
      have hc2 : C₁ * ((p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) ≤
          C₁ * 20 * Real.sqrt p.W := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (rkl_log_bound hW1) hC₁
      linarith
    have ed : |c₀ + rklKc p E - p.N * semicircleCDF E| ≤ |Cm| * |T| * Real.sqrt p.W := by
      refine h4'.trans ?_
      have hnW : (p.n : ℝ) / p.W ≤ |T| := (div_le_iff₀ hW0).mpr hTW
      calc Cm * p.n / p.W ≤ |Cm| * (p.n / p.W) := by
            rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |Cm| * |T| := mul_le_mul_of_nonneg_left hnW (abs_nonneg _)
        _ ≤ |Cm| * |T| * Real.sqrt p.W := le_mul_of_one_le_right (by positivity) hsW
    calc eLpNorm ((((fun x => cphXiM p k E (rklPsi k x) - c₀) + rklV k E) +
          (fun x => rklY k E (rklPsi k x))) +
          fun _ => c₀ + rklKc p E - p.N * semicircleCDF E) (ENNReal.ofReal q)
          ((rngLaw p).prod (rklGue p))
        ≤ eLpNorm (fun x => cphXiM p k E (rklPsi k x) - c₀) (ENNReal.ofReal q)
            ((rngLaw p).prod (rklGue p)) +
          eLpNorm (rklV k E) (ENNReal.ofReal q) ((rngLaw p).prod (rklGue p)) +
          eLpNorm (fun x => rklY k E (rklPsi k x)) (ENNReal.ofReal q)
            ((rngLaw p).prod (rklGue p)) +
          eLpNorm (fun _ : RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ =>
            c₀ + rklKc p E - p.N * semicircleCDF E) (ENNReal.ofReal q)
            ((rngLaw p).prod (rklGue p)) := by
          refine (eLpNorm_add_le hq1).trans (add_le_add_left ?_ _)
          refine (eLpNorm_add_le hq1).trans (add_le_add_left ?_ _)
          exact eLpNorm_add_le hq1
      _ ≤ ENNReal.ofReal (|Cx| * Real.sqrt |T| * Real.sqrt p.W) +
          ENNReal.ofReal (|Cv| * Real.sqrt p.W) +
          ENNReal.ofReal (C₁ * C₅ ^ 2 * (2 * q) * Real.sqrt p.W + C₁ * 20 * Real.sqrt p.W) +
          ENNReal.ofReal (|Cm| * |T| * Real.sqrt p.W) := by
          rw [h4]
          gcongr
          · exact h1.trans (ENNReal.ofReal_le_ofReal ea)
          · exact h2.trans (ENNReal.ofReal_le_ofReal eb)
          · exact h3.trans (ENNReal.ofReal_le_ofReal ec)
      _ ≤ _ := by
          refine rkl_ofReal_add4_le (by positivity) (by positivity) (by positivity)
            (by positivity) ?_
          have : 0 ≤ |T| * R * Real.sqrt R * Real.sqrt p.W := by positivity
          nlinarith
  · rw [not_le] at hlarge
    have hWR : (p.W : ℝ) ≤ R := by
      rw [hR, le_div_iff₀ hε₀]; linarith
    have hb := eLpNorm_le_of_ae_bound (μ := (model.law : Measure p.SiteMatrix))
      (p := ENNReal.ofReal q) ((rkl_measurable_count E).sub_const
        (p.N * semicircleCDF E)).aestronglyMeasurable (C := p.N)
      (Filter.Eventually.of_forall fun H => by
        rw [Real.norm_eq_abs]; exact rkl_abs_count_sub_le H E)
    rw [measure_univ, ENNReal.one_rpow, one_mul] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : Real.sqrt p.W * Real.sqrt p.W = p.W := Real.mul_self_sqrt hW0.le
    have hsR : Real.sqrt p.W ≤ Real.sqrt R := Real.sqrt_le_sqrt hWR
    have hN : (p.N : ℝ) = p.n * p.W := by rw [BlockBand.Parameters.N, Nat.cast_mul]
    have h1 : (p.N : ℝ) ≤ |T| * (p.W * p.W) := by
      rw [hN, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hTW hW0.le
    have h2 : (p.W : ℝ) * p.W ≤ R * Real.sqrt R * Real.sqrt p.W := by
      calc (p.W : ℝ) * p.W = p.W * Real.sqrt p.W * Real.sqrt p.W := by rw [mul_assoc, hsq]
        _ ≤ R * Real.sqrt R * Real.sqrt p.W := by gcongr
    have h3 : |T| * (p.W * p.W) ≤ |T| * R * Real.sqrt R * Real.sqrt p.W := by
      calc |T| * (p.W * p.W) ≤ |T| * (R * Real.sqrt R * Real.sqrt p.W) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = _ := by ring
    have : 0 ≤ (|Cx| * Real.sqrt |T| + |Cv| + C₁ * C₅ ^ 2 * (2 * q) + C₁ * 20 + |Cm| * |T|) *
        Real.sqrt p.W := by positivity
    nlinarith

/-- **The physical count mean bound** under the physical law:
`|E N_H(E) - N F_sc(E)| ≤ C (n/W + W^{2/5} log 2W)`, uniformly in `p` with `p.b = b`, `n ≤ TW`,
`E ∈ I`. -/
theorem rkl_physical_count_mean (hfc : FreshCountContract)
    (hring : RingCompensatedPhaseContract) (hmt : MatchedTracesContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (E : ℝ), E ∈ bulkInterval κ →
      |(∫ H, (physicalCount p H E : ℝ) ∂(model.law : Measure p.SiteMatrix)) -
          p.N * semicircleCDF E| ≤
        C * ((p.n : ℝ) / p.W + (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨Cm, hm⟩ := hring.mean b hb0 hb1 κ T hκ
  obtain ⟨C₁, hC₁, hY⟩ := rkl_abs_Y_le hfc hb0 hb1 hκ
  obtain ⟨ε₀, C₅, hε₀, hcp⟩ := hmt.commonPort b hb0 hb1 κ T hκ
  set R : ℝ := 2 / ε₀ with hR
  refine ⟨C₁ * C₅ ^ 2 * 2 + |Cm| + C₁ + R ^ 2, ?_⟩
  intro p hpb hn model E hE
  have hE2 : |E| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ hE).le
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hnW : 0 ≤ (p.n : ℝ) / p.W := by positivity
  have hL : 0 ≤ (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  by_cases hlarge : 2 ≤ ε₀ * p.W
  · set k : ZMod p.n := 0
    rw [rkl_integral_count model k hE2]
    set c₀ := ∫ H, ringCompensatedPhase p k H E ∂(model.law : Measure p.SiteMatrix)
    set D := |C₅| * Real.sqrt 2 / p.W with hDdef
    have hD : 0 ≤ D := by positivity
    have hmom : eLpNorm (rklDist k E) (ENNReal.ofReal (2 * ((1 : ℕ) : ℝ)))
        (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal D := by
      have hcp' := hcp p hpb hn model k E hE 2 le_rfl hlarge
      rw [← hpb] at hcp'
      rw [Nat.cast_one, mul_one]
      refine hcp'.trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.sqrt_nonneg _)) hW0.le
    have hYi : Integrable (rklY k E) (model.law : Measure p.SiteMatrix) :=
      cph_integrable_of_bound (rkl_measurable_Y k E).aestronglyMeasurable
        (fun H => rkl_abs_Y_le_three k hE2 H)
    have hYb := rkl_abs_integral_le_of_sq hYi hC₁ hW0.le hD
      (L := (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W))
      (by filter_upwards [cph_ring_ae_herm model] with H hH; exact hY p hpb k E hE H hH) hmom
    have hconst : |c₀ + rklKc p E - p.N * semicircleCDF E| ≤ Cm * p.n / p.W := by
      have := hm p hpb hn model k E hE
      rw [← hpb] at this
      exact rkl_abs_const_le hE2 this
    have hDsq : (p.W : ℝ) * D ^ 2 = C₅ ^ 2 * 2 / p.W := by
      rw [hDdef, div_pow, mul_pow, sq_abs, Real.sq_sqrt (by norm_num)]
      field_simp
    have e1 : C₁ * p.W * D ^ 2 ≤ C₁ * C₅ ^ 2 * 2 * ((p.n : ℝ) / p.W) := by
      rw [mul_assoc, hDsq]
      have : C₅ ^ 2 * 2 / p.W ≤ C₅ ^ 2 * 2 * ((p.n : ℝ) / p.W) := by
        rw [div_eq_mul_one_div (C₅ ^ 2 * 2)]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn1 hW0.le) (by positivity)
      calc C₁ * (C₅ ^ 2 * 2 / p.W) ≤ C₁ * (C₅ ^ 2 * 2 * ((p.n : ℝ) / p.W)) :=
            mul_le_mul_of_nonneg_left this hC₁
        _ = _ := by ring
    have e2 : Cm * p.n / p.W ≤ |Cm| * ((p.n : ℝ) / p.W) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hnW
    have htri := abs_add_le (∫ H, rklY k E H ∂(model.law : Measure p.SiteMatrix))
      (c₀ + rklKc p E - p.N * semicircleCDF E)
    have : 0 ≤ R ^ 2 * ((p.n : ℝ) / p.W + (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := by
      positivity
    have : 0 ≤ C₁ * C₅ ^ 2 * 2 * ((p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := by positivity
    have : 0 ≤ |Cm| * ((p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := by positivity
    have : 0 ≤ C₁ * ((p.n : ℝ) / p.W) := by positivity
    nlinarith
  · rw [not_le] at hlarge
    have hWR : (p.W : ℝ) ≤ R := by
      rw [hR, le_div_iff₀ hε₀]; linarith
    have hint : Integrable (fun H => (physicalCount p H E : ℝ))
        (model.law : Measure p.SiteMatrix) :=
      cph_integrable_of_bound (rkl_measurable_count E).aestronglyMeasurable (B := p.N)
        fun H => by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact rkl_count_le H E
    have hb := norm_integral_le_of_norm_le_const (μ := (model.law : Measure p.SiteMatrix))
      (f := fun H => (physicalCount p H E : ℝ) - p.N * semicircleCDF E) (C := (p.N : ℝ))
      (Filter.Eventually.of_forall fun H => by
        rw [Real.norm_eq_abs]; exact rkl_abs_count_sub_le H E)
    rw [probReal_univ, mul_one, Real.norm_eq_abs, integral_sub hint (integrable_const _),
      integral_const, probReal_univ, one_smul] at hb
    refine hb.trans ?_
    have hN : (p.N : ℝ) = (p.n / p.W) * (p.W * p.W) := by
      rw [BlockBand.Parameters.N, Nat.cast_mul]; field_simp
    have hWW : (p.W : ℝ) * p.W ≤ R ^ 2 := by rw [sq]; exact mul_le_mul hWR hWR hW0.le (by linarith)
    have h1 : (p.N : ℝ) ≤ R ^ 2 * ((p.n : ℝ) / p.W) := by
      rw [hN, mul_comm (R ^ 2)]; exact mul_le_mul_of_nonneg_left hWW hnW
    have : 0 ≤ (C₁ * C₅ ^ 2 * 2 + |Cm| + C₁) *
        ((p.n : ℝ) / p.W + (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := by positivity
    have : 0 ≤ R ^ 2 * ((p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W)) := by positivity
    nlinarith

/-- **The physical count clauses of the rank-location theorem**, from the fresh count lemma, the
`Ξ` estimate and the matched traces theorem (common port). -/
theorem rkl_physicalCount_holds (hfc : FreshCountContract)
    (hring : RingCompensatedPhaseContract) (hmt : MatchedTracesContract) : RklPhysicalCount :=
  ⟨rkl_physical_count_moment hfc hring hmt, rkl_physical_count_mean hfc hring hmt⟩

end Physical

end BlockBand.RankLocation
