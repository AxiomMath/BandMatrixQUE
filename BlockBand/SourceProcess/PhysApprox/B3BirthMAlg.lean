module

public import BlockBand.SourceProcess.PhysApprox.B3BirthFresh
public import BlockBand.SourceProcess.PhysApprox.B3MomTight
public import BlockBand.SourceProcess.ClosingLeak.Pointwise
public import BlockBand.SourceProcess.ClosingLeak.Phase
public import BlockBand.SourceProcess.ClosingAux.Reflection
public import BlockBand.SourceProcess.SmallLeak.LeakLayer

/-!
# The newborn Gram column: algebra and Gaussian averages

At length `n`, a tag `i` born at `k = ⌊Wτ_i⌋ < n` sits on the block `p = n − 1 − k`. With
`𝒰 = boundaryToInterior` and the block inclusion `ι_p` (`blockIncl`):
* the unclosed column is `V_i = √(m_i/W) R g_i`, `R = 𝒰ᴴι_p` (`probeFrame_col`), and
  `RRᴴ = Y_{n;k}` (`newR_mul_conj`);
* the closed column is `C_n(z)ᴴ V_i` (`b3ClosedFrameAt_col`); its `M_ii` and `B_ii` are
  `‖C_nᴴV_i‖²` and `‖P C_nᴴV_i‖²` (`gramEntry_closed_diag`);
* Gaussian averages over `g ~ CN(0, I_W)` (`CoareaPalm.circularVectorLaw`):
  `E‖Rg‖² = Re Tr RᴴR` (`lintegral_l2_sq_mulVec`) and
  `E|‖Rg‖² − Re Tr RᴴR| ≤ (Re Tr (RᴴR)²)^{1/2}` (`lintegral_abs_l2_sq_sub_le`);
* the closing leak `L = C_nᴴV − V` has the phase average `E_z‖L‖² = 2 Re ⟨V, A_-V⟩ ≤ 2‖(1−P)V‖²`
  at every length `n ≥ 1` (`lintegral_phase_l2_sq_le`, on the almost sure set
  `ae_phaseAvg_closingDefectAt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthM

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal ENNReal ComplexConjugate Matrix.Norms.L2Operator

variable {W n : ℕ}

/-!
## The block inclusion
-/

/-- The inclusion `ι_p : ℂ^W → ℂ^{n×W}` of the block at position `p`. -/
def blockIncl (W : ℕ) (p : Fin n) : Matrix (Fin n × Fin W) (Fin W) ℂ :=
  Matrix.of fun x a => if x = (p, a) then 1 else 0

theorem blockIncl_mulVec (p : Fin n) (g : Fin W → ℂ) (x : Fin n × Fin W) :
    (blockIncl W p *ᵥ g) x = if x.1 = p then g x.2 else 0 := by
  obtain ⟨x1, x2⟩ := x
  simp only [blockIncl, mulVec, dotProduct, of_apply, Prod.mk.injEq]
  by_cases hx : x1 = p
  · subst hx
    rw [Finset.sum_eq_single x2 (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  · simp [hx]

theorem tagVector_eq (p : Fin n) (μ : ℝ) (g : Fin W → ℂ) :
    tagVector W n p μ g = ((Real.sqrt (μ / W) : ℝ) : ℂ) • (blockIncl W p *ᵥ g) := by
  funext x
  simp only [tagVector, Pi.smul_apply, blockIncl_mulVec, smul_eq_mul]
  split_ifs <;> simp

theorem blockIncl_mul_conj {k : ℕ} (hk : k < n) :
    blockIncl W (⟨n - 1 - k, by omega⟩ : Fin n) * (blockIncl W ⟨n - 1 - k, by omega⟩)ᴴ =
      tagProjection W n k := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [blockIncl, mul_apply, conjTranspose_apply, of_apply, tagProjection, diagonal_apply,
    Prod.mk.injEq]
  rw [Finset.sum_eq_single x2 (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  by_cases h1 : x1 = ⟨n - 1 - k, by omega⟩
  · subst h1
    by_cases h2 : y1 = ⟨n - 1 - k, by omega⟩
    · subst h2
      by_cases h3 : y2 = x2
      · subst h3; simp [hk]
      · simp [h3, Ne.symm h3]
    · have h2' : ¬ ((⟨n - 1 - k, by omega⟩ : Fin n) = y1) := fun e => h2 e.symm
      simp [h2, h2']
  · have h1' : ¬ (x1.val = n - 1 - k) := fun e => h1 (Fin.ext e)
    simp [h1, h1']

/-!
## The newborn direction `R = 𝒰ᴴι_p`
-/

/-- `R = 𝒰ᴴι_p`: the boundary image of the block `p`. -/
def newR (b E : ℝ) (W n : ℕ) (p : Fin n) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  (boundaryToInterior b E W n ω)ᴴ * blockIncl W p

theorem newR_mul_conj (b E : ℝ) {k : ℕ} (hk : k < n) (ω : GrowthPath W) :
    newR b E W n ⟨n - 1 - k, by omega⟩ ω * (newR b E W n ⟨n - 1 - k, by omega⟩ ω)ᴴ =
      tagResponse b E W n k ω := by
  rw [newR, conjTranspose_mul, conjTranspose_conjTranspose, tagResponse,
    ← blockIncl_mul_conj hk]
  simp only [Matrix.mul_assoc]

theorem trace_conj_mul_newR (b E : ℝ) {k : ℕ} (hk : k < n) (ω : GrowthPath W) :
    ((newR b E W n ⟨n - 1 - k, by omega⟩ ω)ᴴ * newR b E W n ⟨n - 1 - k, by omega⟩ ω).trace =
      (tagResponse b E W n k ω).trace := by
  rw [Matrix.trace_mul_comm, newR_mul_conj b E hk]

theorem trace_sq_of_mul_conj {κ : Type*} [Fintype κ] {R : Matrix (Fin 2 × Fin W) κ ℂ}
    {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hR : R * Rᴴ = Y) :
    (Rᴴ * R * (Rᴴ * R)ᴴ).trace = (Y * Y).trace := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose, ← hR]
  calc (Rᴴ * R * (Rᴴ * R)).trace = (Rᴴ * (R * Rᴴ * R)).trace := by simp only [Matrix.mul_assoc]
    _ = (R * Rᴴ * R * Rᴴ).trace := by rw [Matrix.trace_mul_comm]
    _ = (R * Rᴴ * (R * Rᴴ)).trace := by simp only [Matrix.mul_assoc]

/-- **The unclosed newborn column**: `V_i = √(m_i/W) R g_i`. -/
theorem probeFrame_col (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (x : ProbedPath W np) :
    (fun w => probeFrame b E W n τ m x w i) =
      ((Real.sqrt (m i / W) : ℝ) : ℂ) •
        (newR b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ x.1 *ᵥ x.2 i) := by
  have e : (fun w => probeFrame b E W n τ m x w i) =
      (boundaryToInterior b E W n x.1)ᴴ *ᵥ (fun y => probeColumns W n τ m x.2 y i) := by
    funext w
    simp only [probeFrame, mul_apply, mulVec, dotProduct]
  rw [e, probeColumn_eq_tagVector n τ m _ i hi, tagVector_eq, mulVec_smul, newR, ← mulVec_mulVec]

/-- **The closed newborn column**: `C_n(z)ᴴ V_i`. -/
theorem b3ClosedFrameAt_col (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    (fun z => b3ClosedFrameAt b E s h τ m W n Vs y z (Sum.inr i)) =
      (physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ *ᵥ
        (fun w => probeFrame b E W n τ m y.1 w i) := by
  funext z
  simp only [b3ClosedFrameAt, b3OpenFrameAt, mul_apply, mulVec, dotProduct, of_apply,
    Sum.elim_inr]

/-!
## Squared norms
-/

theorem dot_self_eq_l2_sq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    star v ⬝ᵥ v = ((l2 v ^ 2 : ℝ) : ℂ) := by
  rw [dot_self_eq, l2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem dot_conj_mul_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Matrix κ ι ℂ) (u : ι → ℂ) :
    star u ⬝ᵥ ((Bᴴ * B) *ᵥ u) = ((l2 (B *ᵥ u) ^ 2 : ℝ) : ℂ) := by
  rw [← dot_self_eq_l2_sq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem nearPortProj_conj_mul_self : (nearPortProj W)ᴴ * nearPortProj W = nearPortProj W := by
  rw [nearPortProj_conjTranspose, nearPortProj_mul_self]

theorem nearPortProj_mulVec (v : Fin 2 × Fin W → ℂ) (z : Fin 2 × Fin W) :
    (nearPortProj W *ᵥ v) z = if z.1 = 0 then v z else 0 := by
  simp only [nearPortProj, mulVec_diagonal]
  split_ifs <;> simp

theorem farPart_mulVec (v : Fin 2 × Fin W → ℂ) (z : Fin 2 × Fin W) :
    ((1 - nearPortProj W) *ᵥ v) z = if z.1 = 0 then 0 else v z := by
  rw [sub_mulVec, one_mulVec, Pi.sub_apply, nearPortProj_mulVec]
  split_ifs <;> simp

theorem one_sub_nearPortProj_eq_farEmbed :
    1 - nearPortProj W = farEmbed (1 : Matrix (Fin W) (Fin W) ℂ) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  fin_cases i <;> fin_cases j <;> by_cases hxy : x = y <;>
    simp [nearPortProj, farEmbed, one_apply, hxy]

/-- `‖v‖² = ‖Pv‖² + ‖(1−P)v‖²`. -/
theorem l2_sq_split (v : Fin 2 × Fin W → ℂ) :
    l2 v ^ 2 = l2 (nearPortProj W *ᵥ v) ^ 2 + l2 ((1 - nearPortProj W) *ᵥ v) ^ 2 := by
  simp only [l2]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [nearPortProj_mulVec, farPart_mulVec]
  split_ifs <;> simp

theorem l2_near_le (v : Fin 2 × Fin W → ℂ) : l2 (nearPortProj W *ᵥ v) ≤ l2 v := by
  have h := l2_sq_split v
  have h0 := l2_nonneg (nearPortProj W *ᵥ v)
  have h1 := l2_nonneg v
  nlinarith [sq_nonneg (l2 ((1 - nearPortProj W) *ᵥ v))]

/-- **The closed diagonal Gram coordinates**: `M_ii = ‖v‖²`, `B_ii = ‖Pv‖²`, `v` the closed
column. -/
theorem gramEntry_closed_diag (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (σ : Fin 2) :
    let v := fun z => b3ClosedFrameAt b E s h τ m W n Vs y z (Sum.inr i)
    gramEntry (σ, Sum.inr i, Sum.inr i) (b3ClosedGramAt b E s h τ m W n Vs y) =
      ((if σ = 0 then l2 v ^ 2 else l2 (nearPortProj W *ᵥ v) ^ 2 : ℝ) : ℂ) := by
  intro v
  set F := b3ClosedFrameAt b E s h τ m W n Vs y
  have h0 : (Fᴴ * F) (Sum.inr i) (Sum.inr i) = star v ⬝ᵥ v := by
    simp only [mul_apply, conjTranspose_apply, dotProduct, Pi.star_apply, v, F]
  have h1 : (Fᴴ * nearPortProj W * F) (Sum.inr i) (Sum.inr i) =
      star v ⬝ᵥ (((nearPortProj W)ᴴ * nearPortProj W) *ᵥ v) := by
    rw [nearPortProj_conj_mul_self]
    simp only [mul_apply, conjTranspose_apply, dotProduct, Pi.star_apply, mulVec, v, F,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring
  simp only [gramEntry, b3ClosedGramAt, gramPair, sourceGram, nearGram]
  split_ifs with hσ
  · rw [h0, dot_self_eq_l2_sq]
  · rw [h1, dot_conj_mul_eq]

/-!
## Gaussian averages over the newborn probe
-/

section Gauss

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem quad_eq_dot (A : Matrix ι ι ℂ) (g : ι → ℂ) :
    Counting.complexQuadraticForm A g = star g ⬝ᵥ (A *ᵥ g) := by
  simp only [Counting.complexQuadraticForm, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

theorem quad_conj_mul (R : Matrix κ ι ℂ) (g : ι → ℂ) :
    Counting.complexQuadraticForm (Rᴴ * R) g = ((l2 (R *ᵥ g) ^ 2 : ℝ) : ℂ) := by
  rw [quad_eq_dot, dot_conj_mul_eq]

/-- `E‖Rg‖² = Re Tr RᴴR`. -/
theorem lintegral_l2_sq_mulVec (R : Matrix κ (Fin W) ℂ) :
    ∫⁻ g, ENNReal.ofReal (l2 (R *ᵥ g) ^ 2) ∂circularVectorLaw (Fin W) =
      ENNReal.ofReal (Rᴴ * R).trace.re := by
  have hpt : ∀ g, l2 (R *ᵥ g) ^ 2 = (Counting.complexQuadraticForm (Rᴴ * R) g).re := fun g => by
    rw [quad_conj_mul, Complex.ofReal_re]
  simp_rw [hpt]
  have hi : Integrable (fun g => (Counting.complexQuadraticForm (Rᴴ * R) g).re)
      (circularVectorLaw (Fin W)) := (Birth.integrable_quad' (Rᴴ * R)).re
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun g => by
    simp only [Pi.zero_apply]; rw [← hpt]; positivity)]
  congr 1
  have e := integral_re (Birth.integrable_quad' (Rᴴ * R))
  simp only [RCLike.re_to_complex] at e
  rw [e, Birth.integral_quad']

/-- `E|‖Rg‖² − Re Tr RᴴR| ≤ (Re Tr (RᴴR)(RᴴR)ᴴ)^{1/2}`. -/
theorem lintegral_abs_l2_sq_sub_le (R : Matrix κ (Fin W) ℂ) :
    ∫⁻ g, ENNReal.ofReal |l2 (R *ᵥ g) ^ 2 - (Rᴴ * R).trace.re| ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (Real.sqrt (Rᴴ * R * (Rᴴ * R)ᴴ).trace.re) := by
  refine le_trans (lintegral_mono fun g => ?_) (Birth.lintegral_quad_sub_le (Rᴴ * R))
  rw [quad_conj_mul, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : l2 (R *ᵥ g) ^ 2 - (Rᴴ * R).trace.re =
      (((l2 (R *ᵥ g) ^ 2 : ℝ) : ℂ) - (Rᴴ * R).trace).re := by
    rw [Complex.sub_re, Complex.ofReal_re]
  rw [e]
  exact Complex.abs_re_le_norm _

end Gauss

/-!
## The closing leak at every length
-/

/-- **The closing covariance identity at every length**: almost surely, for every `n ≥ 1`,
`1 − zN_n` is invertible on the unit circle and
`E_z (C_n(z) − 1)(C_n(z) − 1)ᴴ = 2 farEmbed A_-` (`phaseAvg_closingDefect`, with
`N^k → 0` from the injectivity argument at the length `n`). -/
theorem ae_phaseAvg_closingDefectAt {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (s h : ℝ) (hh0 : 0 < h) (hh1 : h < 1) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ n, 1 ≤ n →
      (∀ θ, IsUnit (1 - phase θ • closingN (scatteringMatrix b E W n ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) ∧
      phaseAvg (fun θ => (physClosingMapAt b E s h W n ω (phase θ) - 1) *
          (physClosingMapAt b E s h W n ω (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W (closeLen s W) ω) := by
  have hη : 0 < (boundaryZ b E).im := boundaryZ_im_pos (by linarith) hE1 hE2
  have hh2 : h ^ 2 < 1 := by nlinarith
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW, ae_growth_isHermitian W b,
    ae_isUnit_pathPencil_growth hb hW E, ae_isUnit_growth_bond hb0 hW] with ω hU hA hF hB n hn
  have hM := isUnit_fullPathMatrix b E n ω hA hη (hF _)
  have hA2 : farEmbed (omittedProj b E h W (closeLen s W) ω) *
      farEmbed (omittedProj b E h W (closeLen s W) ω) =
        farEmbed (omittedProj b E h W (closeLen s W) ω) := by
    rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : (farEmbed (omittedProj b E h W (closeLen s W) ω))ᴴ =
      farEmbed (omittedProj b E h W (closeLen s W) ω) := by
    rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hPi : farEmbed (closingPairing b E h W (closeLen s W) ω) *
      (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ =
        farEmbed (omittedProj b E h W (closeLen s W) ω) := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh2]
  have hN := tendsto_closingN_pow hA2 hAH hPi (hU n).1 (phys_hinj hη h hn ω hM hB)
  exact ⟨fun θ => isUnit_det_of_tendsto hN (norm_phase θ),
    phaseAvg_closingDefect hA2 hAH hPi (hU n).1 hN⟩

/-- Pythagoras for an orthogonal projection: `‖u‖² = ‖Fu‖² + ‖(1−F)u‖²`. -/
theorem l2_sq_proj_split {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ}
    (hF : Fᴴ = F) (hF2 : F * F = F) (u : ι → ℂ) :
    l2 u ^ 2 = l2 (F *ᵥ u) ^ 2 + l2 ((1 - F) *ᵥ u) ^ 2 := by
  have h1 : Fᴴ * F + (1 - F)ᴴ * (1 - F) = 1 := by
    rw [conjTranspose_sub, conjTranspose_one, hF, hF2, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.mul_one, hF2]
    abel
  rw [← re_dot_conj_mul F u, ← re_dot_conj_mul (1 - F) u, ← Complex.add_re, ← dotProduct_add,
    ← add_mulVec, h1, one_mulVec, l2_sq]

theorem omitted_le_far (b E h : ℝ) (k : ℕ) (ω : GrowthPath W) (v : Fin 2 × Fin W → ℂ) :
    (star v ⬝ᵥ (farEmbed (omittedProj b E h W k ω) *ᵥ v)).re ≤
      l2 ((1 - nearPortProj W) *ᵥ v) ^ 2 := by
  set F := farEmbed (omittedProj b E h W k ω)
  have hF : Fᴴ = F := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hF2 : F * F = F := by rw [farEmbed_mul, omittedProj_mul_self]
  have hFP : F * (1 - nearPortProj W) = F := by
    rw [one_sub_nearPortProj_eq_farEmbed, farEmbed_mul, Matrix.mul_one]
  have e : (star v ⬝ᵥ (F *ᵥ v)).re = l2 (F *ᵥ v) ^ 2 := by
    rw [← re_dot_conj_mul, hF, hF2]
  have e2 : F *ᵥ v = F *ᵥ ((1 - nearPortProj W) *ᵥ v) := by rw [mulVec_mulVec, hFP]
  rw [e, e2, l2_sq_proj_split hF hF2 ((1 - nearPortProj W) *ᵥ v)]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- **The phase average of the closing leak**: on the almost sure set of
`ae_phaseAvg_closingDefectAt`, `E_z‖C_n(z)ᴴV − V‖² ≤ 2‖(1−P)V‖²`. -/
theorem lintegral_phase_l2_sq_le {b E s h : ℝ} {n : ℕ} {ω : GrowthPath W}
    (hD : phaseAvg (fun θ => (physClosingMapAt b E s h W n ω (phase θ) - 1) *
          (physClosingMapAt b E s h W n ω (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W (closeLen s W) ω))
    (hU : ∀ θ, IsUnit (1 - phase θ • closingN (scatteringMatrix b E W n ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (v : Fin 2 × Fin W → ℂ) :
    ∫⁻ θ, ENNReal.ofReal (l2 ((physClosingMapAt b E s h W n ω (phase θ))ᴴ *ᵥ v - v) ^ 2)
        ∂phaseLaw ≤ ENNReal.ofReal (2 * l2 ((1 - nearPortProj W) *ᵥ v) ^ 2) := by
  set S := scatteringMatrix b E W n ω
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  set P := farEmbed (closingPairing b E h W (closeLen s W) ω)
  have hc : Continuous fun θ => physClosingMapAt b E s h W n ω (phase θ) - 1 := by
    have e : (fun θ => physClosingMapAt b E s h W n ω (phase θ) - 1) =
        fun θ => closingX S A P θ - A :=
      funext fun θ => closingMap_sub_one S A P θ
    rw [e]
    exact (continuous_closingX hU).sub continuous_const
  have hcc : Continuous fun θ => (physClosingMapAt b E s h W n ω (phase θ) - 1) *
      (physClosingMapAt b E s h W n ω (phase θ) - 1)ᴴ := hc.matrix_mul hc.matrix_conjTranspose
  set X := vecMulVec v (star v)
  have hpt : ∀ θ, l2 ((physClosingMapAt b E s h W n ω (phase θ))ᴴ *ᵥ v - v) ^ 2 =
      ((physClosingMapAt b E s h W n ω (phase θ) - 1) *
        (physClosingMapAt b E s h W n ω (phase θ) - 1)ᴴ * X).trace.re := by
    intro θ
    have e1 : l2 ((physClosingMapAt b E s h W n ω (phase θ))ᴴ *ᵥ v - v) =
        l2 (v - (physClosingMapAt b E s h W n ω (phase θ))ᴴ *ᵥ v) := by
      rw [show (physClosingMapAt b E s h W n ω (phase θ))ᴴ *ᵥ v - v =
        -(v - (physClosingMapAt b E s h W n ω (phase θ))ᴴ *ᵥ v) by abel]
      simp only [l2, Pi.neg_apply, norm_neg]
    have e2 := re_dot_conj_mul (physClosingMapAt b E s h W n ω (phase θ) - 1)ᴴ v
    rw [conjTranspose_conjTranspose] at e2
    rw [e1, l2_sub_conj, ← e2, Sampling.trace_mul_vecMulVec]
  simp only [hpt]
  have hint : Integrable (fun θ => ((physClosingMapAt b E s h W n ω (phase θ) - 1) *
      (physClosingMapAt b E s h W n ω (phase θ) - 1)ᴴ * X).trace.re) phaseLaw :=
    (integrable_of_continuous ((continuous_id.matrix_trace).comp
      (hcc.matrix_mul (continuous_const (y := X))))).re
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun θ => by
    simp only [Pi.zero_apply]; rw [← hpt]; positivity), integral_trace_re_mul hcc, hD]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul, Sampling.trace_mul_vecMulVec]
  have h2 : ((2 : ℂ) * (star v ⬝ᵥ (A *ᵥ v))).re = 2 * (star v ⬝ᵥ (A *ᵥ v)).re := by
    rw [Complex.mul_re]; simp
  rw [h2]
  linarith [omitted_le_far b E h (closeLen s W) ω v]

end BlockBand.SourceProcess.PhysApprox.B3.BirthM
