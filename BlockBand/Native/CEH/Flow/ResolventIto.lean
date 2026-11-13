module

public import BlockBand.Native.CEH.Flow.ResolventCalc
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
public import BlockBand.Palm.RelativeLocalizationSemimart
public import BlockBand.Palm.CoarseRelativeAlgebra
public import BlockBand.External.CEH.SourceObservables

/-!
# CEH flow: Itô formula for the resolvent along the characteristic flow

Setting: `(Ω, 𝓖, Q)` a filtered probability space, `G` a Hermitian Brownian motion for `𝓖`
(`IsHermitianBrownian`, increments `GUE_N((t-s)/N)`, i.e. `E|dG_ab|² = dt/N`), `F` a
deterministic Hermitian matrix, `s ≥ 0`, `z` nonreal and `m` with `Im z · Im m ≥ 0` (in the
application `m = ⟨M⟩`, `Im m` of the sign of `Im z`). The characteristic
`z_σ = z + (s - σ) m` (`flowSpectral`) is nonreal for `σ ≤ s` (`flowSpectral_im_ne_zero`), and
`R_σ = (F + G_σ - z_σ)⁻¹` (`flowResolvent`).

**Main result** (`isContinuousSemimartingale_reTr_flowResolvent`): for every matrix `K`, the real
process `t ↦ Re tr(K R_{t ∧ s})` is a continuous semimartingale for `𝓖`
(`IsContinuousSemimartingale`, `d = 1`) with
* drift `1_{t ≤ s} · Re tr(K (⟨R_t⟩ - m) R_t²)`,
* bracket density `1_{t ≤ s} · (1/N) ∑_x (Re tr(K R_t E_x R_t))²`, `E_x = hermBasis x`.
After `s` the process is constant (stopped). Specializations (`K = N⁻¹B`, `-iN⁻¹B`, `y x*`,
`-i y x*`): `isContinuousSemimartingale_avgRe/avgIm/isoRe/isoIm_flowResolvent` for
`Re/Im ⟨R B⟩` (drift `Re/Im (⟨R⟩ - m)⟨R² B⟩`) and `Re/Im x*Ry` (drift `Re/Im (⟨R⟩ - m) x*R²y`).

**Bracket bounds** (deterministic, every matrix `R`): `avgRe_bracket_le`, `avgIm_bracket_le`:
`(1/N) ∑_x (Re/Im ⟨R E_x R B⟩)² ≤ N⁻² Re⟨(RBR)(RBR)ᴴ⟩`; `isoRe_bracket_le`, `isoIm_bracket_le`:
`(1/N) ∑_x (Re/Im x*R E_x R y)² ≤ (1/N) Re(x*RRᴴx) Re(y*RᴴRy)`; general `sum_reTr_sq_le`.

Proof. The state `(hermVec(F + G_t), t) ∈ ℝ^{N·N+1}` (`flowState`) is a continuous
semimartingale with drift `(0, 1)` and covariance `(gueCovVec N, 0)`
(`isContinuousSemimartingale_hermVec` at start `0` plus `appendFV`); it is stopped at the
constant time `s` (`stoppedSemimartingale_holds`), so the time coordinate stays in `[0, s]` and
the state stays in the open set `flowDomain` where `z_{last}` is nonreal. The Itô formula
(`semimartingaleItoFormula_holds`) is applied to the time-independent `C²` function
`flowTest K (t, y) = Re tr(K (vecHerm(blk y) - z_{last y})⁻¹)`. Its derivatives give: the time
direction `-m R²`, i.e. `∂_σR = R ż R` with `ż = -m`; the second-order term
`½ (1/N) ∑_x 2 R E_x R E_x R = ⟨R⟩ R²` from `∑_x E_x X E_x = tr(X) · 1`
(`sum_hermBasis_mul_mul`, the coordinates `hermVec` being orthonormal for `tr(AB)` with
covariance `(1/N) I`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Flow
open MeasureTheory ProbabilityTheory Matrix Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal ENNReal ComplexConjugate

variable {N : ℕ}

/-!
### The characteristic and the state coordinates
-/

/-- The characteristic `z_σ = z + (s - σ) m`. -/
def flowSpectral (z m : ℂ) (s σ : ℝ) : ℂ := z + ((s - σ : ℝ) : ℂ) * m

theorem flowSpectral_im (z m : ℂ) (s σ : ℝ) :
    (flowSpectral z m s σ).im = z.im + (s - σ) * m.im := by
  simp [flowSpectral]

/-- The characteristic stays nonreal before time `s` when `Im m` has the sign of `Im z`
(`Im z · Im m ≥ 0`, which allows `Im m = 0`). -/
theorem flowSpectral_im_ne_zero {z m : ℂ} (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) {s σ : ℝ}
    (hσ : σ ≤ s) : (flowSpectral z m s σ).im ≠ 0 := by
  rw [flowSpectral_im]
  intro h
  have h1 : 0 < z.im * z.im := mul_self_pos.mpr hz
  have h2 : 0 ≤ (s - σ) * (z.im * m.im) := mul_nonneg (by linarith) hm
  have h3 : z.im * (z.im + (s - σ) * m.im) = 0 := by rw [h, mul_zero]
  nlinarith

/-- The flow resolvent `R_σ = (F + G_σ - z_σ)⁻¹`. -/
def flowResolvent {Ω : Type*} (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s σ : ℝ≥0) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℂ :=
  (F + G σ ω - flowSpectral z m s σ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- Matrix block of the state `y ∈ ℝ^{N·N + 1}` (`finSumFinEquiv` layout). -/
def flowBlk (y : Fin (N * N + 1) → ℝ) : Fin (N * N) → ℝ := fun k => y (finSumFinEquiv (Sum.inl k))

/-- Time coordinate of the state. -/
def flowLast (y : Fin (N * N + 1) → ℝ) : ℝ := y (finSumFinEquiv (Sum.inr 0))

@[simp] theorem flowBlk_sumVec (a : Fin (N * N) → ℝ) (b : Fin 1 → ℝ) :
    flowBlk (sumVec a b) = a := by
  funext k; simp [flowBlk, sumVec]

@[simp] theorem flowLast_sumVec (a : Fin (N * N) → ℝ) (b : Fin 1 → ℝ) :
    flowLast (sumVec a b) = b 0 := by
  simp [flowLast, sumVec]

theorem vecHerm_add (a b : Fin (N * N) → ℝ) : vecHerm N (a + b) = vecHerm N a + vecHerm N b := by
  simp only [vecHerm, hermOfCoord, Pi.add_apply, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]

theorem vecHerm_smul (r : ℝ) (a : Fin (N * N) → ℝ) : vecHerm N (r • a) = r • vecHerm N a := by
  simp only [vecHerm, hermOfCoord, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_smul, Complex.coe_smul]

theorem vecHerm_zero : vecHerm N 0 = 0 := by
  simp [vecHerm, hermOfCoord]

theorem vecHerm_single (k : Fin (N * N)) :
    vecHerm N (Pi.single k 1) = hermBasis (finProdFinEquiv.symm k) := by
  unfold vecHerm hermOfCoord
  rw [Finset.sum_eq_single (finProdFinEquiv.symm k)]
  · simp only [Equiv.apply_symm_apply, Pi.single_eq_same, Complex.ofReal_one, one_smul]
  · intro x _ hx
    change (((Pi.single k (1 : ℝ) : Fin (N * N) → ℝ) (finProdFinEquiv x) : ℝ) : ℂ) •
      hermBasis x = 0
    rw [Pi.single_apply, ite_eq_right]
    · simp
    · intro h; exact hx (by rw [← h]; simp)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Linear part of the state-to-matrix map: `(t, y) ↦ vecHerm(blk y) + (last y) m · 1`. -/
def flowLin (N : ℕ) (m : ℂ) : ℝ × (Fin (N * N + 1) → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := vecHerm N (flowBlk p.2) + ((flowLast p.2 : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ)
  map_add' p q := by
    have : flowBlk (p + q).2 = flowBlk p.2 + flowBlk q.2 := rfl
    rw [this, vecHerm_add]
    simp only [flowLast, Prod.snd_add, Pi.add_apply, Complex.ofReal_add, add_mul, add_smul]
    abel
  map_smul' r p := by
    have : flowBlk (r • p).2 = r • flowBlk p.2 := rfl
    rw [this, vecHerm_smul]
    simp only [flowLast, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      RingHom.id_apply, smul_add, mul_assoc, mul_smul, Complex.coe_smul]

/-- Constant part `-(z + s m) · 1`. -/
def flowBase (N : ℕ) (z m : ℂ) (s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  -((z + (s : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ))

theorem flowBase_add_flowLin (z m : ℂ) (s : ℝ) (p : ℝ × (Fin (N * N + 1) → ℝ)) :
    flowBase N z m s + flowLin N m p =
      vecHerm N (flowBlk p.2) - flowSpectral z m s (flowLast p.2) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  change -((z + (s : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ)) +
      (vecHerm N (flowBlk p.2) + ((flowLast p.2 : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ)) =
    vecHerm N (flowBlk p.2) - (z + ((s - flowLast p.2 : ℝ) : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ)
  rw [show (z + ((s - flowLast p.2 : ℝ) : ℂ) * m) = (z + (s : ℂ) * m) - (flowLast p.2 : ℂ) * m by
    push_cast; ring, sub_smul]
  abel

theorem flowLin_time (m : ℂ) : flowLin N m (1, 0) = 0 := by
  have h : flowBlk (0 : Fin (N * N + 1) → ℝ) = 0 := rfl
  simp [flowLin, flowLast, h, vecHerm_zero]

theorem flowLin_blk (m : ℂ) (k : Fin (N * N)) :
    flowLin N m (0, Pi.single (finSumFinEquiv (Sum.inl k)) 1) =
      hermBasis (finProdFinEquiv.symm k) := by
  have h1 : flowBlk (Pi.single (finSumFinEquiv (Sum.inl k)) (1 : ℝ) : Fin (N * N + 1) → ℝ) =
      Pi.single k 1 := by
    funext j
    simp only [flowBlk, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
  have h2 : flowLast (Pi.single (finSumFinEquiv (Sum.inl k)) (1 : ℝ) : Fin (N * N + 1) → ℝ) =
      0 := by
    simp only [flowLast]
    rw [Pi.single_apply, ite_eq_right (finSumFinEquiv.injective.ne (by simp))]
  simp only [flowLin, LinearMap.coe_mk, AddHom.coe_mk, h1, h2, vecHerm_single]
  simp

theorem flowLin_last (m : ℂ) :
    flowLin N m (0, Pi.single (finSumFinEquiv (Sum.inr 0)) 1) =
      m • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have h1 : flowBlk (Pi.single (finSumFinEquiv (Sum.inr 0)) (1 : ℝ) : Fin (N * N + 1) → ℝ) =
      0 := by
    funext j
    simp only [flowBlk]
    rw [Pi.single_apply, ite_eq_right (finSumFinEquiv.injective.ne (by simp))]
    rfl
  have h2 : flowLast (Pi.single (finSumFinEquiv (Sum.inr 0)) (1 : ℝ) : Fin (N * N + 1) → ℝ) =
      1 := by
    simp [flowLast]
  simp only [flowLin, LinearMap.coe_mk, AddHom.coe_mk, h1, h2, vecHerm_zero]
  simp

/-!
### The test function and its derivatives
-/

/-- Open domain of the state: the characteristic at the time coordinate is nonreal. -/
def flowDomain (N : ℕ) (z m : ℂ) (s : ℝ) : Set (Fin (N * N + 1) → ℝ) :=
  {y | (flowSpectral z m s (flowLast y)).im ≠ 0}

theorem isOpen_flowDomain (z m : ℂ) (s : ℝ) : IsOpen (flowDomain N z m s) := by
  have hc : Continuous fun y : Fin (N * N + 1) → ℝ => (flowSpectral z m s (flowLast y)).im := by
    simp only [flowSpectral_im, flowLast]
    fun_prop
  exact isOpen_ne.preimage hc

/-- Resolvent of a state `y`: `(vecHerm(blk y) - z_{last y})⁻¹`. -/
def flowR (z m : ℂ) (s : ℝ) (y : Fin (N * N + 1) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (vecHerm N (flowBlk y) - flowSpectral z m s (flowLast y) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- The Itô test function `(t, y) ↦ Re tr(K R(y))` (time-independent). -/
def flowTest (K : Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s : ℝ) :
    ℝ × (Fin (N * N + 1) → ℝ) → ℝ :=
  invTest (flowBase N z m s) (flowLin N m) K

theorem flowTest_apply (K : Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s : ℝ)
    (p : ℝ × (Fin (N * N + 1) → ℝ)) : flowTest K z m s p = reTr K (flowR z m s p.2) := by
  simp only [flowTest, invTest, flowBase_add_flowLin, flowR]

theorem flowBase_add_flowLin_inv (z m : ℂ) (s : ℝ) (p : ℝ × (Fin (N * N + 1) → ℝ)) :
    (flowBase N z m s + flowLin N m p)⁻¹ = flowR z m s p.2 := by
  rw [flowBase_add_flowLin]; rfl

theorem isUnit_flow {z m : ℂ} {s : ℝ} {y : Fin (N * N + 1) → ℝ} (hy : y ∈ flowDomain N z m s)
    (t : ℝ) : IsUnit (flowBase N z m s + flowLin N m (t, y)).det := by
  rw [flowBase_add_flowLin]
  exact BlockBand.Palm.CoarseRelative.hermitian_shift_det_isUnit (vecHerm_isHermitian _) hy

theorem flowTest_contDiffOn (K : Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s : ℝ) :
    ContDiffOn ℝ 2 (flowTest K z m s) (Set.univ ×ˢ flowDomain N z m s) := fun p hp =>
  (contDiffAt_invTest _ _ K (isUnit_flow (z := z) (m := m) (s := s) hp.2 p.1)).contDiffWithinAt

variable {K : Matrix (Fin N) (Fin N) ℂ} {z m : ℂ} {s : ℝ} {y : Fin (N * N + 1) → ℝ}

theorem partialTime_flowTest (hy : y ∈ flowDomain N z m s) (t : ℝ) :
    partialTime (flowTest K z m s) (t, y) = 0 := by
  unfold partialTime flowTest
  rw [fderiv_invTest _ _ K (isUnit_flow hy t), flowLin_time]
  simp [reTr]

theorem partialSpace_flowTest_blk (hy : y ∈ flowDomain N z m s) (t : ℝ) (k : Fin (N * N)) :
    partialSpace (flowTest K z m s) (t, y) (finSumFinEquiv (Sum.inl k)) =
      -reTr K (flowR z m s y * hermBasis (finProdFinEquiv.symm k) * flowR z m s y) := by
  unfold partialSpace flowTest
  rw [fderiv_invTest _ _ K (isUnit_flow hy t), flowLin_blk, flowBase_add_flowLin_inv]

theorem partialSpace_flowTest_last (hy : y ∈ flowDomain N z m s) (t : ℝ) :
    partialSpace (flowTest K z m s) (t, y) (finSumFinEquiv (Sum.inr 0)) =
      -reTr K (flowR z m s y * (m • (1 : Matrix (Fin N) (Fin N) ℂ)) * flowR z m s y) := by
  unfold partialSpace flowTest
  rw [fderiv_invTest _ _ K (isUnit_flow hy t), flowLin_last, flowBase_add_flowLin_inv]

theorem partialSpace2_flowTest_blk (hy : y ∈ flowDomain N z m s) (t : ℝ) (k l : Fin (N * N)) :
    partialSpace2 (flowTest K z m s) (t, y) (finSumFinEquiv (Sum.inl k))
        (finSumFinEquiv (Sum.inl l)) =
      reTr K (flowR z m s y * hermBasis (finProdFinEquiv.symm k) * flowR z m s y *
          hermBasis (finProdFinEquiv.symm l) * flowR z m s y +
        flowR z m s y * hermBasis (finProdFinEquiv.symm l) * flowR z m s y *
          hermBasis (finProdFinEquiv.symm k) * flowR z m s y) := by
  unfold partialSpace2 flowTest
  rw [fderiv_fderiv_invTest _ _ K (isUnit_flow hy t), flowLin_blk, flowLin_blk,
    flowBase_add_flowLin_inv]

/-!
### Itô drift and bracket of the test function
-/

theorem sum_fin_split (f : Fin (N * N + 1) → ℝ) :
    ∑ i, f i = ∑ k, f (finSumFinEquiv (Sum.inl k)) + f (finSumFinEquiv (Sum.inr 0)) := by
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_one]

@[simp] theorem blockCov_inl_inl (A : Matrix (Fin (N * N)) (Fin (N * N)) ℝ) (a b : Fin (N * N)) :
    blockCov (e := 1) A (finSumFinEquiv (Sum.inl a)) (finSumFinEquiv (Sum.inl b)) = A a b := by
  simp [blockCov]

@[simp] theorem blockCov_inl_inr (A : Matrix (Fin (N * N)) (Fin (N * N)) ℝ) (a : Fin (N * N))
    (b : Fin 1) : blockCov (e := 1) A (finSumFinEquiv (Sum.inl a)) (finSumFinEquiv (Sum.inr b)) = 0 := by
  simp [blockCov]

@[simp] theorem blockCov_inr (A : Matrix (Fin (N * N)) (Fin (N * N)) ℝ) (a : Fin 1)
    (j : Fin (N * N + 1)) : blockCov (e := 1) A (finSumFinEquiv (Sum.inr a)) j = 0 := by
  simp [blockCov]

@[simp] theorem sumVec_inl (a : Fin (N * N) → ℝ) (b : Fin 1 → ℝ) (k : Fin (N * N)) :
    sumVec a b (finSumFinEquiv (Sum.inl k)) = a k := by simp [sumVec]

@[simp] theorem sumVec_inr (a : Fin (N * N) → ℝ) (b : Fin 1 → ℝ) (k : Fin 1) :
    sumVec a b (finSumFinEquiv (Sum.inr k)) = b k := by simp [sumVec]

/-- Reindexing of the basis sum from `Fin (N * N)` to `Fin N × Fin N`. -/
theorem sum_hermBasis_reindex {M : Type*} [AddCommMonoid M] (f : Matrix (Fin N) (Fin N) ℂ → M) :
    ∑ k : Fin (N * N), f (hermBasis (finProdFinEquiv.symm k)) = ∑ x, f (hermBasis x) :=
  finProdFinEquiv.symm.sum_comp (fun x => f (hermBasis x))

/-- **Itô drift** of `Re tr(K R)` before time `s` (drift `(0, 1)`, covariance `(gueCovVec, 0)`):
`Re tr(K (⟨R⟩ - m) R²)`. -/
theorem itoDrift_flowTest (hy : y ∈ flowDomain N z m s) (t : ℝ≥0) :
    itoDrift (flowTest K z m s) y t (sumVec 0 fun _ => 1) (blockCov (gueCovVec N)) =
      reTr K ((BlockBand.External.CEH.normalizedTrace (flowR z m s y) - m) •
        (flowR z m s y * flowR z m s y)) := by
  set R := flowR z m s y
  unfold itoDrift
  rw [partialTime_flowTest hy, sum_fin_split, sum_fin_split]
  simp only [sumVec_inl, sumVec_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    one_mul, blockCov_inr, sum_fin_split (fun j => blockCov _ _ j * _), blockCov_inl_inl,
    blockCov_inl_inr, add_zero, gueCovVec_apply, ite_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [partialSpace_flowTest_last hy]
  simp only [partialSpace2_flowTest_blk hy]
  have hsum : ∑ k : Fin (N * N), 1 / (N : ℝ) * reTr K (R * hermBasis (finProdFinEquiv.symm k) * R *
      hermBasis (finProdFinEquiv.symm k) * R + R * hermBasis (finProdFinEquiv.symm k) * R *
      hermBasis (finProdFinEquiv.symm k) * R) =
      2 * reTr K (((1 / (N : ℝ) : ℝ) : ℂ) • (R.trace • (R * R))) := by
    rw [sum_hermBasis_reindex (fun E => 1 / (N : ℝ) * reTr K (R * E * R * E * R + R * E * R * E * R)),
      reTr_ofReal_smul]
    have e : R.trace • (R * R) = ∑ x, R * hermBasis x * R * hermBasis x * R := by
      calc R.trace • (R * R) = R * (R.trace • (1 : Matrix (Fin N) (Fin N) ℂ)) * R := by
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        _ = R * (∑ x, hermBasis x * R * hermBasis x) * R := by rw [sum_hermBasis_mul_mul]
        _ = _ := by
            rw [Finset.mul_sum, Finset.sum_mul]
            simp only [Matrix.mul_assoc]
    rw [e, reTr_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [reTr_add]; ring
  rw [hsum]
  have e1 : -reTr K (R * (m • (1 : Matrix (Fin N) (Fin N) ℂ)) * R) +
      1 / 2 * (2 * reTr K (((1 / (N : ℝ) : ℝ) : ℂ) • (R.trace • (R * R)))) =
      reTr K (-(R * (m • (1 : Matrix (Fin N) (Fin N) ℂ)) * R) +
        ((1 / (N : ℝ) : ℝ) : ℂ) • (R.trace • (R * R))) := by
    rw [reTr_add, reTr_neg]; ring
  rw [e1]
  congr 1
  unfold BlockBand.External.CEH.normalizedTrace
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, sub_smul, smul_smul]
  push_cast
  rw [one_div]
  abel

/-- **Itô bracket** of `Re tr(K R)` before time `s`: `(1/N) ∑_x (Re tr(K R E_x R))²`. -/
theorem itoBracket_flowTest (hy : y ∈ flowDomain N z m s) (t : ℝ≥0) :
    itoBracket (flowTest K z m s) y t (blockCov (gueCovVec N)) =
      1 / (N : ℝ) * ∑ x, reTr K (flowR z m s y * hermBasis x * flowR z m s y) ^ 2 := by
  unfold itoBracket
  rw [sum_fin_split]
  simp only [blockCov_inr, zero_mul, Finset.sum_const_zero, add_zero,
    sum_fin_split (fun j => blockCov _ _ j * _ * _), blockCov_inl_inl, blockCov_inl_inr,
    gueCovVec_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    partialSpace_flowTest_blk hy]
  rw [sum_hermBasis_reindex (fun E => 1 / (N : ℝ) * -reTr K (flowR z m s y * E * flowR z m s y) *
    -reTr K (flowR z m s y * E * flowR z m s y)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- After the stopping time the characteristics vanish and so does the Itô drift. -/
theorem itoDrift_flowTest_zero (hy : y ∈ flowDomain N z m s) (t : ℝ≥0) :
    itoDrift (flowTest K z m s) y t 0 0 = 0 := by
  simp [itoDrift, partialTime_flowTest hy]

theorem itoBracket_zero (φ : ℝ × (Fin (N * N + 1) → ℝ) → ℝ) (t : ℝ≥0) :
    itoBracket φ y t 0 = 0 := by
  simp [itoBracket]

/-!
### Measurability
-/

theorem measurable_matrix_inv' :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hdet : Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => A.det) :=
    continuous_id.matrix_det.measurable
  have hadj : Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => A.adjugate i j) :=
    (((measurable_pi_apply j).comp (measurable_pi_apply i) :
      Measurable fun M : Matrix (Fin N) (Fin N) ℂ => M i j)).comp continuous_id.matrix_adjugate.measurable
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hdet.inv.mul hadj

theorem continuous_reTr (K : Matrix (Fin N) (Fin N) ℂ) :
    Continuous (reTr K : Matrix (Fin N) (Fin N) ℂ → ℝ) :=
  Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace

theorem measurable_flowTest (K : Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s : ℝ) :
    Measurable (flowTest K z m s) := by
  have hc : Continuous fun p : ℝ × (Fin (N * N + 1) → ℝ) =>
      vecHerm N (flowBlk p.2) - flowSpectral z m s (flowLast p.2) •
        (1 : Matrix (Fin N) (Fin N) ℂ) := by
    have hb : Continuous fun p : ℝ × (Fin (N * N + 1) → ℝ) => flowBlk p.2 :=
      continuous_pi fun k => (continuous_apply _).comp continuous_snd
    have hl : Continuous fun p : ℝ × (Fin (N * N + 1) → ℝ) => flowLast p.2 :=
      (continuous_apply _).comp continuous_snd
    have hs : Continuous fun p : ℝ × (Fin (N * N + 1) → ℝ) => flowSpectral z m s (flowLast p.2) := by
      simp only [flowSpectral]
      fun_prop
    exact (continuous_vecHerm.comp hb).sub (hs.smul continuous_const)
  have h : flowTest K z m s = fun p => reTr K (flowR z m s p.2) := funext (flowTest_apply K z m s)
  rw [h]
  exact (continuous_reTr K).measurable.comp (measurable_matrix_inv'.comp hc.measurable)

/-!
### Averaged and isotropic functionals
-/

open BlockBand.External.CEH (normalizedTrace)

theorem normalizedTrace_eq (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace A = (N : ℂ)⁻¹ * A.trace := rfl

theorem reTr_smul_eq (c : ℂ) (B X : Matrix (Fin N) (Fin N) ℂ) :
    reTr (c • B) X = (c * trace (X * B)).re := by
  rw [reTr, Matrix.smul_mul, trace_smul, smul_eq_mul, trace_mul_comm]

theorem reTr_avgRe (B X : Matrix (Fin N) (Fin N) ℂ) :
    reTr ((N : ℂ)⁻¹ • B) X = (normalizedTrace (X * B)).re := by
  rw [reTr_smul_eq]; rfl

theorem reTr_avgIm (B X : Matrix (Fin N) (Fin N) ℂ) :
    reTr ((-Complex.I * (N : ℂ)⁻¹) • B) X = (normalizedTrace (X * B)).im := by
  rw [reTr_smul_eq, normalizedTrace_eq, mul_assoc]
  simp [Complex.mul_re]

theorem trace_vecMulVec_mul (x y : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    trace (vecMulVec y (star x) * X) = star x ⬝ᵥ (X *ᵥ y) := by
  rw [vecMulVec_mul, trace_vecMulVec, dotProduct_comm, dotProduct_mulVec]

theorem reTr_isoRe (x y : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    reTr (vecMulVec y (star x)) X = (star x ⬝ᵥ (X *ᵥ y)).re := by
  rw [reTr, trace_vecMulVec_mul]

theorem reTr_isoIm (x y : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    reTr ((-Complex.I) • vecMulVec y (star x)) X = (star x ⬝ᵥ (X *ᵥ y)).im := by
  rw [reTr, Matrix.smul_mul, trace_smul, trace_vecMulVec_mul, smul_eq_mul]
  simp [Complex.mul_re]

theorem normalizedTrace_smul_mul (a : ℂ) (X B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace ((a • X) * B) = a * normalizedTrace (X * B) := by
  simp only [normalizedTrace_eq, Matrix.smul_mul, trace_smul, smul_eq_mul]; ring

theorem dotProduct_smul_mulVec (a : ℂ) (x y : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    star x ⬝ᵥ ((a • X) *ᵥ y) = a * (star x ⬝ᵥ (X *ᵥ y)) := by
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

/-!
### Bracket bounds
-/

theorem reTr_resolvent_basis (K R : Matrix (Fin N) (Fin N) ℂ) (x : Fin N × Fin N) :
    reTr K (R * hermBasis x * R) = (trace (hermBasis x * (R * K * R))).re := by
  rw [reTr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (K * R), trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-- General bracket bound: `∑_x (Re tr(K R E_x R))² ≤ Re tr((RKR)(RKR)ᴴ)`. -/
theorem sum_reTr_sq_le (K R : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, reTr K (R * hermBasis x * R) ^ 2 ≤ (trace ((R * K * R) * (R * K * R)ᴴ)).re := by
  rw [← sum_normSq_trace]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [reTr_resolvent_basis, sq]
  exact Complex.re_sq_le_normSq _

theorem trace_smul_mul_conjTranspose (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    (trace ((c • M) * (c • M)ᴴ)).re = Complex.normSq c * (trace (M * Mᴴ)).re := by
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, show star c = conj c from rfl, Complex.mul_conj,
    Complex.re_ofReal_mul]

/-- **Averaged bracket bound** (real part): `(1/N) ∑_x (Re⟨R E_x R B⟩)² ≤ N⁻² ⟨(RBR)(RBR)ᴴ⟩`. -/
theorem avgRe_bracket_le (R B : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (R * hermBasis x * R * B)).re ^ 2 ≤
      1 / (N : ℝ) ^ 2 * (normalizedTrace ((R * B * R) * (R * B * R)ᴴ)).re := by
  have e : ∀ x, (normalizedTrace (R * hermBasis x * R * B)).re =
      reTr ((N : ℂ)⁻¹ • B) (R * hermBasis x * R) := fun x => (reTr_avgRe _ _).symm
  simp only [e]
  have h := sum_reTr_sq_le ((N : ℂ)⁻¹ • B) R
  rw [Matrix.mul_smul, Matrix.smul_mul, trace_smul_mul_conjTranspose] at h
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  calc 1 / (N : ℝ) * ∑ x, reTr ((N : ℂ)⁻¹ • B) (R * hermBasis x * R) ^ 2
      ≤ 1 / (N : ℝ) * (Complex.normSq ((N : ℂ)⁻¹) * (trace (R * B * R * (R * B * R)ᴴ)).re) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by
        rw [normalizedTrace_eq, Complex.normSq_inv, Complex.normSq_natCast, ← Complex.ofReal_natCast,
          ← Complex.ofReal_inv, Complex.re_ofReal_mul]
        ring

/-- **Averaged bracket bound** (imaginary part). -/
theorem avgIm_bracket_le (R B : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (R * hermBasis x * R * B)).im ^ 2 ≤
      1 / (N : ℝ) ^ 2 * (normalizedTrace ((R * B * R) * (R * B * R)ᴴ)).re := by
  have e : ∀ x, (normalizedTrace (R * hermBasis x * R * B)).im =
      reTr ((-Complex.I * (N : ℂ)⁻¹) • B) (R * hermBasis x * R) := fun x => (reTr_avgIm _ _).symm
  simp only [e]
  have h := sum_reTr_sq_le ((-Complex.I * (N : ℂ)⁻¹) • B) R
  rw [Matrix.mul_smul, Matrix.smul_mul, trace_smul_mul_conjTranspose] at h
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  calc 1 / (N : ℝ) * ∑ x, reTr ((-Complex.I * (N : ℂ)⁻¹) • B) (R * hermBasis x * R) ^ 2
      ≤ 1 / (N : ℝ) * (Complex.normSq (-Complex.I * (N : ℂ)⁻¹) *
          (trace (R * B * R * (R * B * R)ᴴ)).re) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by
        rw [normalizedTrace_eq, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I, one_mul,
          Complex.normSq_inv, Complex.normSq_natCast, ← Complex.ofReal_natCast,
          ← Complex.ofReal_inv, Complex.re_ofReal_mul]
        ring

theorem dotProduct_star_self_eq (w : Fin N → ℂ) :
    w ⬝ᵥ star w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (w i) = conj (w i) from rfl, Complex.mul_conj]

theorem trace_iso_mul_conjTranspose (R : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    trace ((R * vecMulVec y (star x) * R) * (R * vecMulVec y (star x) * R)ᴴ) =
      (star x ᵥ* R ⬝ᵥ star (star x ᵥ* R)) * ((R *ᵥ y) ⬝ᵥ star (R *ᵥ y)) := by
  rw [mul_vecMulVec, vecMulVec_mul, conjTranspose_vecMulVec, vecMulVec_mul_vecMulVec,
    trace_vecMulVec, dotProduct_smul, smul_eq_mul]

theorem quad_mul_conjTranspose (R : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    star x ⬝ᵥ ((R * Rᴴ) *ᵥ x) = star x ᵥ* R ⬝ᵥ star (star x ᵥ* R) := by
  rw [star_vecMul, star_star, ← mulVec_mulVec, dotProduct_mulVec]

theorem quad_conjTranspose_mul (R : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) :
    star y ⬝ᵥ ((Rᴴ * R) *ᵥ y) = (R *ᵥ y) ⬝ᵥ star (R *ᵥ y) := by
  rw [star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_comm]

/-- **Isotropic bracket bound** (real part):
`(1/N) ∑_x (Re x*(R E_x R)y)² ≤ (1/N) (R Rᴴ)_xx (Rᴴ R)_yy`. -/
theorem isoRe_bracket_le (R : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    1 / (N : ℝ) * ∑ e, (star x ⬝ᵥ ((R * hermBasis e * R) *ᵥ y)).re ^ 2 ≤
      1 / (N : ℝ) * ((star x ⬝ᵥ ((R * Rᴴ) *ᵥ x)).re * (star y ⬝ᵥ ((Rᴴ * R) *ᵥ y)).re) := by
  rw [quad_mul_conjTranspose, quad_conjTranspose_mul, dotProduct_star_self_eq,
    dotProduct_star_self_eq, Complex.ofReal_re, Complex.ofReal_re]
  simp only [← reTr_isoRe]
  have h := sum_reTr_sq_le (vecMulVec y (star x)) R
  rw [trace_iso_mul_conjTranspose, dotProduct_star_self_eq, dotProduct_star_self_eq,
    ← Complex.ofReal_mul, Complex.ofReal_re] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Isotropic bracket bound** (imaginary part). -/
theorem isoIm_bracket_le (R : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    1 / (N : ℝ) * ∑ e, (star x ⬝ᵥ ((R * hermBasis e * R) *ᵥ y)).im ^ 2 ≤
      1 / (N : ℝ) * ((star x ⬝ᵥ ((R * Rᴴ) *ᵥ x)).re * (star y ⬝ᵥ ((Rᴴ * R) *ᵥ y)).re) := by
  rw [quad_mul_conjTranspose, quad_conjTranspose_mul, dotProduct_star_self_eq,
    dotProduct_star_self_eq, Complex.ofReal_re, Complex.ofReal_re]
  simp only [← reTr_isoIm]
  have h := sum_reTr_sq_le ((-Complex.I) • vecMulVec y (star x)) R
  rw [Matrix.mul_smul, Matrix.smul_mul, trace_smul_mul_conjTranspose, Complex.normSq_neg,
    Complex.normSq_I, one_mul, trace_iso_mul_conjTranspose, dotProduct_star_self_eq,
    dotProduct_star_self_eq, ← Complex.ofReal_mul, Complex.ofReal_re] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-!
### The stochastic layer
-/

section Stochastic

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Matrix (Fin N) (Fin N) ℂ}

omit [IsProbabilityMeasure Q] in
theorem shiftFiltration_zero : shiftFiltration 𝓖 0 = 𝓖 := by
  ext1; funext u; simp [shiftFiltration]

/-- The augmented state `(hermVec(F + G_t), t) ∈ ℝ^{N·N + 1}`. -/
def flowState (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (t : ℝ≥0) (ω : Ω) : Fin (N * N + 1) → ℝ :=
  sumVec (hermVec N (F + G t ω)) fun _ => (t : ℝ)

/-- The augmented state is a continuous semimartingale: drift `(0, 1)`, covariance
`(gueCovVec N, 0)`. -/
theorem isContinuousSemimartingale_flowState (hG : IsHermitianBrownian Q 𝓖 N G) :
    IsContinuousSemimartingale Q 𝓖 (flowState F G) (fun _ _ => sumVec 0 fun _ => 1)
      (fun _ _ => blockCov (e := 1) (gueCovVec N)) := by
  have h0 := isContinuousSemimartingale_hermVec hG (F := fun _ => F) measurable_const 0
  simp only [zero_add, shiftFiltration_zero] at h0
  have hZc : Continuous fun t : ℝ≥0 => (fun _ : Fin 1 => (t : ℝ)) :=
    continuous_pi fun _ => NNReal.continuous_coe
  have hZa : ∀ t : ℝ≥0, StronglyMeasurable[𝓖 t] (fun _ : Ω => fun _ : Fin 1 => (t : ℝ)) :=
    fun _ => stronglyMeasurable_const
  have h := BlockBand.Palm.RelativeLocalization.IsContinuousSemimartingale.appendFV h0 (e := 1) (Z := fun t _ _ => (t : ℝ)) (γ := fun _ _ _ => 1) hZa
    (StronglyAdapted.isStronglyProgressive_of_continuous hZa fun _ => hZc)
    (Eventually.of_forall fun _ => hZc) (isStronglyProgressive_const _ _)
    (Eventually.of_forall fun _ _ _ => integrableOn_const (by simp))
    (Eventually.of_forall fun ω t i => by
      simp [smCompensated])
  exact h

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem stoppedProcess_flowState (s : ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (flowState F G) (fun _ => (s : WithTop ℝ≥0)) t ω = flowState F G (min t s) ω := by
  simp only [stoppedProcess]
  rw [← WithTop.coe_min]
  exact congrArg (fun σ => flowState F G σ ω) (WithTop.untopD_coe _ _)

omit [IsProbabilityMeasure Q] in
theorem flowR_flowState (hF : F.IsHermitian) (hG : IsHermitianBrownian Q 𝓖 N G) (z m : ℂ)
    (s σ : ℝ≥0) (ω : Ω) :
    flowR z m s (flowState F G σ ω) = flowResolvent F G z m s σ ω := by
  simp only [flowR, flowState, flowBlk_sumVec, flowLast_sumVec,
    vecHerm_hermVec (hF.add (hG.hermitian σ ω)), flowResolvent]

/-- **Itô formula for `Re tr(K R_σ)` along the characteristic flow**, stopped at `s`.
For a Hermitian Brownian motion `G` (`E|dG_ab|² = dt/N`), deterministic Hermitian `F`, `s ≥ 0`,
nonreal `z` and `m` with `Im z · Im m ≥ 0`, and every matrix `K`, the real process
`t ↦ Re tr(K R_{t ∧ s})`, `R_σ = (F + G_σ - (z + (s - σ) m))⁻¹`, is a continuous semimartingale
for `𝓖` with drift `1_{t ≤ s} Re tr(K (⟨R_t⟩ - m) R_t²)` and bracket density
`1_{t ≤ s} (1/N) ∑_x (Re tr(K R_t E_x R_t))²` (`E_x = hermBasis x`). -/
theorem isContinuousSemimartingale_reTr_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) (s : ℝ≥0)
    (K : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => reTr K (flowResolvent F G z m s (min t s) ω))
      (fun t ω _ => if t ≤ s then
        reTr K ((BlockBand.External.CEH.normalizedTrace (flowResolvent F G z m s t ω) - m) •
          (flowResolvent F G z m s t ω * flowResolvent F G z m s t ω)) else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, reTr K (flowResolvent F G z m s t ω * hermBasis x *
          flowResolvent F G z m s t ω) ^ 2 else 0) := by
  set ρ : Ω → WithTop ℝ≥0 := fun _ => (s : WithTop ℝ≥0)
  have hst := BlockBand.SourceProcess.Stochastic.Semimartingale.stoppedSemimartingale_holds
    (N * N + 1) Ω Q 𝓖 _ _ _ (isContinuousSemimartingale_flowState (F := F) hG) ρ
    (isStoppingTime_const 𝓖 _)
  have hU : ∀ t ω, stoppedProcess (flowState F G) ρ t ω ∈ flowDomain N z m s := by
    intro t ω
    rw [stoppedProcess_flowState]
    simp only [flowDomain, Set.mem_ofPred_eq, flowState, flowLast_sumVec]
    exact flowSpectral_im_ne_zero hz hm (NNReal.coe_le_coe.mpr (min_le_right t s))
  have hito := BlockBand.SourceProcess.Stochastic.SemimartingaleIto.semimartingaleItoFormula_holds
    (N * N + 1) Ω Q 𝓖 _ _ _ hst (flowDomain N z m s) (isOpen_flowDomain z m s)
    (Eventually.of_forall fun ω t => hU t ω) (flowTest K z m s) (measurable_flowTest K z m s)
    (flowTest_contDiffOn K z m s)
  have hsw : ∀ {E : Type} [Zero E] (f : E) (t : ℝ≥0) (ω : Ω),
      switchAfter ρ (fun _ _ => f) t ω = if t ≤ s then f else 0 := by
    intro E _ f t ω
    simp only [switchAfter, ρ, WithTop.coe_le_coe]
  have hR : ∀ t ω, flowR z m s (stoppedProcess (flowState F G) ρ t ω) =
      flowResolvent F G z m s (min t s) ω := by
    intro t ω
    rw [stoppedProcess_flowState, flowR_flowState hF hG]
  have e1 : (fun (t : ℝ≥0) ω (_ : Fin 1) => flowTest K z m s ((t : ℝ), stoppedProcess (flowState F G) ρ t ω))
      = fun t ω _ => reTr K (flowResolvent F G z m s (min t s) ω) := by
    funext t ω i
    rw [flowTest_apply, hR]
  have e2 : (fun (t : ℝ≥0) ω (_ : Fin 1) => itoDrift (flowTest K z m s)
      (stoppedProcess (flowState F G) ρ t ω) t
      (switchAfter ρ (fun _ _ => sumVec 0 fun _ => 1) t ω)
      (switchAfter ρ (fun _ _ => blockCov (e := 1) (gueCovVec N)) t ω)) =
      fun t ω _ => if t ≤ s then
        reTr K ((BlockBand.External.CEH.normalizedTrace (flowResolvent F G z m s t ω) - m) •
          (flowResolvent F G z m s t ω * flowResolvent F G z m s t ω)) else 0 := by
    funext t ω i
    rw [hsw, hsw]
    split_ifs with h
    · rw [itoDrift_flowTest (hU t ω), hR, min_eq_left h]
    · exact itoDrift_flowTest_zero (hU t ω) t
  have e3 : (fun (t : ℝ≥0) ω => Matrix.of fun (_ _ : Fin 1) => itoBracket (flowTest K z m s)
      (stoppedProcess (flowState F G) ρ t ω) t
      (switchAfter ρ (fun _ _ => blockCov (e := 1) (gueCovVec N)) t ω)) =
      fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, reTr K (flowResolvent F G z m s t ω * hermBasis x *
          flowResolvent F G z m s t ω) ^ 2 else 0 := by
    funext t ω
    rw [hsw]
    split_ifs with h
    · rw [itoBracket_flowTest (hU t ω), hR, min_eq_left h]
    · rw [itoBracket_zero]
  rw [e1, e2, e3] at hito
  exact hito

/-- **Averaged, real part**: `t ↦ Re⟨R_{t∧s} B⟩` is a continuous semimartingale with drift
`1_{t≤s} Re((⟨R_t⟩ - m)⟨R_t² B⟩)` and bracket `1_{t≤s} (1/N) ∑_x (Re⟨R_t E_x R_t B⟩)²`
(bounded by `N⁻² ⟨(R_t B R_t)(R_t B R_t)ᴴ⟩`, `avgRe_bracket_le`). -/
theorem isContinuousSemimartingale_avgRe_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) (s : ℝ≥0)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (normalizedTrace (flowResolvent F G z m s (min t s) ω * B)).re)
      (fun t ω _ => if t ≤ s then ((normalizedTrace (flowResolvent F G z m s t ω) - m) *
        normalizedTrace (flowResolvent F G z m s t ω * flowResolvent F G z m s t ω * B)).re else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (normalizedTrace (flowResolvent F G z m s t ω * hermBasis x * flowResolvent F G z m s t ω * B)).re ^ 2
        else 0) := by
  have h := isContinuousSemimartingale_reTr_flowResolvent hG hF hz hm s ((N : ℂ)⁻¹ • B)
  simp only [reTr_avgRe, normalizedTrace_smul_mul] at h
  exact h

/-- **Averaged, imaginary part**: as `isContinuousSemimartingale_avgRe_flowResolvent` with `Im`
(bracket bound `avgIm_bracket_le`). -/
theorem isContinuousSemimartingale_avgIm_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) (s : ℝ≥0)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (normalizedTrace (flowResolvent F G z m s (min t s) ω * B)).im)
      (fun t ω _ => if t ≤ s then ((normalizedTrace (flowResolvent F G z m s t ω) - m) *
        normalizedTrace (flowResolvent F G z m s t ω * flowResolvent F G z m s t ω * B)).im else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (normalizedTrace (flowResolvent F G z m s t ω * hermBasis x * flowResolvent F G z m s t ω * B)).im ^ 2
        else 0) := by
  have h := isContinuousSemimartingale_reTr_flowResolvent hG hF hz hm s
    ((-Complex.I * (N : ℂ)⁻¹) • B)
  simp only [reTr_avgIm, normalizedTrace_smul_mul] at h
  exact h

/-- **Isotropic, real part**: `t ↦ Re x*R_{t∧s}y` is a continuous semimartingale with drift
`1_{t≤s} Re((⟨R_t⟩ - m) x*R_t²y)` and bracket `1_{t≤s} (1/N) ∑_e (Re x*R_t E_e R_t y)²`
(bounded by `(1/N)(R_t R_tᴴ)_xx (R_tᴴ R_t)_yy`, `isoRe_bracket_le`). -/
theorem isContinuousSemimartingale_isoRe_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) (s : ℝ≥0)
    (x y : Fin N → ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (star x ⬝ᵥ (flowResolvent F G z m s (min t s) ω *ᵥ y)).re)
      (fun t ω _ => if t ≤ s then ((normalizedTrace (flowResolvent F G z m s t ω) - m) *
        (star x ⬝ᵥ ((flowResolvent F G z m s t ω * flowResolvent F G z m s t ω) *ᵥ y))).re else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ e, (star x ⬝ᵥ ((flowResolvent F G z m s t ω * hermBasis e * flowResolvent F G z m s t ω) *ᵥ y)).re ^ 2
        else 0) := by
  have h := isContinuousSemimartingale_reTr_flowResolvent hG hF hz hm s (vecMulVec y (star x))
  simp only [reTr_isoRe, dotProduct_smul_mulVec] at h
  exact h

/-- **Isotropic, imaginary part** (bracket bound `isoIm_bracket_le`). -/
theorem isContinuousSemimartingale_isoIm_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) (s : ℝ≥0)
    (x y : Fin N → ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (star x ⬝ᵥ (flowResolvent F G z m s (min t s) ω *ᵥ y)).im)
      (fun t ω _ => if t ≤ s then ((normalizedTrace (flowResolvent F G z m s t ω) - m) *
        (star x ⬝ᵥ ((flowResolvent F G z m s t ω * flowResolvent F G z m s t ω) *ᵥ y))).im else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ e, (star x ⬝ᵥ ((flowResolvent F G z m s t ω * hermBasis e * flowResolvent F G z m s t ω) *ᵥ y)).im ^ 2
        else 0) := by
  have h := isContinuousSemimartingale_reTr_flowResolvent hG hF hz hm s
    ((-Complex.I) • vecMulVec y (star x))
  simp only [reTr_isoIm, dotProduct_smul_mulVec] at h
  exact h

end Stochastic

end BlockBand.Native.CEH.Flow
