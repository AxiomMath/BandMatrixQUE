module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalBlockConditioningReconstruction

/-!
# The normalized physical diagonal block as singleton BlockGUE

The physical diagonal block has variance `c/W`.  This module transports every
one-dimensional Gaussian law and every two-component independence assertion
through division by `sqrt c`, obtaining exactly the singleton `BlockGUE`
normalization `1/W`.

The ordering-sensitive part is mutual independence in `BlockGUE`'s chosen upper
ordering.  The ring and `BlockGUE` laws use different opaque finite orderings,
so transporting the ring upper independence needs an orientation/reindexing
argument.  These fields form `NormalizedDiagonalBlockGUEOrderingTransport`,
proved as `Law.normalizedDiagonalBlockGUEOrderingTransport`.  Given them,
`normalizedDiagonalBlockGUE` constructs the complete standard law on the
original probability space and thereby instantiates
`NormalizedDiagonalBlockGUECoupling`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder ENNReal NNReal

namespace GaussianRing

/-- A singleton BlockGUE index has the physical internal coordinate `x.2`. -/
@[simp] theorem normalizedSingletonBlock_apply
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (x y : BlockGUE.Index (singletonBlockSize p.W)) :
    M.normalizedSingletonBlock j ω x y =
      ((Real.sqrt p.c)⁻¹ : ℂ) * M.H ω (j, x.2) (j, y.2) := rfl

/-- The real part of a normalized entry is the original real part divided by
`sqrt c`. -/
theorem normalizedSingletonBlock_re
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (x y : BlockGUE.Index (singletonBlockSize p.W)) :
    (M.normalizedSingletonBlock j ω x y).re =
      (M.H ω (j, x.2) (j, y.2)).re / Real.sqrt p.c := by
  rw [normalizedSingletonBlock_apply]
  have hs : ((Real.sqrt p.c : ℂ)⁻¹) =
      (((Real.sqrt p.c)⁻¹ : ℝ) : ℂ) := by norm_num
  rw [hs, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [div_eq_mul_inv, mul_comm]

/-- The imaginary part scales by the same real factor. -/
theorem normalizedSingletonBlock_im
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (x y : BlockGUE.Index (singletonBlockSize p.W)) :
    (M.normalizedSingletonBlock j ω x y).im =
      (M.H ω (j, x.2) (j, y.2)).im / Real.sqrt p.c := by
  rw [normalizedSingletonBlock_apply]
  have hs : ((Real.sqrt p.c : ℂ)⁻¹) =
      (((Real.sqrt p.c)⁻¹ : ℝ) : ℂ) := by norm_num
  rw [hs, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [div_eq_mul_inv, mul_comm]

/-- The BlockGUE singleton entry variance is exactly `1/W`. -/
@[simp] theorem singleton_entryVariance
    {W : ℕ} (x y : BlockGUE.Index (singletonBlockSize W)) :
    BlockGUE.entryVariance (singletonBlockSize W) x y = 1 / (W : ℝ) := by
  have hxy : x.1 = y.1 := Subsingleton.elim _ _
  simp [BlockGUE.entryVariance, singletonBlockSize, hxy]

/-- Division by `sqrt c` converts the physical diagonal variance parameter to
BlockGUE's singleton variance parameter. -/
theorem normalized_varianceNNReal
    (p : Params) (j : ZMod p.n) (a b : Fin p.W) :
    varianceNNReal p (j, a) (j, b) /
      ⟨(Real.sqrt p.c) ^ 2, sq_nonneg _⟩ =
      ⟨1 / (p.W : ℝ), one_div_nonneg.mpr (by positivity)⟩ := by
  apply NNReal.eq
  change varianceProfile p (j, a) (j, b) / (Real.sqrt p.c) ^ 2 =
    1 / (p.W : ℝ)
  rw [varianceProfile_diagonalBlock]
  simpa [div_eq_inv_mul] using normalizedDiagonalBlock_variance p

/-- The same normalization sends the physical real/imaginary
half-variance to `1/(2W)`. -/
theorem normalized_halfVarianceNNReal
    (p : Params) (j : ZMod p.n) (a b : Fin p.W) :
    (⟨varianceProfile p (j, a) (j, b) / 2,
      div_nonneg (varianceProfile_nonneg p (j, a) (j, b)) (by norm_num)⟩ : NNReal) /
      ⟨(Real.sqrt p.c) ^ 2, sq_nonneg _⟩ =
      ⟨(1 / (p.W : ℝ)) / 2, div_nonneg (by positivity) (by norm_num)⟩ := by
  apply NNReal.eq
  change (varianceProfile p (j, a) (j, b) / 2) /
      (Real.sqrt p.c) ^ 2 = (1 / (p.W : ℝ)) / 2
  rw [varianceProfile_diagonalBlock]
  have hc : 0 ≤ p.c := p.c_pos.le
  have hs : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  rw [Real.sq_sqrt hc]
  field_simp [p.c_pos.ne', Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.W_pos)]

/-- A normalized diagonal entry has the standard centered Gaussian law of
variance `1/W`. -/
theorem Law.normalizedSingletonBlock_diagonal_re_law
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x : BlockGUE.Index (singletonBlockSize p.W)) :
    HasLaw (fun ω => (M.normalizedSingletonBlock j ω x x).re)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (singletonBlockSize p.W) x x,
          BlockGUE.entryVariance_nonneg (singletonBlockSize_pos p.W_pos) x x⟩)
      M.P := by
  rw [show (fun ω => (M.normalizedSingletonBlock j ω x x).re) =
      (fun ω => (M.H ω (j, x.2) (j, x.2)).re / Real.sqrt p.c) by
    funext ω
    exact normalizedSingletonBlock_re M j ω x x]
  have h := (M.diagonal_re_law (j, x.2)) |> fun h => gaussianReal_div_const h (Real.sqrt p.c)
  convert h using 1
  rw [zero_div]
  apply congrArg (gaussianReal 0)
  apply NNReal.eq
  simp only [singleton_entryVariance, varianceNNReal]
  change 1 / (p.W : ℝ) =
    varianceProfile p (j, x.2) (j, x.2) / (Real.sqrt p.c) ^ 2
  simp only [varianceProfile]
  rw [blockWeight_self, Real.sq_sqrt p.c_pos.le]
  field_simp [p.c_pos.ne', Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.W_pos)]

/-- The normalized diagonal remains real almost surely. -/
theorem Law.normalizedSingletonBlock_diagonal_im_zero
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x : BlockGUE.Index (singletonBlockSize p.W)) :
    ∀ᵐ ω ∂M.P, (M.normalizedSingletonBlock j ω x x).im = 0 := by
  filter_upwards [M.diagonal_im_zero (j, x.2)] with ω hω
  rw [normalizedSingletonBlock_im M j ω x x, hω, zero_div]

/-- Normalization preserves independence of the real and imaginary components
of each strict upper physical entry. -/
theorem Law.normalizedSingletonBlock_components_independent
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x y : BlockGUE.Index (singletonBlockSize p.W))
    (hxy : GaussianRing.siteLE p (j, x.2) (j, y.2))
    (hne : x.2 ≠ y.2) :
    IndepFun (fun ω => (M.normalizedSingletonBlock j ω x y).re)
      (fun ω => (M.normalizedSingletonBlock j ω x y).im) M.P := by
  rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).re) =
      (fun ω => (M.H ω (j, x.2) (j, y.2)).re / Real.sqrt p.c) by
    funext ω
    exact normalizedSingletonBlock_re M j ω x y]
  rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).im) =
      (fun ω => (M.H ω (j, x.2) (j, y.2)).im / Real.sqrt p.c) by
    funext ω
    exact normalizedSingletonBlock_im M j ω x y]
  have h := (M.offdiag_components_independent (j, x.2) (j, y.2)
    hxy (by intro h; exact hne (Prod.mk.inj h).2)).comp
      (measurable_id.div_const (Real.sqrt p.c))
      (measurable_id.div_const (Real.sqrt p.c))
  simpa [Function.comp_def] using h

/-- A normalized strict-upper real component has variance `1/(2W)`. -/
theorem Law.normalizedSingletonBlock_offdiag_re_law
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x y : BlockGUE.Index (singletonBlockSize p.W))
    (hxy : GaussianRing.siteLE p (j, x.2) (j, y.2))
    (hne : x.2 ≠ y.2) :
    HasLaw (fun ω => (M.normalizedSingletonBlock j ω x y).re)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (singletonBlockSize p.W) x y / 2,
          div_nonneg (BlockGUE.entryVariance_nonneg
            (singletonBlockSize_pos p.W_pos) x y) (by norm_num)⟩) M.P := by
  rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).re) =
      (fun ω => (M.H ω (j, x.2) (j, y.2)).re / Real.sqrt p.c) by
    funext ω
    exact normalizedSingletonBlock_re M j ω x y]
  have h := (M.offdiag_re_law (j, x.2) (j, y.2) hxy
    (by intro h; exact hne (Prod.mk.inj h).2)) |> fun h => gaussianReal_div_const h
      (Real.sqrt p.c)
  convert h using 1
  rw [zero_div]
  apply congrArg (gaussianReal 0)
  apply NNReal.eq
  simp only [singleton_entryVariance]
  change (1 / (p.W : ℝ)) / 2 =
    (varianceProfile p (j, x.2) (j, y.2) / 2) / (Real.sqrt p.c) ^ 2
  simp only [varianceProfile]
  rw [blockWeight_self, Real.sq_sqrt p.c_pos.le]
  field_simp [p.c_pos.ne', Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.W_pos)]

/-- A normalized strict-upper imaginary component has variance `1/(2W)`. -/
theorem Law.normalizedSingletonBlock_offdiag_im_law
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x y : BlockGUE.Index (singletonBlockSize p.W))
    (hxy : GaussianRing.siteLE p (j, x.2) (j, y.2))
    (hne : x.2 ≠ y.2) :
    HasLaw (fun ω => (M.normalizedSingletonBlock j ω x y).im)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (singletonBlockSize p.W) x y / 2,
          div_nonneg (BlockGUE.entryVariance_nonneg
            (singletonBlockSize_pos p.W_pos) x y) (by norm_num)⟩) M.P := by
  rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).im) =
      (fun ω => (M.H ω (j, x.2) (j, y.2)).im / Real.sqrt p.c) by
    funext ω
    exact normalizedSingletonBlock_im M j ω x y]
  have h := (M.offdiag_im_law (j, x.2) (j, y.2) hxy
    (by intro h; exact hne (Prod.mk.inj h).2)) |> fun h => gaussianReal_div_const h
      (Real.sqrt p.c)
  convert h using 1
  rw [zero_div]
  apply congrArg (gaussianReal 0)
  apply NNReal.eq
  simp only [singleton_entryVariance]
  change (1 / (p.W : ℝ)) / 2 =
    (varianceProfile p (j, x.2) (j, y.2) / 2) / (Real.sqrt p.c) ^ 2
  simp only [varianceProfile]
  rw [blockWeight_self, Real.sq_sqrt p.c_pos.le]
  field_simp [p.c_pos.ne', Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.W_pos)]

/-- The single ordering-sensitive input not supplied by scalar Gaussian
transport. -/
structure NormalizedDiagonalBlockUpperIndependence
    {p : Params} (M : Law p) (j : ZMod p.n) : Prop where
  upper_independent :
    @iIndepFun M.Ω (BlockGUE.UpperPair (singletonBlockSize p.W)) M.mΩ
      (fun _ => ℂ) (fun _ => Complex.measurableSpace)
      (fun q ω => M.normalizedSingletonBlock j ω q.1.1 q.1.2) M.P

/-- The ordering transport from the ring's upper-triangular coordinates to
`BlockGUE`'s independently chosen upper ordering (proved as
`Law.normalizedDiagonalBlockGUEOrderingTransport`).  Every scalar Gaussian
normalization is proved above; this record contains only the
assertions whose indices can be reversed by the mismatch of the two opaque
finite orderings. -/
structure NormalizedDiagonalBlockGUEOrderingTransport
    {p : Params} (M : Law p) (j : ZMod p.n) : Prop
    extends NormalizedDiagonalBlockUpperIndependence M j where
  offdiag_components_independent : ∀ x y,
    BlockGUE.indexLE (singletonBlockSize p.W) x y → x ≠ y → x.1 = y.1 →
    IndepFun (fun ω => (M.normalizedSingletonBlock j ω x y).re)
      (fun ω => (M.normalizedSingletonBlock j ω x y).im) M.P
  offdiag_re_law : ∀ x y,
    BlockGUE.indexLE (singletonBlockSize p.W) x y → x ≠ y → x.1 = y.1 →
    HasLaw (fun ω => (M.normalizedSingletonBlock j ω x y).re)
      (gaussianReal 0 ⟨BlockGUE.entryVariance (singletonBlockSize p.W) x y / 2,
        div_nonneg (BlockGUE.entryVariance_nonneg
          (singletonBlockSize_pos p.W_pos) x y) (by norm_num)⟩) M.P
  offdiag_im_law : ∀ x y,
    BlockGUE.indexLE (singletonBlockSize p.W) x y → x ≠ y → x.1 = y.1 →
    HasLaw (fun ω => (M.normalizedSingletonBlock j ω x y).im)
      (gaussianReal 0 ⟨BlockGUE.entryVariance (singletonBlockSize p.W) x y / 2,
        div_nonneg (BlockGUE.entryVariance_nonneg
          (singletonBlockSize_pos p.W_pos) x y) (by norm_num)⟩) M.P

/-- Given only the ordering-transport data, the normalized physical diagonal
block is a complete standard singleton `BlockGUE.Law` on the original sample
space. -/
def Law.normalizedDiagonalBlockGUE
    {p : Params} (M : Law p) (j : ZMod p.n)
    (h : NormalizedDiagonalBlockGUEOrderingTransport M j) :
    BlockGUE.Law (singletonBlockSize p.W)
      (singletonBlockSize_pos p.W_pos) where
  Ω := M.Ω
  mΩ := M.mΩ
  P := M.P
  probability := M.probability
  G := M.normalizedSingletonBlock j
  hermitian := M.normalizedSingletonBlock_isHermitian j
  measurable_entry := fun x y =>
    (Matrix.measurable_iff.mp (M.measurable_normalizedSingletonBlock j)) x y
  block_diagonal := by
    intro x y hxy
    exact (hxy (Subsingleton.elim _ _)).elim
  upper_independent := h.upper_independent
  diagonal_im_zero := M.normalizedSingletonBlock_diagonal_im_zero j
  diagonal_re_law := M.normalizedSingletonBlock_diagonal_re_law j
  offdiag_components_independent := h.offdiag_components_independent
  offdiag_re_law := h.offdiag_re_law
  offdiag_im_law := h.offdiag_im_law

/-- The constructed standard law realizes the exact coupling interface from
the reconstruction module, with identity distribution witnessed on the same
probability space. -/
def normalizedDiagonalBlockGUECoupling
    {p : Params} (M : Law p) (j : ZMod p.n)
    (h : NormalizedDiagonalBlockGUEOrderingTransport M j) :
    NormalizedDiagonalBlockGUECoupling M j where
  exposed := M.normalizedDiagonalBlockGUE j h
  identDistrib := IdentDistrib.refl
    (M.measurable_normalizedSingletonBlock j).aemeasurable

end GaussianRing

end CoareaNative.BlockBand
