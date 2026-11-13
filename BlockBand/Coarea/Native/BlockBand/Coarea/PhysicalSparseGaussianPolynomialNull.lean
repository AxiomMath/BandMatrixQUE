module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalPairMassLaw
public import BlockBand.Coarea.Native.BlockBand.Coarea.HermitianDiscriminantReal
public import BlockBand.Coarea.Native.BlockBand.Coarea.LagrangeProjectorCorrectness
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalMovingSchurCover
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalCoareaExceptionalNull
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalEigenvectorMassProfileMeasurable
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial nullity for the sparse physical Gaussian ring

The physical ring law `GaussianRing.Law` is not
absolutely continuous on the space of all Hermitian matrices: entries between blocks
that are neither equal nor cyclically adjacent have variance zero.  This file proves
that the exceptional events of the eigenpair coarea argument are
nevertheless null for this law.

* The *active* real coordinates are the diagonal real parts and the real and imaginary
  parts of the strict upper entries of nonzero variance.  From the independence
  field of `GaussianRing.Law` their joint law is the product of nondegenerate
  centred Gaussians (`Law.hasLaw_physicalActiveCoordinates`), hence absolutely
  continuous with respect to Lebesgue measure on the active coordinates, and almost
  surely the physical matrix is the band reconstruction of these coordinates
  (`Law.ae_physicalReconstruction_eq`).
* Any complex polynomial in the active coordinates which is nonzero at one real point
  is almost surely nonzero (`Law.ae_eval_ne_zero_of_witness`).  This is applied to the
  discriminant (witness: a diagonal matrix with distinct entries), to a fixed-energy
  exterior determinant (witness: a constant diagonal), and to the resultant of the full
  and exterior characteristic polynomials (witness: a path matrix whose unit
  nearest-neighbour couplings join the exposed block to every exterior site).

The resultant is a polynomial in *all* active coordinates, couplings included; no
statement is made on a fixed fibre of the off-diagonal coordinates (on the fibre of
zero couplings the full and exterior spectra do intersect).

Main results, for every `M : GaussianRing.Law p` (fixed `n ≥ 4`, `W ≥ 1`,
`0 < b < 1/2`, `c = 1 - 2b`, normalization `H / sqrt c` of the coarea modules, exposed
block `j`, all ordered ranks simultaneously; no limit):

* `Law.ae_charpoly_separable`, `Law.ae_mem_physicalFullSimpleSpectrumEvent`: full
  simple spectrum almost surely;
* `Law.ae_det_physicalExteriorPencil_ne_zero`: a fixed deterministic energy is almost
  surely not an exterior pole;
* `Law.ae_isCoprime_normalizedPhysical_exterior_charpoly`,
  `Law.ae_mem_physicalCommonSpectrumFreeEvent`: almost surely no eigenvalue of the full
  normalized matrix is an eigenvalue of the exterior minor outside block `j`;
* `Law.ae_mem_physicalSelectedExposedMassPositiveEvent`,
  `Law.ae_physicalOrderedPairMass_pos`: positive exposed and pair masses;
* `Law.ae_mem_physicalCoareaGoodEvent`, `Law.measure_physicalCoareaGoodEvent`: the good
  event of `PhysicalCoareaExceptionalNull` has probability one.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The upper site pairs form a finite type. -/
instance upperPairFintype (p : Params) : Fintype (UpperPair p) := by
  unfold UpperPair
  infer_instance

/-- Real coordinate labels of the physical upper triangle: an upper site pair and a
component flag (`false` = real part, `true` = imaginary part). -/
abbrev PhysicalRealCoordinate (p : Params) := UpperPair p × Bool

/-- Variance of one real physical coordinate.  A diagonal entry has real part of
variance `c/W` (in fact `varianceProfile`) and no imaginary part; a strict upper entry
of total variance `s` has two components of variance `s/2`.  Off the band, `s = 0`. -/
def physicalCoordinateVariance (p : Params) (c : PhysicalRealCoordinate p) : NNReal :=
  if c.1.1.1 = c.1.1.2 then (if c.2 then 0 else varianceNNReal p c.1.1.1 c.1.1.2)
  else ⟨varianceProfile p c.1.1.1 c.1.1.2 / 2,
    div_nonneg (varianceProfile_nonneg p _ _) (by norm_num)⟩

/-- The real-valued component map attached to a coordinate label. -/
def physicalCoordinateMap (p : Params) (c : PhysicalRealCoordinate p) : ℂ → ℝ :=
  if c.2 then (if c.1.1.1 = c.1.1.2 then fun _ => 0 else Complex.im) else Complex.re

theorem measurable_physicalCoordinateMap (p : Params) (c : PhysicalRealCoordinate p) :
    Measurable (physicalCoordinateMap p c) := by
  unfold physicalCoordinateMap
  split_ifs
  · exact measurable_const
  · exact Complex.measurable_im
  · exact Complex.measurable_re

/-- The real physical coordinate of the sampled ring matrix. -/
def Law.physicalCoordinate {p : Params} (M : Law p) (c : PhysicalRealCoordinate p)
    (ω : M.Ω) : ℝ :=
  physicalCoordinateMap p c (M.H ω c.1.1.1 c.1.1.2)

theorem Law.measurable_physicalCoordinate {p : Params} (M : Law p)
    (c : PhysicalRealCoordinate p) : Measurable (M.physicalCoordinate c) :=
  (measurable_physicalCoordinateMap p c).comp (M.measurable_entry _ _)

/-- Each real physical coordinate is a centred Gaussian with the displayed variance
(a Dirac mass at zero when the variance vanishes). -/
theorem Law.hasLaw_physicalCoordinate {p : Params} (M : Law p)
    (c : PhysicalRealCoordinate p) :
    HasLaw (M.physicalCoordinate c) (gaussianReal 0 (physicalCoordinateVariance p c)) M.P := by
  obtain ⟨⟨⟨x, y⟩, hxy⟩, b⟩ := c
  by_cases hd : x = y
  · subst hd
    cases b
    · have hf : M.physicalCoordinate (⟨(x, x), hxy⟩, false) =
          fun ω => (M.H ω x x).re := rfl
      rw [hf]
      simpa [physicalCoordinateVariance] using M.diagonal_re_law x
    · have hf : M.physicalCoordinate (⟨(x, x), hxy⟩, true) = fun _ => 0 := by
        funext ω
        simp [Law.physicalCoordinate, physicalCoordinateMap]
      rw [hf]
      refine ⟨measurable_const.aemeasurable, ?_⟩
      simp [physicalCoordinateVariance, Measure.map_const, gaussianReal_zero_var]
  · cases b
    · have hf : M.physicalCoordinate (⟨(x, y), hxy⟩, false) =
          fun ω => (M.H ω x y).re := rfl
      rw [hf]
      simpa [physicalCoordinateVariance, hd] using M.offdiag_re_law x y hxy hd
    · have hf : M.physicalCoordinate (⟨(x, y), hxy⟩, true) =
          fun ω => (M.H ω x y).im := by
        funext ω
        simp [Law.physicalCoordinate, physicalCoordinateMap, hd]
      rw [hf]
      simpa [physicalCoordinateVariance, hd] using M.offdiag_im_law x y hxy hd

/-- Splitting independent random elements into two independent real components each
yields an independent real family indexed by `ι × Bool`. -/
theorem iIndepFun_pairComponents {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ∀ i, Ω → β i) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (φ : ∀ i, Bool → β i → ℝ) (hφ : ∀ i b, Measurable (φ i b))
    (hpair : ∀ i, IndepFun (fun ω => φ i false (Y i ω)) (fun ω => φ i true (Y i ω)) P) :
    iIndepFun (fun c : ι × Bool => fun ω => φ c.1 c.2 (Y c.1 ω)) P := by
  classical
  set Z : ι × Bool → Ω → ℝ := fun c ω => φ c.1 c.2 (Y c.1 ω)
  have hZ : ∀ c, Measurable (Z c) := fun c => (hφ c.1 c.2).comp (hY c.1)
  rw [iIndepFun_iff_hasLaw_pi_pi (μ := fun c => P.map (Z c))
    (fun c => ⟨(hZ c).aemeasurable, rfl⟩)]
  have hvec : Measurable (fun ω c => Z c ω) := measurable_pi_iff.mpr hZ
  refine ⟨hvec.aemeasurable, ?_⟩
  symm
  refine Measure.pi_eq ?_
  intro s hs
  rw [Measure.map_apply hvec (MeasurableSet.univ_pi hs)]
  let t : ∀ i, Set (β i) := fun i => φ i false ⁻¹' s (i, false) ∩ φ i true ⁻¹' s (i, true)
  have ht : ∀ i, MeasurableSet (t i) := fun i =>
    ((hφ i false) (hs (i, false))).inter ((hφ i true) (hs (i, true)))
  have hpre : (fun ω c => Z c ω) ⁻¹' Set.univ.pi s =
      ⋂ i ∈ (Finset.univ : Finset ι), Y i ⁻¹' t i := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter, Finset.mem_univ,
      forall_true_left, t, Set.mem_inter_iff, Z, Prod.forall, Bool.forall_bool]
  rw [hpre, hind.measure_inter_preimage_eq_mul Finset.univ (fun i _ => ht i),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi := (hpair i).measure_inter_preimage_eq_mul (s (i, false)) (s (i, true))
    (hs _) (hs _)
  rw [Fintype.prod_bool, mul_comm, Measure.map_apply (hZ _) (hs _),
    Measure.map_apply (hZ _) (hs _)]
  exact hi

/-- The real physical coordinates are jointly independent.  This combines the
upper-triangular independence of `GaussianRing.Law` with the independence of the real
and imaginary parts of each strict upper entry; the imaginary label of a diagonal
entry is the constant zero map. -/
theorem Law.iIndepFun_physicalCoordinate {p : Params} (M : Law p) :
    iIndepFun (fun c : PhysicalRealCoordinate p => M.physicalCoordinate c) M.P := by
  have h := iIndepFun_pairComponents (P := M.P)
    (fun q : UpperPair p => fun ω => M.H ω q.1.1 q.1.2)
    (fun q => M.measurable_entry q.1.1 q.1.2) M.upper_independent
    (fun q b => physicalCoordinateMap p (q, b))
    (fun q b => measurable_physicalCoordinateMap p (q, b)) ?_
  · exact h
  intro q
  by_cases hd : q.1.1 = q.1.2
  · have hconst : (fun ω => physicalCoordinateMap p (q, true) (M.H ω q.1.1 q.1.2)) =
        fun _ => (0 : ℝ) := by
      funext ω
      simp [physicalCoordinateMap, hd]
    rw [hconst]
    exact indepFun_const_right _ 0
  · have hre : (fun ω => physicalCoordinateMap p (q, false) (M.H ω q.1.1 q.1.2)) =
        fun ω => (M.H ω q.1.1 q.1.2).re := by
      funext ω
      simp [physicalCoordinateMap]
    have him : (fun ω => physicalCoordinateMap p (q, true) (M.H ω q.1.1 q.1.2)) =
        fun ω => (M.H ω q.1.1 q.1.2).im := by
      funext ω
      simp [physicalCoordinateMap, hd]
    rw [hre, him]
    exact M.offdiag_components_independent q.1.1 q.1.2 q.2 hd

/-- The active real coordinates: those of nonzero variance.  These are the diagonal
real parts and the real and imaginary parts of the strict upper entries inside one
block or between cyclically adjacent blocks. -/
abbrev PhysicalActiveCoordinate (p : Params) :=
  {c : PhysicalRealCoordinate p // physicalCoordinateVariance p c ≠ 0}

/-- The random vector of active real coordinates. -/
def Law.physicalActiveCoordinates {p : Params} (M : Law p) (ω : M.Ω) :
    PhysicalActiveCoordinate p → ℝ :=
  fun c => M.physicalCoordinate c.1 ω

theorem Law.measurable_physicalActiveCoordinates {p : Params} (M : Law p) :
    Measurable M.physicalActiveCoordinates :=
  measurable_pi_iff.mpr fun c => M.measurable_physicalCoordinate c.1

/-- The joint law of the active coordinates is the product of nondegenerate centred
Gaussians with the physical variances. -/
theorem Law.hasLaw_physicalActiveCoordinates {p : Params} (M : Law p) :
    HasLaw M.physicalActiveCoordinates
      (Measure.pi fun c : PhysicalActiveCoordinate p =>
        gaussianReal 0 (physicalCoordinateVariance p c.1)) M.P := by
  have hind : iIndepFun (fun c : PhysicalActiveCoordinate p =>
      M.physicalCoordinate c.1) M.P :=
    M.iIndepFun_physicalCoordinate.precomp Subtype.val_injective
  exact hind.hasLaw_pi (fun c => M.hasLaw_physicalCoordinate c.1)

/-- An inactive coordinate vanishes almost surely. -/
theorem Law.ae_physicalCoordinate_eq_zero {p : Params} (M : Law p)
    (c : PhysicalRealCoordinate p) (hc : physicalCoordinateVariance p c = 0) :
    ∀ᵐ ω ∂M.P, M.physicalCoordinate c ω = 0 := by
  have h := M.hasLaw_physicalCoordinate c
  rw [hc, gaussianReal_zero_var] at h
  have hmap : ∀ᵐ y ∂(M.P.map (M.physicalCoordinate c)), y = 0 := by
    rw [h.map_eq]
    rw [ae_dirac_eq]; exact Filter.eventually_pure.mpr rfl
  exact ae_of_ae_map h.aemeasurable hmap

/-- Totality of the site order used to select upper pairs. -/
theorem siteLE_of_not_siteLE {p : Params} {a b : Site p.n p.W} (h : ¬siteLE p a b) :
    siteLE p b a := by
  unfold siteLE at h ⊢
  omega

/-- The value of a coordinate label in an active-coordinate vector, zero on inactive
labels. -/
def activeValue (p : Params) {R : Type*} [Zero R] (x : PhysicalActiveCoordinate p → R)
    (c : PhysicalRealCoordinate p) : R :=
  if h : physicalCoordinateVariance p c ≠ 0 then x ⟨c, h⟩ else 0

/-- Reconstruct the Hermitian band matrix from its active real coordinates; inactive
coordinates are set to zero and the lower triangle is the conjugate of the upper one. -/
def physicalReconstruction (p : Params) (x : PhysicalActiveCoordinate p → ℝ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ := fun a b =>
  if h : siteLE p a b then
    ((activeValue p x (⟨(a, b), h⟩, false) : ℝ) : ℂ) +
      Complex.I * ((activeValue p x (⟨(a, b), h⟩, true) : ℝ) : ℂ)
  else
    ((activeValue p x (⟨(b, a), siteLE_of_not_siteLE h⟩, false) : ℝ) : ℂ) -
      Complex.I * ((activeValue p x (⟨(b, a), siteLE_of_not_siteLE h⟩, true) : ℝ) : ℂ)

/-- The universal band matrix over the polynomial ring in the active coordinates. -/
def physicalUniversalMatrix (p : Params) :
    Matrix (Site p.n p.W) (Site p.n p.W) (MvPolynomial (PhysicalActiveCoordinate p) ℂ) :=
  fun a b =>
  if h : siteLE p a b then
    activeValue p MvPolynomial.X (⟨(a, b), h⟩, false) +
      MvPolynomial.C Complex.I * activeValue p MvPolynomial.X (⟨(a, b), h⟩, true)
  else
    activeValue p MvPolynomial.X (⟨(b, a), siteLE_of_not_siteLE h⟩, false) -
      MvPolynomial.C Complex.I *
        activeValue p MvPolynomial.X (⟨(b, a), siteLE_of_not_siteLE h⟩, true)

theorem eval_activeValue_X (p : Params) (x : PhysicalActiveCoordinate p → ℝ)
    (c : PhysicalRealCoordinate p) :
    MvPolynomial.eval (fun c => (x c : ℂ)) (activeValue p MvPolynomial.X c) =
      ((activeValue p x c : ℝ) : ℂ) := by
  unfold activeValue
  split_ifs <;> simp

/-- Evaluating the universal band matrix at real coordinates is the reconstruction. -/
theorem physicalUniversalMatrix_map_eval (p : Params) (x : PhysicalActiveCoordinate p → ℝ) :
    (physicalUniversalMatrix p).map (MvPolynomial.eval fun c => (x c : ℂ)) =
      physicalReconstruction p x := by
  ext a b
  simp only [Matrix.map_apply, physicalUniversalMatrix, physicalReconstruction]
  split_ifs <;> simp [eval_activeValue_X]

/-- On active coordinates the reconstruction reads the physical coordinates. -/
theorem Law.activeValue_physicalActiveCoordinates {p : Params} (M : Law p) (ω : M.Ω)
    (hzero : ∀ c : PhysicalRealCoordinate p, physicalCoordinateVariance p c = 0 →
      M.physicalCoordinate c ω = 0) (c : PhysicalRealCoordinate p) :
    activeValue p (M.physicalActiveCoordinates ω) c = M.physicalCoordinate c ω := by
  unfold activeValue
  split_ifs with h
  · rfl
  · exact (hzero c (not_not.mp h)).symm

/-- Almost surely the physical matrix is the reconstruction of its active coordinates:
the off-band entries vanish and the diagonal is real. -/
theorem Law.ae_physicalReconstruction_eq {p : Params} (M : Law p) :
    ∀ᵐ ω ∂M.P, physicalReconstruction p (M.physicalActiveCoordinates ω) = M.H ω := by
  have hzero : ∀ᵐ ω ∂M.P, ∀ c : PhysicalRealCoordinate p,
      physicalCoordinateVariance p c = 0 → M.physicalCoordinate c ω = 0 := by
    rw [ae_all_iff]
    intro c
    by_cases hc : physicalCoordinateVariance p c = 0
    · filter_upwards [M.ae_physicalCoordinate_eq_zero c hc] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hc
  have hdiag : ∀ᵐ ω ∂M.P, ∀ x : Site p.n p.W, (M.H ω x x).im = 0 := by
    rw [ae_all_iff]
    exact M.diagonal_im_zero
  filter_upwards [hzero, hdiag] with ω hz hd
  have hv := M.activeValue_physicalActiveCoordinates ω hz
  ext a b
  simp only [physicalReconstruction]
  split_ifs with h
  · rw [hv, hv]
    by_cases hab : a = b
    · subst hab
      simp only [Law.physicalCoordinate, physicalCoordinateMap, ite_true]
      apply Complex.ext <;> simp [hd a]
    · simp only [Law.physicalCoordinate, physicalCoordinateMap, ite_true, ite_false, hab]
      apply Complex.ext <;> simp
  · rw [hv, hv]
    have hba : b ≠ a := by
      rintro rfl
      exact h (le_refl _)
    have hH := congrFun (congrFun (M.H_hermitian ω) a) b
    simp only [Matrix.conjTranspose_apply] at hH
    simp only [Law.physicalCoordinate, physicalCoordinateMap, ite_true, ite_false, hba]
    rw [← hH]
    apply Complex.ext <;> simp

/-!
### Polynomial nullity under the active Gaussian law
-/

/-- Finite products of absolutely continuous factors are absolutely continuous
w.r.t. Lebesgue measure on `σ → ℝ`. -/
theorem pi_absolutelyContinuous_volume {σ : Type*} [Fintype σ]
    (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (h : ∀ i, μ i ≪ (volume : Measure ℝ)) :
    Measure.pi μ ≪ (volume : Measure (σ → ℝ)) := by
  let P : ∀ (α : Type _) [Fintype α], Prop := fun α _ =>
    ∀ (μ ν : α → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν
  have key : P σ := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ σ
    · intro α β _ e hα μ ν _ _ hμν
      let _ : Fintype α := Fintype.ofEquiv β e.symm
      have hm := (measurePreserving_piCongrLeft μ e).map_eq
      have hn := (measurePreserving_piCongrLeft ν e).map_eq
      rw [← hm, ← hn]
      exact (hα (fun a => μ (e a)) (fun a => ν (e a)) (fun a => hμν (e a))).map
        (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e).measurable
    · intro μ ν _ _ _
      rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
    · intro α _ hα μ ν _ _ hμν
      rw [← Measure.pi_map_piOptionEquivProd μ, ← Measure.pi_map_piOptionEquivProd ν]
      exact ((hα (fun i => μ (some i)) (fun i => ν (some i)) (fun i => hμν (some i))).prod
        (hμν none)).map (MeasurableEquiv.piOptionEquivProd (fun _ => ℝ)).symm.measurable
  rw [volume_pi]
  exact key μ (fun _ => volume) h

/-- The zero set of a nonzero real polynomial in finitely many variables indexed by any
fintype is Lebesgue-null. -/
theorem volume_mvPolynomial_zeroSet_fintype {σ : Type*} [Fintype σ]
    (Q : MvPolynomial σ ℝ) (hQ : Q ≠ 0) :
    volume {x : σ → ℝ | MvPolynomial.eval x Q = 0} = 0 := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let Q' : MvPolynomial (Fin (Fintype.card σ)) ℝ := MvPolynomial.rename e Q
  have hQ' : Q' ≠ 0 := by
    intro h0
    apply hQ
    apply MvPolynomial.rename_injective e e.injective
    simpa [Q'] using h0
  have hnull := volume_mvPolynomial_zeroSet _ Q' hQ'
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e
  have hpre : {x : σ → ℝ | MvPolynomial.eval x Q = 0} =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e) ⁻¹'
        {y | MvPolynomial.eval y Q' = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Q', MvPolynomial.eval_rename]
    have : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e) x) ∘ e = x := by
      funext a
      exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card σ) => ℝ) e x a
    rw [this]
  rw [hpre]
  exact hmp.quasiMeasurePreserving.preimage_null hnull

/-- The real norm-square polynomial of a complex polynomial in real variables. -/
def mvPolynomialNormSq {σ : Type*} (F : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  mvPolynomialRealPart F ^ 2 + mvPolynomialImagPart F ^ 2

theorem eval_mvPolynomialNormSq {σ : Type*} (F : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval x (mvPolynomialNormSq F) =
      Complex.normSq (MvPolynomial.eval (fun i => (x i : ℂ)) F) := by
  rw [mvPolynomialNormSq, map_add, map_pow, map_pow,
    eval_mvPolynomialRealPart, eval_mvPolynomialImagPart]
  simp [Complex.normSq, pow_two]

/-- The active-coordinate law of the physical Gaussian ring is absolutely continuous
with respect to Lebesgue measure on the active coordinates. -/
theorem physicalActiveLaw_absolutelyContinuous (p : Params) :
    (Measure.pi fun c : PhysicalActiveCoordinate p =>
        gaussianReal 0 (physicalCoordinateVariance p c.1)) ≪ volume :=
  pi_absolutelyContinuous_volume _ fun c => gaussianReal_absolutelyContinuous 0 c.2

/-- **Polynomial nullity for the sparse physical law.**  A complex polynomial in the
active physical coordinates which does not vanish at one real coordinate point is almost
surely nonzero at the physical coordinates. -/
theorem Law.ae_eval_ne_zero_of_witness {p : Params} (M : Law p)
    (F : MvPolynomial (PhysicalActiveCoordinate p) ℂ)
    (x₀ : PhysicalActiveCoordinate p → ℝ)
    (h₀ : MvPolynomial.eval (fun c => (x₀ c : ℂ)) F ≠ 0) :
    ∀ᵐ ω ∂M.P,
      MvPolynomial.eval (fun c => (M.physicalActiveCoordinates ω c : ℂ)) F ≠ 0 := by
  set Q := mvPolynomialNormSq F
  have hQ : Q ≠ 0 := by
    intro hQ
    apply h₀
    have h := eval_mvPolynomialNormSq F x₀
    rw [show mvPolynomialNormSq F = 0 from hQ, map_zero] at h
    exact Complex.normSq_eq_zero.mp h.symm
  set Z := {x : PhysicalActiveCoordinate p → ℝ | MvPolynomial.eval x Q = 0}
  have hZmeas : MeasurableSet Z :=
    (MvPolynomial.continuous_eval Q).measurable (measurableSet_singleton 0)
  have hZ : (Measure.pi fun c : PhysicalActiveCoordinate p =>
      gaussianReal 0 (physicalCoordinateVariance p c.1)) Z = 0 :=
    physicalActiveLaw_absolutelyContinuous p (volume_mvPolynomial_zeroSet_fintype Q hQ)
  have hlaw := M.hasLaw_physicalActiveCoordinates
  have hP : M.P (M.physicalActiveCoordinates ⁻¹' Z) = 0 := by
    rw [← Measure.map_apply M.measurable_physicalActiveCoordinates hZmeas, hlaw.map_eq]
    exact hZ
  rw [ae_iff]
  refine measure_mono_null ?_ hP
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_not] at hω
  change MvPolynomial.eval (M.physicalActiveCoordinates ω) Q = 0
  rw [eval_mvPolynomialNormSq, hω, map_zero]

/-!
### Realizing deterministic band matrices as coordinate points
-/

/-- The real coordinates of a deterministic matrix, read on the active labels. -/
def coordinatesOfMatrix (p : Params) (K : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) :
    PhysicalActiveCoordinate p → ℝ :=
  fun c => physicalCoordinateMap p c.1 (K c.1.1.1.1 c.1.1.1.2)

/-- Every diagonal entry has strictly positive variance. -/
theorem varianceProfile_self_pos (p : Params) (x : Site p.n p.W) :
    0 < varianceProfile p x x := by
  have hc := p.c_pos
  have hb := p.b_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold varianceProfile blockWeight
  apply div_pos _ hW
  rw [ite_eq_left rfl]
  have h1 : 0 ≤ (if x.1 = x.1 + 1 then p.b else 0) := by split_ifs <;> linarith
  have h2 : 0 ≤ (if x.1 = x.1 - 1 then p.b else 0) := by split_ifs <;> linarith
  linarith

/-- A Hermitian matrix supported on the band is the reconstruction of its own active
coordinates. -/
theorem physicalReconstruction_coordinatesOfMatrix (p : Params)
    (K : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hK : K.IsHermitian)
    (hband : ∀ a b, a ≠ b → varianceProfile p a b = 0 → K a b = 0) :
    physicalReconstruction p (coordinatesOfMatrix p K) = K := by
  have hval : ∀ c : PhysicalRealCoordinate p,
      activeValue p (coordinatesOfMatrix p K) c =
        if physicalCoordinateVariance p c ≠ 0 then
          physicalCoordinateMap p c (K c.1.1.1 c.1.1.2) else 0 := by
    intro c
    unfold activeValue coordinatesOfMatrix
    split_ifs <;> rfl
  have hHerm : ∀ a b, K a b = star (K b a) := by
    intro a b
    have h := congrFun (congrFun hK a) b
    simp only [Matrix.conjTranspose_apply] at h
    exact h.symm
  have hdiag : ∀ a, (K a a).im = 0 := by
    intro a
    have h := hHerm a a
    have := congrArg Complex.im h
    simp at this
    linarith
  have hvpos : ∀ a, physicalCoordinateVariance p (⟨(a, a), le_refl _⟩, false) ≠ 0 := by
    intro a h
    simp only [physicalCoordinateVariance] at h
    have := varianceProfile_self_pos p a
    have h' : varianceProfile p a a = 0 := congrArg (fun r : NNReal => (r : ℝ)) h
    linarith
  -- the off-diagonal entry formula
  have hoff : ∀ a b (h : siteLE p a b), a ≠ b →
      ((activeValue p (coordinatesOfMatrix p K) (⟨(a, b), h⟩, false) : ℝ) : ℂ) +
        Complex.I * ((activeValue p (coordinatesOfMatrix p K) (⟨(a, b), h⟩, true) : ℝ) : ℂ) =
        K a b := by
    intro a b h hab
    rw [hval, hval]
    by_cases hv : varianceProfile p a b = 0
    · have hz : ∀ bb : Bool,
          physicalCoordinateVariance p (⟨(a, b), h⟩, bb) = 0 := by
        intro bb
        apply NNReal.eq
        cases bb <;> simp [physicalCoordinateVariance, hab, hv] <;> rfl
      simp only [hz, ne_eq, not_true_eq_false, ite_false]
      simp [hband a b hab hv]
    · have hnz : ∀ bb : Bool,
          physicalCoordinateVariance p (⟨(a, b), h⟩, bb) ≠ 0 := by
        intro bb h0
        have h' := congrArg (fun r : NNReal => (r : ℝ)) h0
        cases bb <;> simp only [physicalCoordinateVariance, hab] at h' <;>
          exact hv (by have h'' : varianceProfile p a b / 2 = 0 := h'; linarith)
      simp only [hnz, ne_eq, not_false_eq_true, ite_true]
      simp only [physicalCoordinateMap, ite_true, ite_false, hab, Bool.false_eq_true]
      apply Complex.ext <;> simp
  ext a b
  simp only [physicalReconstruction]
  split_ifs with h
  · by_cases hab : a = b
    · subst hab
      rw [hval, hval]
      have hz : physicalCoordinateVariance p (⟨(a, a), h⟩, true) = 0 := by
        simp [physicalCoordinateVariance]
      simp only [hvpos a, hz, ne_eq, not_false_eq_true, not_true_eq_false, ite_true,
        ite_false]
      simp only [physicalCoordinateMap, ite_false, Bool.false_eq_true]
      apply Complex.ext <;> simp [hdiag a]
    · exact hoff a b h hab
  · have hba : b ≠ a := by
      rintro rfl
      exact h (le_refl _)
    have := hoff b a (siteLE_of_not_siteLE h) hba
    rw [hHerm a b, ← this]
    apply Complex.ext <;> simp

/-!
### Discriminant and resultant polynomials of polynomial matrix families
-/

/-- Evaluation commutes with the matrix discriminant. -/
theorem discr_map_eval {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (MvPolynomial σ ℂ)) (g : σ → ℂ) :
    (U.map (MvPolynomial.eval g)).discr = MvPolynomial.eval g U.discr := by
  rw [Matrix.discr, Matrix.discr, Matrix.charpoly_map]
  exact Polynomial.discr_map_of_monic _ _ (Matrix.charpoly_monic U)

/-- Evaluation commutes with the resultant of the characteristic polynomials of a
matrix and of one of its principal submatrices, at the dimension degrees. -/
theorem resultant_charpoly_submatrix_map_eval {σ ι ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    (U : Matrix ι ι (MvPolynomial σ ℂ)) (f : ρ → ι) (g : σ → ℂ) :
    ((U.map (MvPolynomial.eval g)).charpoly).resultant
        (((U.map (MvPolynomial.eval g)).submatrix f f).charpoly)
        (Fintype.card ι) (Fintype.card ρ) =
      MvPolynomial.eval g
        ((U.charpoly).resultant ((U.submatrix f f).charpoly)
          (Fintype.card ι) (Fintype.card ρ)) := by
  rw [Matrix.submatrix_map, Matrix.charpoly_map, Matrix.charpoly_map,
    Polynomial.resultant_map_map]

/-- For characteristic polynomials over `ℂ`, the dimension-degree resultant is nonzero
exactly when the two polynomials are coprime. -/
theorem resultant_charpoly_ne_zero_iff {ι ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ι ι ℂ) (B : Matrix ρ ρ ℂ) :
    A.charpoly.resultant B.charpoly (Fintype.card ι) (Fintype.card ρ) ≠ 0 ↔
      IsCoprime A.charpoly B.charpoly := by
  have h := Polynomial.resultant_eq_zero_iff (f := A.charpoly) (g := B.charpoly)
  rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim] at h
  rw [ne_eq, h]
  have hA : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  constructor
  · intro hn
    by_contra hc
    exact hn ⟨Or.inl hA, hc⟩
  · rintro hc ⟨_, hn⟩
    exact hn hc

/-- **Almost-sure simple spectrum for a polynomial family.**  If a matrix family that is
polynomial in the active physical coordinates has separable characteristic polynomial
at one real coordinate point, then it has separable characteristic polynomial almost
surely at the physical coordinates. -/
theorem Law.ae_charpoly_separable_of_polynomialFamily {p : Params} (M : Law p)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (MvPolynomial (PhysicalActiveCoordinate p) ℂ))
    (x₀ : PhysicalActiveCoordinate p → ℝ)
    (h₀ : (U.map (MvPolynomial.eval fun c => (x₀ c : ℂ))).charpoly.Separable) :
    ∀ᵐ ω ∂M.P, (U.map (MvPolynomial.eval fun c =>
      (M.physicalActiveCoordinates ω c : ℂ))).charpoly.Separable := by
  have hw : MvPolynomial.eval (fun c => (x₀ c : ℂ)) U.discr ≠ 0 := by
    rw [← discr_map_eval, Matrix.discr]
    exact Polynomial.discr_ne_zero_of_monic_separable (Matrix.charpoly_monic _) h₀
  filter_upwards [M.ae_eval_ne_zero_of_witness U.discr x₀ hw] with ω hω
  rw [← discr_map_eval, Matrix.discr] at hω
  by_contra hns
  exact hω ((Polynomial.discr_eq_zero_iff_not_separable (Matrix.charpoly_monic _)).mpr hns)

/-- **Almost-sure common-spectrum avoidance for a polynomial family.**  If a matrix
family polynomial in the active physical coordinates and one of its principal
submatrices have coprime characteristic polynomials at one real coordinate point, then
they have coprime characteristic polynomials almost surely. -/
theorem Law.ae_isCoprime_charpoly_submatrix_of_polynomialFamily {p : Params} (M : Law p)
    {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    (U : Matrix ι ι (MvPolynomial (PhysicalActiveCoordinate p) ℂ)) (f : ρ → ι)
    (x₀ : PhysicalActiveCoordinate p → ℝ)
    (h₀ : IsCoprime (U.map (MvPolynomial.eval fun c => (x₀ c : ℂ))).charpoly
      ((U.map (MvPolynomial.eval fun c => (x₀ c : ℂ))).submatrix f f).charpoly) :
    ∀ᵐ ω ∂M.P, IsCoprime
      (U.map (MvPolynomial.eval fun c => (M.physicalActiveCoordinates ω c : ℂ))).charpoly
      ((U.map (MvPolynomial.eval fun c =>
        (M.physicalActiveCoordinates ω c : ℂ))).submatrix f f).charpoly := by
  have hw := (resultant_charpoly_ne_zero_iff _ _).mpr h₀
  rw [resultant_charpoly_submatrix_map_eval] at hw
  filter_upwards [M.ae_eval_ne_zero_of_witness _ x₀ hw] with ω hω
  rw [← resultant_charpoly_submatrix_map_eval] at hω
  exact (resultant_charpoly_ne_zero_iff _ _).mp hω

/-!
### Full simple spectrum
-/

/-- The diagonal witness: the site `x` carries its row-major flat index. -/
def distinctDiagonalSiteMatrix (p : Params) : Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  Matrix.diagonal fun x => ((siteEquivFin p.n p.W x : ℕ) : ℂ)

theorem distinctDiagonalSiteMatrix_isHermitian (p : Params) :
    (distinctDiagonalSiteMatrix p).IsHermitian := by
  rw [distinctDiagonalSiteMatrix, Matrix.isHermitian_diagonal_iff]
  intro i
  exact IsSelfAdjoint.natCast _

theorem physicalReconstruction_distinctDiagonal (p : Params) :
    physicalReconstruction p (coordinatesOfMatrix p (distinctDiagonalSiteMatrix p)) =
      distinctDiagonalSiteMatrix p :=
  physicalReconstruction_coordinatesOfMatrix p _ (distinctDiagonalSiteMatrix_isHermitian p)
    fun a b hab _ => by simp [distinctDiagonalSiteMatrix, Matrix.diagonal_apply_ne _ hab]

theorem siteFlatIndex_injective (p : Params) :
    Function.Injective fun x : Site p.n p.W => ((siteEquivFin p.n p.W x : ℕ) : ℂ) := by
  intro x y hxy
  have h : ((siteEquivFin p.n p.W x : ℕ)) = (siteEquivFin p.n p.W y : ℕ) :=
    Nat.cast_injective (R := ℂ) hxy
  exact (siteEquivFin p.n p.W).injective (Fin.ext h)

/-- **Full simple spectrum.**  Almost surely the characteristic polynomial of the
physical Gaussian ring matrix is separable, i.e. its spectrum is simple.

This is the exceptional-set step of the coarea theorem, for the exact law
of the model with block weights `c 1_{l=k} + b 1_{l=k±1}` divided by `W`.  Fixed `n`,
`W`, `b`; no limit.  The proof uses only the active (band) coordinates: their joint law
is a product of nondegenerate Gaussians, the discriminant is a polynomial in them, and
it is nonzero at the diagonal band configuration `distinctDiagonalSiteMatrix`. -/
theorem Law.ae_charpoly_separable {p : Params} (M : Law p) :
    ∀ᵐ ω ∂M.P, (M.H ω).charpoly.Separable := by
  have h₀ : ((physicalUniversalMatrix p).map (MvPolynomial.eval fun c =>
      (coordinatesOfMatrix p (distinctDiagonalSiteMatrix p) c : ℂ))).charpoly.Separable := by
    rw [physicalUniversalMatrix_map_eval, physicalReconstruction_distinctDiagonal,
      distinctDiagonalSiteMatrix, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (siteFlatIndex_injective p)
  filter_upwards [M.ae_charpoly_separable_of_polynomialFamily _ _ h₀,
    M.ae_physicalReconstruction_eq] with ω hω hrec
  rwa [physicalUniversalMatrix_map_eval, hrec] at hω

/-- The universal polynomial form of the normalized physical matrix. -/
def normalizedPhysicalUniversalMatrix (p : Params) :
    Matrix (PhysicalIndex p) (PhysicalIndex p)
      (MvPolynomial (PhysicalActiveCoordinate p) ℂ) := fun x y =>
  MvPolynomial.C ((Real.sqrt p.c)⁻¹ : ℂ) *
    physicalUniversalMatrix p (allDiagonalSite x) (allDiagonalSite y)

theorem normalizedPhysicalUniversalMatrix_map_eval (p : Params)
    (x : PhysicalActiveCoordinate p → ℝ) :
    (normalizedPhysicalUniversalMatrix p).map (MvPolynomial.eval fun c => (x c : ℂ)) =
      fun i j => ((Real.sqrt p.c)⁻¹ : ℂ) *
        physicalReconstruction p x (allDiagonalSite i) (allDiagonalSite j) := by
  ext i j
  rw [Matrix.map_apply, normalizedPhysicalUniversalMatrix, map_mul, MvPolynomial.eval_C,
    ← physicalUniversalMatrix_map_eval p x, Matrix.map_apply]

/-- **Full simple spectrum of the normalized physical matrix.**  Almost surely the
normalized ring matrix `H / sqrt c`, in the block coordinates used by the coarea and
mass-profile modules, lies in `physicalSimpleSpectrumMatrices`. -/
theorem Law.ae_normalizedPhysicalMatrix_mem_physicalSimpleSpectrumMatrices
    {p : Params} (M : Law p) :
    ∀ᵐ ω ∂M.P, M.normalizedPhysicalMatrix ω ∈ physicalSimpleSpectrumMatrices p := by
  have hr : ((Real.sqrt p.c)⁻¹ : ℂ) ≠ 0 := by
    have : Real.sqrt p.c ≠ 0 := (Real.sqrt_pos.mpr p.c_pos).ne'
    exact inv_ne_zero (by exact_mod_cast this)
  have h₀ : ((normalizedPhysicalUniversalMatrix p).map (MvPolynomial.eval fun c =>
      (coordinatesOfMatrix p (distinctDiagonalSiteMatrix p) c : ℂ))).charpoly.Separable := by
    rw [normalizedPhysicalUniversalMatrix_map_eval, physicalReconstruction_distinctDiagonal]
    have hdiag : (fun i j : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
        distinctDiagonalSiteMatrix p (allDiagonalSite i) (allDiagonalSite j)) =
        Matrix.diagonal fun i => ((Real.sqrt p.c)⁻¹ : ℂ) *
          ((siteEquivFin p.n p.W (allDiagonalSite i) : ℕ) : ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [distinctDiagonalSiteMatrix]
      · have hne : allDiagonalSite i ≠ allDiagonalSite j :=
          fun h => hij (allDiagonalSite_injective h)
        simp [distinctDiagonalSiteMatrix, Matrix.diagonal_apply_ne _ hne,
          Matrix.diagonal_apply_ne _ hij]
    rw [hdiag, Matrix.charpoly_diagonal]
    refine Polynomial.separable_prod_X_sub_C_iff.mpr ?_
    intro i j hij
    exact allDiagonalSite_injective (siteFlatIndex_injective p (mul_left_cancel₀ hr hij))
  filter_upwards [M.ae_charpoly_separable_of_polynomialFamily _ _ h₀,
    M.ae_physicalReconstruction_eq] with ω hω hrec
  rw [normalizedPhysicalUniversalMatrix_map_eval, hrec] at hω
  change (physicalHermitianFinCoordinates p (M.normalizedPhysicalMatrix ω)) ∈
    hermitianSimpleSpectrumCoordinates (PhysicalDimension p)
  simp only [hermitianSimpleSpectrumCoordinates, Set.mem_ofPred_eq,
    hermitianOfFinCoordinates_physicalHermitianFinCoordinates, physicalHermitianFinReindex,
    Matrix.charpoly_reindex]
  exact hω

/-- The full-simple-spectrum event of `PhysicalCoareaExceptionalNull` has probability
one. -/
theorem Law.ae_mem_physicalFullSimpleSpectrumEvent {p : Params} (M : Law p) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalFullSimpleSpectrumEvent :=
  M.ae_normalizedPhysicalMatrix_mem_physicalSimpleSpectrumMatrices

/-!
### Fixed deterministic energy: exterior-pole avoidance
-/

/-- **Almost-sure invertibility for a polynomial family.** -/
theorem Law.ae_det_ne_zero_of_polynomialFamily {p : Params} (M : Law p)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (MvPolynomial (PhysicalActiveCoordinate p) ℂ))
    (x₀ : PhysicalActiveCoordinate p → ℝ)
    (h₀ : (U.map (MvPolynomial.eval fun c => (x₀ c : ℂ))).det ≠ 0) :
    ∀ᵐ ω ∂M.P, (U.map (MvPolynomial.eval fun c =>
      (M.physicalActiveCoordinates ω c : ℂ))).det ≠ 0 := by
  have hw : MvPolynomial.eval (fun c => (x₀ c : ℂ)) U.det ≠ 0 := by
    rw [RingHom.map_det]
    exact h₀
  filter_upwards [M.ae_eval_ne_zero_of_witness U.det x₀ hw] with ω hω
  rw [RingHom.map_det] at hω
  exact hω

/-- The normalized physical exterior minor as a polynomial family. -/
theorem normalizedPhysicalUniversalMatrix_submatrix_map_eval (p : Params) (j : Fin p.n)
    (x : PhysicalActiveCoordinate p → ℝ) :
    ((normalizedPhysicalUniversalMatrix p).submatrix
        (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)).map
      (MvPolynomial.eval fun c => (x c : ℂ)) =
      Matrix.submatrix (fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
        physicalReconstruction p x (allDiagonalSite i) (allDiagonalSite k))
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p) := by
  rw [← Matrix.submatrix_map, normalizedPhysicalUniversalMatrix_map_eval]

/-- Almost surely the normalized physical matrix is the normalized reconstruction of
the active coordinates. -/
theorem Law.ae_normalizedPhysicalMatrix_eq {p : Params} (M : Law p) :
    ∀ᵐ ω ∂M.P, (M.normalizedPhysicalMatrix ω : Matrix _ _ ℂ) =
      fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
        physicalReconstruction p (M.physicalActiveCoordinates ω)
          (allDiagonalSite i) (allDiagonalSite k) := by
  filter_upwards [M.ae_physicalReconstruction_eq] with ω hω
  rw [hω]
  rfl

theorem sqrt_c_complex_ne_zero (p : Params) : ((Real.sqrt p.c : ℝ) : ℂ) ≠ 0 := by
  have : Real.sqrt p.c ≠ 0 := (Real.sqrt_pos.mpr p.c_pos).ne'
  exact_mod_cast this

/-- A constant real diagonal band matrix. -/
theorem physicalReconstruction_constDiagonal (p : Params) (a : ℝ) :
    physicalReconstruction p
        (coordinatesOfMatrix p (Matrix.diagonal fun _ => ((a : ℝ) : ℂ))) =
      Matrix.diagonal fun _ => ((a : ℝ) : ℂ) :=
  physicalReconstruction_coordinatesOfMatrix p _
    (by
      rw [Matrix.isHermitian_diagonal_iff]
      intro i
      exact Complex.conj_ofReal a)
    fun a b hab _ => by simp [Matrix.diagonal_apply_ne _ hab]

/-- **Fixed-energy exterior-pole avoidance.**  For every fixed deterministic real energy
`E` and exposed block `j`, almost surely `E` is not an eigenvalue of the normalized
physical exterior minor: the exterior pencil `D - E` is invertible.

This is the pole-avoidance step of the coarea theorem for a deterministic energy.  Fixed
`n`, `W`, `b`, `j`, `E`; the null set depends on `E`. -/
theorem Law.ae_det_physicalExteriorPencil_ne_zero {p : Params} (M : Law p)
    (j : Fin p.n) (E : ℝ) :
    ∀ᵐ ω ∂M.P,
      (physicalExteriorPencil (M.normalizedPhysicalExteriorMatrix j ω).1 E).det ≠ 0 := by
  set V : Matrix (PhysicalExteriorIndex p j) (PhysicalExteriorIndex p j)
      (MvPolynomial (PhysicalActiveCoordinate p) ℂ) :=
    (normalizedPhysicalUniversalMatrix p).submatrix Subtype.val Subtype.val -
      Matrix.diagonal fun _ => MvPolynomial.C (E : ℂ)
  have hV : ∀ x : PhysicalActiveCoordinate p → ℝ,
      V.map (MvPolynomial.eval fun c => (x c : ℂ)) =
        physicalExteriorPencil (Matrix.submatrix (fun i k : PhysicalIndex p =>
          ((Real.sqrt p.c)⁻¹ : ℂ) *
          physicalReconstruction p x (allDiagonalSite i) (allDiagonalSite k))
            (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)) E := by
    intro x
    rw [← normalizedPhysicalUniversalMatrix_submatrix_map_eval, physicalExteriorPencil]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [V, Matrix.sub_apply, Matrix.smul_apply]
    · simp [V, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab,
        Matrix.one_apply_ne hab]
  set x₀ := coordinatesOfMatrix p
    (Matrix.diagonal fun _ => (((Real.sqrt p.c * (E + 1)) : ℝ) : ℂ))
  have h₀ : (V.map (MvPolynomial.eval fun c => (x₀ c : ℂ))).det ≠ 0 := by
    rw [hV, physicalReconstruction_constDiagonal]
    have hone : physicalExteriorPencil (Matrix.submatrix (fun i k : PhysicalIndex p =>
        ((Real.sqrt p.c)⁻¹ : ℂ) * (Matrix.diagonal fun _ =>
          (((Real.sqrt p.c * (E + 1)) : ℝ) : ℂ)) (allDiagonalSite i) (allDiagonalSite k))
            (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)) E = 1 := by
      ext a b
      simp only [physicalExteriorPencil, Matrix.sub_apply, Matrix.submatrix, Matrix.of_apply,
        Matrix.smul_apply, smul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        have := sqrt_c_complex_ne_zero p
        push_cast
        field_simp
        ring
      · have hne : allDiagonalSite a.1 ≠ allDiagonalSite b.1 :=
          fun h => hab (Subtype.ext (allDiagonalSite_injective h))
        simp [Matrix.diagonal_apply_ne _ hne, Matrix.one_apply_ne hab]
    rw [hone, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [M.ae_det_ne_zero_of_polynomialFamily V x₀ h₀,
    M.ae_normalizedPhysicalMatrix_eq] with ω hω hN
  rw [hV] at hω
  have hext : (M.normalizedPhysicalExteriorMatrix j ω).1 =
      (M.normalizedPhysicalMatrix ω : Matrix _ _ ℂ).submatrix Subtype.val Subtype.val := rfl
  rw [hext, hN]
  exact hω

/-!
### A deterministic path witness for common-spectrum exclusion

On `Fin L`, the matrix `jacobiWitness L W B t` has unit nearest-neighbour couplings on
the path `W - 1, W, ..., L - B - 1` and the value `t` on the remaining diagonal.  The
exterior `[W, L - B)` is the path with its first vertex removed.  For a suitable real
`t`, the full and exterior characteristic polynomials are coprime.
-/

/-- Indices of the exterior: `W ≤ a < L - B`. -/
abbrev jacobiExterior (L W B : ℕ) := {a : Fin L // W ≤ a.val ∧ a.val + B < L}

/-- The path part: `W - 1 ≤ a < L - B`. -/
def jacobiPath (L W B : ℕ) (a : Fin L) : Prop := W ≤ a.val + 1 ∧ a.val + B < L

instance jacobiPath.decidable (L W B : ℕ) (a : Fin L) : Decidable (jacobiPath L W B a) := by
  unfold jacobiPath; infer_instance

/-- Unit nearest-neighbour couplings along the path `W-1, W, ..., L-B-1`, and value `t`
on the diagonal at every index off the path; zero elsewhere. -/
def jacobiWitness (L W B : ℕ) (t : ℝ) : Matrix (Fin L) (Fin L) ℂ := fun a b =>
  if jacobiPath L W B a ∧ jacobiPath L W B b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val) then 1
  else if a = b ∧ ¬ jacobiPath L W B a then (t : ℂ) else 0

theorem jacobiWitness_transpose (L W B : ℕ) (t : ℝ) :
    (jacobiWitness L W B t)ᵀ = jacobiWitness L W B t := by
  ext a b
  simp only [Matrix.transpose_apply, jacobiWitness]
  by_cases h1 : jacobiPath L W B a ∧ jacobiPath L W B b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val)
  · rw [ite_eq_left h1, ite_eq_left ⟨h1.2.1, h1.1, h1.2.2.symm⟩]
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 ⟨h.2.1, h.1, h.2.2.symm⟩)]
    by_cases h2 : a = b
    · subst h2; rfl
    · rw [ite_eq_right (fun h => h2 h.1.symm), ite_eq_right (fun h => h2 h.1)]

theorem jacobiWitness_conj (L W B : ℕ) (t : ℝ) :
    ∀ a b, star (jacobiWitness L W B t a b) = jacobiWitness L W B t a b := by
  intro a b
  simp only [jacobiWitness]
  split_ifs <;> simp

lemma jacobiWitness_ne_zero {L W B : ℕ} {t : ℝ} {a b : Fin L}
    (h : jacobiWitness L W B t a b ≠ 0) :
    (jacobiPath L W B a ∧ jacobiPath L W B b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val)) ∨
      (a = b ∧ ¬ jacobiPath L W B a) := by
  unfold jacobiWitness at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd rfl h

lemma jacobiWitness_submatrix_eq (L W B : ℕ) (t s : ℝ) :
    (jacobiWitness L W B t).submatrix (Subtype.val : jacobiExterior L W B → Fin L)
        (Subtype.val : jacobiExterior L W B → Fin L) =
      (jacobiWitness L W B s).submatrix (Subtype.val : jacobiExterior L W B → Fin L)
        (Subtype.val : jacobiExterior L W B → Fin L) := by
  ext a b
  have ha : jacobiPath L W B a.1 := ⟨by have := a.2.1; omega, a.2.2⟩
  simp [jacobiWitness, ha]

/-- Path lemma: an exterior null vector of `E - K_R` vanishing at the first exterior
index vanishes identically. -/
lemma jacobiWitness_path_zero {L W B : ℕ} (t : ℝ) (E : ℂ) (u : jacobiExterior L W B → ℂ)
    (hu : (Matrix.scalar _ E - (jacobiWitness L W B t).submatrix
      (Subtype.val : jacobiExterior L W B → Fin L) (Subtype.val : jacobiExterior L W B → Fin L))
        *ᵥ u = 0)
    (h0 : ∀ r : jacobiExterior L W B, r.1.val = W → u r = 0) : u = 0 := by
  have key : ∀ n : ℕ, ∀ r : jacobiExterior L W B, r.1.val ≤ W + n → u r = 0 := by
    intro n
    induction n with
    | zero => intro r hr; exact h0 r (by have := r.2.1; omega)
    | succ n ih =>
      intro r hr
      rcases Nat.lt_or_ge r.1.val (W + n + 1) with h | h
      · exact ih r (by omega)
      have hrv : r.1.val = W + n + 1 := by omega
      have hr2 := r.2
      let m : jacobiExterior L W B := ⟨⟨W + n, by omega⟩, by simp; omega⟩
      have hrow := congrFun hu m
      simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, Matrix.scalar_apply,
        Matrix.mulVec_diagonal] at hrow
      have hm : u m = 0 := ih m (by simp [m])
      rw [hm, mul_zero, zero_sub, neg_eq_zero] at hrow
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at hrow
      rw [Finset.sum_eq_single r] at hrow
      · have hmr : jacobiWitness L W B t m.1 r.1 = 1 := by
          simp only [jacobiWitness]
          rw [ite_eq_left]
          refine ⟨⟨show W ≤ W + n + 1 by omega, show W + n + B < L by omega⟩, ⟨by omega, hr2.2⟩, Or.inl ?_⟩
          simp [m]; omega
        rw [hmr, one_mul] at hrow
        exact hrow
      · intro b _ hb
        by_cases hK : jacobiWitness L W B t m.1 b.1 = 0
        · rw [hK, zero_mul]
        · rw [ih b, mul_zero]
          rcases jacobiWitness_ne_zero hK with ⟨-, -, h | h⟩ | ⟨h, -⟩
          · exfalso; apply hb; apply Subtype.ext; apply Fin.ext; simp [m] at h; omega
          · simp [m] at h; omega
          · rw [← h]
      · simp
  funext r
  exact key (r.1.val - W) r (by omega)

lemma jacobiWitness_exists_nonroot (L W B : ℕ) : ∃ t : ℝ, Polynomial.eval (t : ℂ)
    ((jacobiWitness L W B 0).submatrix (Subtype.val : jacobiExterior L W B → Fin L)
      (Subtype.val : jacobiExterior L W B → Fin L)).charpoly ≠ 0 := by
  set p := ((jacobiWitness L W B 0).submatrix (Subtype.val : jacobiExterior L W B → Fin L)
      (Subtype.val : jacobiExterior L W B → Fin L)).charpoly
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (p.roots.toFinset.image Complex.re)
  refine ⟨t, fun h => ht ?_⟩
  rw [Finset.mem_image]
  refine ⟨(t : ℂ), ?_, by simp⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
  exact h

theorem exists_jacobiWitness_coprime (L W B : ℕ) (hW : 1 ≤ W) (hL : W + B < L) :
    ∃ t : ℝ, IsCoprime (jacobiWitness L W B t).charpoly
      ((jacobiWitness L W B t).submatrix
        (Subtype.val : jacobiExterior L W B → Fin L) Subtype.val).charpoly := by
  obtain ⟨t, ht⟩ := jacobiWitness_exists_nonroot L W B
  refine ⟨t, ?_⟩
  rw [← jacobiWitness_submatrix_eq L W B t 0] at ht
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro E
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Polynomial.coe_aeval_eq_eval, Matrix.eval_charpoly] at h1 h2
  have hEt : E ≠ (t : ℂ) := by
    rintro rfl; apply ht; rw [Matrix.eval_charpoly]; exact h2
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h2
  set K := jacobiWitness L W B t with hKdef
  have row : ∀ a : Fin L, E * v a = ∑ b, K a b * v b := by
    intro a
    have h := congrFun hv a
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, Matrix.scalar_apply,
      Matrix.mulVec_diagonal] at h
    simp only [Matrix.mulVec, dotProduct] at h
    exact sub_eq_zero.mp h
  let w₀ : Fin L := ⟨W - 1, by omega⟩
  let wW : Fin L := ⟨W, by omega⟩
  let rW : jacobiExterior L W B := ⟨wW, show W ≤ W ∧ W + B < L by omega⟩
  have hurW : u rW ≠ 0 := by
    intro h
    apply hu0
    refine jacobiWitness_path_zero t E u hu (fun r hr => ?_)
    have : r = rW := Subtype.ext (Fin.ext hr)
    rw [this]; exact h
  -- exterior rows of the full equation
  have step4 : ∀ r : jacobiExterior L W B,
      E * v r.1 - ∑ b : jacobiExterior L W B, K r.1 b.1 * v b.1 =
        if r.1.val = W then v w₀ else 0 := by
    intro r
    have hr := r.2
    rw [row r.1, ← Fintype.sum_subtype_add_sum_subtype
      (fun b : Fin L => W ≤ b.val ∧ b.val + B < L), add_sub_cancel_left]
    rw [Finset.sum_eq_single ⟨w₀, show ¬ (W ≤ W - 1 ∧ W - 1 + B < L) by omega⟩]
    · split_ifs with hrW
      · have : K r.1 w₀ = 1 := by
          rw [hKdef]; unfold jacobiWitness
          rw [ite_eq_left]
          exact ⟨⟨by omega, hr.2⟩, ⟨show W ≤ W - 1 + 1 by omega, show W - 1 + B < L by omega⟩,
            Or.inr (show W - 1 + 1 = r.1.val by omega)⟩
        rw [this, one_mul]
      · have : K r.1 w₀ = 0 := by
          rw [hKdef]; unfold jacobiWitness
          rw [ite_eq_right, ite_eq_right]
          · rintro ⟨h, -⟩
            have := congrArg Fin.val h
            simp only [w₀] at this
            omega
          · rintro ⟨-, -, h | h⟩
            · simp only [w₀] at h; omega
            · simp only [w₀] at h; omega
        rw [this, zero_mul]
    · intro b _ hb
      have hb2 := b.2
      simp only [not_and, not_lt] at hb2
      have : K r.1 b.1 = 0 := by
        by_contra hK
        rcases jacobiWitness_ne_zero hK with ⟨-, hpb, h | h⟩ | ⟨h, -⟩
        · unfold jacobiPath at hpb
          have := hb2 (by omega)
          omega
        · unfold jacobiPath at hpb
          apply hb; apply Subtype.ext; apply Fin.ext
          show b.1.val = W - 1
          by_contra hne
          have := hb2 (by omega)
          omega
        · have := hb2 (h ▸ hr.1)
          rw [← h] at this
          omega
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  set KR := K.submatrix (Subtype.val : jacobiExterior L W B → Fin L)
    (Subtype.val : jacobiExterior L W B → Fin L) with hKR
  set vR : jacobiExterior L W B → ℂ := fun r => v r.1 with hvR
  have hMv : ∀ r, ((Matrix.scalar _ E - KR) *ᵥ vR) r = if r.1.val = W then v w₀ else 0 := by
    intro r
    rw [← step4 r]
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    simp only [Matrix.mulVec, dotProduct, hKR, hvR, Matrix.submatrix_apply]
  have hsymm : (Matrix.scalar _ E - KR)ᵀ = Matrix.scalar _ E - KR := by
    rw [Matrix.transpose_sub, hKR, Matrix.transpose_submatrix, hKdef, jacobiWitness_transpose]
    simp [Matrix.scalar_apply]
  have hdot : u ⬝ᵥ ((Matrix.scalar _ E - KR) *ᵥ vR) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← hsymm, Matrix.vecMul_transpose, hu,
      zero_dotProduct]
  have hdot2 : u ⬝ᵥ ((Matrix.scalar _ E - KR) *ᵥ vR) = u rW * v w₀ := by
    rw [dotProduct, Finset.sum_eq_single rW]
    · rw [hMv]; simp [rW, wW]
    · intro b _ hb
      rw [hMv, ite_eq_right, mul_zero]
      intro h; exact hb (Subtype.ext (Fin.ext h))
    · intro h; exact absurd (Finset.mem_univ _) h
  have hvw₀ : v w₀ = 0 := by
    rw [hdot2] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left hurW
  have hvwW : v wW = 0 := by
    have h := row w₀
    rw [hvw₀, mul_zero, Finset.sum_eq_single wW] at h
    · have : K w₀ wW = 1 := by
        rw [hKdef]; unfold jacobiWitness
        rw [ite_eq_left]
        exact ⟨⟨show W ≤ W - 1 + 1 by omega, show W - 1 + B < L by omega⟩,
          ⟨show W ≤ W + 1 by omega, show W + B < L by omega⟩,
          Or.inl (show W - 1 + 1 = W by omega)⟩
      rw [this, one_mul] at h
      exact h.symm
    · intro b _ hb
      have : K w₀ b = 0 := by
        by_contra hK
        rcases jacobiWitness_ne_zero hK with ⟨-, hpb, h | h⟩ | ⟨h, hp⟩
        · apply hb; apply Fin.ext; simp only [w₀] at h; simp only [wW]; omega
        · unfold jacobiPath at hpb; simp only [w₀] at h; omega
        · apply hp
          exact ⟨show W ≤ W - 1 + 1 by omega, show W - 1 + B < L by omega⟩
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hvR0 : vR = 0 := by
    refine jacobiWitness_path_zero t E vR ?_ (fun r hr => ?_)
    · funext r
      rw [hMv]
      split_ifs <;> simp [hvw₀]
    · have : r = rW := Subtype.ext (Fin.ext hr)
      rw [this]; exact hvwW
  apply hv0
  funext a
  by_cases hRa : W ≤ a.val ∧ a.val + B < L
  · exact congrFun hvR0 ⟨a, hRa⟩
  by_cases hp : jacobiPath L W B a
  · have : a = w₀ := by
      apply Fin.ext; unfold jacobiPath at hp; simp only [w₀]; omega
    rw [this]; exact hvw₀
  · have h := row a
    rw [Finset.sum_eq_single a] at h
    · have : K a a = (t : ℂ) := by
        rw [hKdef]; unfold jacobiWitness
        rw [ite_eq_right (fun h => hp h.1), ite_eq_left ⟨rfl, hp⟩]
      rw [this, ← sub_eq_zero, ← sub_mul] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hEt)
    · intro b _ hb
      have : K a b = 0 := by
        by_contra hK
        rcases jacobiWitness_ne_zero hK with ⟨hpa, -⟩ | ⟨h, -⟩
        · exact hp hpa
        · exact hb h.symm
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-!
### Embedding the path witness in the physical band
-/

/-- The inverse of `allDiagonalSite`. -/
def physicalIndexOfSite {p : Params} (x : Site p.n p.W) : PhysicalIndex p :=
  ⟨⟨x.1.val, x.1.val_lt⟩, x.2⟩

theorem allDiagonalSite_physicalIndexOfSite {p : Params} (x : Site p.n p.W) :
    allDiagonalSite (physicalIndexOfSite x) = x := by
  obtain ⟨k, a⟩ := x
  simp [allDiagonalSite, physicalIndexOfSite]

theorem physicalIndexOfSite_allDiagonalSite {p : Params} (y : PhysicalIndex p) :
    physicalIndexOfSite (allDiagonalSite y) = y :=
  allDiagonalSite_injective (allDiagonalSite_physicalIndexOfSite _)

/-- Flat position of a site counted cyclically from the exposed block `j`:
`W * (k - j) + a`. -/
def exposedSitePos (p : Params) (j : Fin p.n) (x : Site p.n p.W) : ℕ :=
  p.W * (x.1 - (j : ZMod p.n)).val + x.2.val

theorem exposedSitePos_lt (p : Params) (j : Fin p.n) (x : Site p.n p.W) :
    exposedSitePos p j x < p.n * p.W := by
  have h1 : (x.1 - (j : ZMod p.n)).val < p.n := ZMod.val_lt _
  have h2 := x.2.isLt
  unfold exposedSitePos
  have : p.W * (x.1 - (j : ZMod p.n)).val + p.W ≤ p.n * p.W := by
    rw [mul_comm p.n]
    calc p.W * (x.1 - (j : ZMod p.n)).val + p.W
        = p.W * ((x.1 - (j : ZMod p.n)).val + 1) := by ring
      _ ≤ p.W * p.n := Nat.mul_le_mul_left _ h1
  omega

theorem exposedSitePos_div (p : Params) (j : Fin p.n) (x : Site p.n p.W) :
    exposedSitePos p j x / p.W = (x.1 - (j : ZMod p.n)).val := by
  unfold exposedSitePos
  rw [add_comm, Nat.add_mul_div_left _ _ p.W_pos, Nat.div_eq_of_lt x.2.isLt, zero_add]

theorem exposedSitePos_mod (p : Params) (j : Fin p.n) (x : Site p.n p.W) :
    exposedSitePos p j x % p.W = x.2.val := by
  unfold exposedSitePos
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]

theorem exposedSitePos_injective (p : Params) (j : Fin p.n) :
    Function.Injective (exposedSitePos p j) := by
  intro x y h
  have hd := exposedSitePos_div p j x
  have hm := exposedSitePos_mod p j x
  rw [h] at hd hm
  rw [exposedSitePos_div] at hd
  rw [exposedSitePos_mod] at hm
  have h1 : x.1 - (j : ZMod p.n) = y.1 - (j : ZMod p.n) := ZMod.val_injective _ hd.symm
  exact Prod.ext (sub_left_injective h1) (Fin.ext hm.symm)

theorem W_le_exposedSitePos_iff (p : Params) (j : Fin p.n) (x : Site p.n p.W) :
    p.W ≤ exposedSitePos p j x ↔ x.1 ≠ (j : ZMod p.n) := by
  have h := Nat.le_div_iff_mul_le (k := p.W) (x := 1) (y := exposedSitePos p j x) p.W_pos
  rw [one_mul, exposedSitePos_div] at h
  rw [← h, Nat.one_le_iff_ne_zero, ne_eq, ZMod.val_eq_zero, sub_eq_zero]

/-- The block weight is positive on equal and on forward-adjacent blocks. -/
theorem blockWeight_pos_of_eq_or_succ (p : Params) (k l : ZMod p.n)
    (h : l = k ∨ l = k + 1) : 0 < blockWeight p k l := by
  have hc := p.c_pos
  have hb := p.b_pos
  unfold blockWeight
  have h1 : 0 ≤ (if l = k then p.c else 0) := by split_ifs <;> linarith
  have h2 : 0 ≤ (if l = k + 1 then p.b else 0) := by split_ifs <;> linarith
  have h3 : 0 ≤ (if l = k - 1 then p.b else 0) := by split_ifs <;> linarith
  rcases h with h | h
  · rw [ite_eq_left h]; linarith
  · rw [ite_eq_left h] at h2 ⊢; linarith

/-- Consecutive exposed-relative positions lie in equal or adjacent blocks, so their
entry has nonzero variance. -/
theorem varianceProfile_ne_zero_of_exposedSitePos_succ (p : Params) (j : Fin p.n)
    {a b : Site p.n p.W} (h : exposedSitePos p j b = exposedSitePos p j a + 1) :
    varianceProfile p a b ≠ 0 := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hdiv := Nat.succ_div (a := exposedSitePos p j a) (b := p.W)
  rw [← h, exposedSitePos_div, exposedSitePos_div] at hdiv
  have hblock : b.1 = a.1 ∨ b.1 = a.1 + 1 := by
    split_ifs at hdiv
    · right
      have hz := congrArg (fun m : ℕ => (m : ZMod p.n)) hdiv
      simp only [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_one] at hz
      linear_combination hz
    · left
      have hz : b.1 - (j : ZMod p.n) = a.1 - (j : ZMod p.n) :=
        ZMod.val_injective _ (by simpa using hdiv)
      exact sub_left_injective hz
  unfold varianceProfile
  exact (div_pos (blockWeight_pos_of_eq_or_succ p a.1 b.1 hblock) hW).ne'

/-- The path witness placed on the physical sites, ordered from the exposed block `j`
and multiplied by `sqrt c` (so that the normalized matrix is the path witness itself). -/
def exposedPathSiteMatrix (p : Params) (j : Fin p.n) (t : ℝ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ := fun a b =>
  (Real.sqrt p.c : ℂ) * jacobiWitness (p.n * p.W) p.W 0 t
    ⟨exposedSitePos p j a, exposedSitePos_lt p j a⟩
    ⟨exposedSitePos p j b, exposedSitePos_lt p j b⟩

theorem exposedPathSiteMatrix_isHermitian (p : Params) (j : Fin p.n) (t : ℝ) :
    (exposedPathSiteMatrix p j t).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, exposedPathSiteMatrix, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  congr 1
  have hc := jacobiWitness_conj (p.n * p.W) p.W 0 t
    ⟨exposedSitePos p j b, exposedSitePos_lt p j b⟩
    ⟨exposedSitePos p j a, exposedSitePos_lt p j a⟩
  have h := congrFun (congrFun (jacobiWitness_transpose (p.n * p.W) p.W 0 t)
    ⟨exposedSitePos p j a, exposedSitePos_lt p j a⟩)
    ⟨exposedSitePos p j b, exposedSitePos_lt p j b⟩
  simp only [Matrix.transpose_apply] at h
  rw [← h]
  exact hc

theorem exposedPathSiteMatrix_band (p : Params) (j : Fin p.n) (t : ℝ)
    (a b : Site p.n p.W) (hab : a ≠ b) (hv : varianceProfile p a b = 0) :
    exposedPathSiteMatrix p j t a b = 0 := by
  unfold exposedPathSiteMatrix
  by_contra hne
  have hJ := right_ne_zero_of_mul hne
  rcases jacobiWitness_ne_zero hJ with ⟨-, -, h | h⟩ | ⟨h, -⟩
  · exact varianceProfile_ne_zero_of_exposedSitePos_succ p j h.symm hv
  · rw [varianceProfile_comm] at hv
    exact varianceProfile_ne_zero_of_exposedSitePos_succ p j h.symm hv
  · exact hab (exposedSitePos_injective p j (congrArg Fin.val h))

/-- The exposed-relative position of a physical block index. -/
def exposedPhysicalPos (p : Params) (j : Fin p.n) (i : PhysicalIndex p) :
    Fin (p.n * p.W) :=
  ⟨exposedSitePos p j (allDiagonalSite i), exposedSitePos_lt p j _⟩

theorem exposedPhysicalPos_bijective (p : Params) (j : Fin p.n) :
    Function.Bijective (exposedPhysicalPos p j) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y h => allDiagonalSite_injective
    (exposedSitePos_injective p j (congrArg Fin.val h)), ?_⟩
  change Fintype.card (Σ k : Fin p.n, Fin (physicalBlockSizes p k)) = _
  rw [Fintype.card_sigma, Fintype.card_fin]
  have h : ∀ k : Fin p.n, Fintype.card (Fin (physicalBlockSizes p k)) = p.W := fun k => by
    rw [Fintype.card_eq_nat_card, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The exposed-relative position as an equivalence. -/
def exposedPhysicalPosEquiv (p : Params) (j : Fin p.n) : PhysicalIndex p ≃ Fin (p.n * p.W) :=
  Equiv.ofBijective _ (exposedPhysicalPos_bijective p j)

theorem physicalIndex_ne_iff (p : Params) (j : Fin p.n) (x : PhysicalIndex p) :
    x.1 ≠ j ↔ p.W ≤ (exposedPhysicalPos p j x).val ∧
      (exposedPhysicalPos p j x).val + 0 < p.n * p.W := by
  rw [add_zero]
  simp only [exposedPhysicalPos, (exposedSitePos_lt p j _), and_true]
  rw [W_le_exposedSitePos_iff]
  simp only [allDiagonalSite]
  constructor
  · intro h hz
    apply h
    apply Fin.ext
    have := congrArg ZMod.val hz
    rwa [ZMod.val_natCast_of_lt x.1.isLt, ZMod.val_natCast_of_lt j.isLt] at this
  · intro h hz
    exact h (by rw [hz])

/-- The exterior of block `j` corresponds to the exterior `[W, nW)` of the path. -/
def exposedExteriorEquiv (p : Params) (j : Fin p.n) :
    PhysicalExteriorIndex p j ≃ jacobiExterior (p.n * p.W) p.W 0 :=
  (exposedPhysicalPosEquiv p j).subtypeEquiv fun x => physicalIndex_ne_iff p j x

/-- **The deterministic witness.**  For some real `t`, the normalized form of the path
witness and its exterior minor outside block `j` have coprime characteristic
polynomials. -/
theorem exists_exposedPath_coprime (p : Params) (j : Fin p.n) :
    ∃ t : ℝ, IsCoprime
      (Matrix.of fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
        exposedPathSiteMatrix p j t (allDiagonalSite i) (allDiagonalSite k)).charpoly
      ((Matrix.of fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
        exposedPathSiteMatrix p j t (allDiagonalSite i) (allDiagonalSite k)).submatrix
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)).charpoly := by
  have hW : 1 ≤ p.W := p.W_pos
  have hL : p.W + 0 < p.n * p.W := by
    have h4 : 4 ≤ p.n := p.n_ge_four
    nlinarith
  obtain ⟨t, ht⟩ := exists_jacobiWitness_coprime (p.n * p.W) p.W 0 hW hL
  refine ⟨t, ?_⟩
  set J := jacobiWitness (p.n * p.W) p.W 0 t
  have hfull : (Matrix.of fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
      exposedPathSiteMatrix p j t (allDiagonalSite i) (allDiagonalSite k)) =
      Matrix.reindex (exposedPhysicalPosEquiv p j).symm (exposedPhysicalPosEquiv p j).symm J := by
    ext i k
    have := sqrt_c_complex_ne_zero p
    simp only [Matrix.of_apply, exposedPathSiteMatrix, Matrix.reindex_apply,
      Equiv.symm_symm, Matrix.submatrix_apply]
    rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]
    rfl
  rw [hfull, Matrix.charpoly_reindex]
  have hext : (Matrix.reindex (exposedPhysicalPosEquiv p j).symm
      (exposedPhysicalPosEquiv p j).symm J).submatrix
        (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
        (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p) =
      Matrix.reindex (exposedExteriorEquiv p j).symm (exposedExteriorEquiv p j).symm
        (J.submatrix (Subtype.val : jacobiExterior (p.n * p.W) p.W 0 → Fin (p.n * p.W))
          Subtype.val) := by
    ext a b
    rfl
  rw [hext, Matrix.charpoly_reindex]
  exact ht

/-!
### Almost-sure common-spectrum exclusion and its consequences
-/

/-- **Common-spectrum exclusion.**  For every exposed block `j`, almost surely the
normalized physical matrix and its exterior principal minor outside block `j` have
coprime characteristic polynomials, i.e. no common eigenvalue.

This is a statement about the joint law of all active band coordinates, not about a
fixed fibre of the off-diagonal coordinates: the resultant is a polynomial in all
active coordinates, and it is nonzero at the path witness `exposedPathSiteMatrix`,
whose nonzero couplings join the exposed block to every exterior site. -/
theorem Law.ae_isCoprime_normalizedPhysical_exterior_charpoly {p : Params} (M : Law p)
    (j : Fin p.n) :
    ∀ᵐ ω ∂M.P, IsCoprime (M.normalizedPhysicalMatrix ω).1.charpoly
      (M.normalizedPhysicalExteriorMatrix j ω).1.charpoly := by
  obtain ⟨t, ht⟩ := exists_exposedPath_coprime p j
  set x₀ := coordinatesOfMatrix p (exposedPathSiteMatrix p j t)
  have hrec := physicalReconstruction_coordinatesOfMatrix p (exposedPathSiteMatrix p j t)
    (exposedPathSiteMatrix_isHermitian p j t) (exposedPathSiteMatrix_band p j t)
  have h₀ : IsCoprime
      ((normalizedPhysicalUniversalMatrix p).map
        (MvPolynomial.eval fun c => (x₀ c : ℂ))).charpoly
      (((normalizedPhysicalUniversalMatrix p).map
        (MvPolynomial.eval fun c => (x₀ c : ℂ))).submatrix
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)).charpoly := by
    rw [normalizedPhysicalUniversalMatrix_map_eval, hrec]
    exact ht
  filter_upwards [M.ae_isCoprime_charpoly_submatrix_of_polynomialFamily _ _ x₀ h₀,
    M.ae_normalizedPhysicalMatrix_eq] with ω hω hN
  rw [normalizedPhysicalUniversalMatrix_map_eval] at hω
  have hext : (M.normalizedPhysicalExteriorMatrix j ω).1 =
      (M.normalizedPhysicalMatrix ω).1.submatrix Subtype.val Subtype.val := rfl
  rw [hext, hN]
  exact hω

/-- A common root obstructs coprimality. -/
theorem not_isCoprime_of_isRoot {f g : Polynomial ℂ} {E : ℂ} (hf : f.IsRoot E)
    (hg : g.IsRoot E) : ¬IsCoprime f g := by
  rintro ⟨a, b, h⟩
  have := congrArg (Polynomial.eval E) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, hf.eq_zero, hg.eq_zero, mul_zero,
    add_zero, Polynomial.eval_one] at this
  exact zero_ne_one this

/-- An eigenvalue with a nonzero eigenvector is a root of the characteristic
polynomial. -/
theorem charpoly_isRoot_of_mulVec_eq_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {v : ι → ℂ} (hv : v ≠ 0) {E : ℂ} (h : A *ᵥ v = E • v) :
    A.charpoly.IsRoot E := by
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, h, Matrix.scalar_apply]
  funext i
  simp [smul_eq_mul]

/-- Every ordered eigenvalue of a Hermitian matrix is a root of its characteristic
polynomial. -/
theorem charpoly_isRoot_orderedEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (r : Fin (Fintype.card ι)) :
    (A : Matrix ι ι ℂ).charpoly.IsRoot (orderedEigenvalue A r : ℂ) := by
  apply charpoly_isRoot_of_mulVec_eq_smul _ _ (orderedNormalizedEigenvector_eigenvector A r)
  intro h
  have hn := norm_orderedNormalizedEigenvector A r
  have h0 : orderedNormalizedEigenvector A r = 0 := by
    ext i
    exact congrFun h i
  rw [h0, norm_zero] at hn
  exact zero_ne_one hn

/-- With coprime full and exterior characteristic polynomials, no eigenvector vanishes
on the complement of the exterior. -/
theorem eigenvector_ne_zero_off_exterior {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ρ] [DecidableEq ρ] (A : Matrix ι ι ℂ) (f : ρ → ι) (hf : Function.Injective f)
    (hcop : IsCoprime A.charpoly (A.submatrix f f).charpoly)
    {u : ι → ℂ} (hu : u ≠ 0) {E : ℂ} (hE : A *ᵥ u = E • u)
    (hsupp : ∀ x, x ∉ Set.range f → u x = 0) : False := by
  have hsum : ∀ x, (A *ᵥ u) x = ∑ y : ρ, A x (f y) * u (f y) := by
    intro x
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))]
    · rw [Finset.sum_image (fun a _ b _ h => hf h)]
    · intro z _ hz
      have : z ∉ Set.range f := by
        rintro ⟨y, rfl⟩
        exact hz (Finset.mem_image_of_mem f (Finset.mem_univ y))
      rw [hsupp z this, mul_zero]
  have huR : (fun y => u (f y)) ≠ 0 := by
    intro h0
    apply hu
    funext x
    by_cases hx : x ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hx
      exact congrFun h0 y
    · exact hsupp x hx
  have hER : (A.submatrix f f) *ᵥ (fun y => u (f y)) = E • fun y => u (f y) := by
    funext y
    have h1 := congrFun hE (f y)
    rw [hsum] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  exact not_isCoprime_of_isRoot (charpoly_isRoot_of_mulVec_eq_smul A hu hE)
    (charpoly_isRoot_of_mulVec_eq_smul _ huR hER) hcop

/-- **Selected-energy/exterior common-spectrum avoidance.**  For every exposed block
`j`, almost surely no ordered eigenvalue of the normalized physical matrix is an
eigenvalue of its exterior minor outside block `j`: the event
`physicalCommonSpectrumFreeEvent j` has probability one. -/
theorem Law.ae_mem_physicalCommonSpectrumFreeEvent {p : Params} (M : Law p)
    (j : Fin p.n) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalCommonSpectrumFreeEvent j := by
  filter_upwards [M.ae_isCoprime_normalizedPhysical_exterior_charpoly j] with ω hω
  simp only [Law.physicalCommonSpectrumFreeEvent, Set.mem_iInter,
    Law.physicalSelectedEnergyExteriorPoleFreeEvent, Set.mem_ofPred_eq]
  intro r s hrs
  have h1 := charpoly_isRoot_orderedEigenvalue (M.normalizedPhysicalMatrix ω) r
  have h2 := charpoly_isRoot_orderedEigenvalue (M.normalizedPhysicalExteriorMatrix j ω) s
  rw [hrs] at h2
  exact not_isCoprime_of_isRoot h1 h2 hω

/-- For every ordered rank, the selected energy almost surely avoids the exterior
spectrum. -/
theorem Law.ae_mem_physicalSelectedEnergyExteriorPoleFreeEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalSelectedEnergyExteriorPoleFreeEvent j r := by
  filter_upwards [M.ae_mem_physicalCommonSpectrumFreeEvent j] with ω hω
  exact Set.mem_iInter.mp hω r

/-- On simple spectrum, coprimality of the full and exterior characteristic
polynomials forces every canonical ordered eigenvector to charge the exposed block. -/
theorem physicalMeasurableBlockMassWeight_pos_of_isCoprime {p : Params}
    (A : HermitianMatrix (PhysicalIndex p)) (hA : A ∈ physicalSimpleSpectrumMatrices p)
    (j : Fin p.n)
    (hcop : IsCoprime A.1.charpoly
      (A.1.submatrix (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p)
        Subtype.val).charpoly)
    (r : Fin (PhysicalDimension p)) :
    0 < physicalMeasurableBlockMassWeight p r A j := by
  set w := physicalSimpleOrderedEigenvectorFin p r ⟨A, hA⟩
  set φ := physicalIndexEquivFin p
  set u : PhysicalIndex p → ℂ := fun x => w (φ x)
  by_contra hpos
  have hzero : physicalMeasurableBlockMassWeight p r A j = 0 :=
    le_antisymm (not_lt.mp hpos) bot_le
  have hterm : ∀ a : Fin (physicalBlockSizes p j), u ⟨j, a⟩ = 0 := by
    intro a
    unfold physicalMeasurableBlockMassWeight at hzero
    rw [physicalMeasurableOrderedEigenvectorFin_apply_simple p r ⟨A, hA⟩] at hzero
    have h := (Finset.sum_eq_zero_iff.mp hzero) a (Finset.mem_univ a)
    have h' : ‖w (φ ⟨j, a⟩)‖₊ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    exact nnnorm_eq_zero.mp h'
  have hw := physicalSimpleOrderedEigenvectorFin_eigenvector p r ⟨A, hA⟩
  have hE : A.1 *ᵥ u = ((orderedEigenvalue (physicalHermitianFinReindex p A)
      (physicalEigenRank p r) : ℝ) : ℂ) • u := by
    funext x
    have h := congrFun hw (φ x)
    simp only [physicalHermitianFinReindex, Matrix.mulVec, dotProduct,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, u]
    rw [← Equiv.sum_comp φ.symm]
    simp only [Equiv.apply_symm_apply]
    convert h using 1
    · simp [φ, w]
    · rfl
  have hu : u ≠ 0 := by
    intro h0
    have hn : ‖w‖ = 1 := norm_physicalSimpleOrderedEigenvectorFin p r ⟨A, hA⟩
    have : w = 0 := by
      ext z
      have := congrFun h0 (φ.symm z)
      simpa [u] using this
    rw [this, norm_zero] at hn
    exact zero_ne_one hn
  refine eigenvector_ne_zero_off_exterior A.1
    (Subtype.val : PhysicalExteriorIndex p j → PhysicalIndex p) Subtype.val_injective
    hcop hu hE ?_
  rintro ⟨k, a⟩ hx
  have hk : k = j := by
    by_contra hk
    exact hx ⟨⟨⟨k, a⟩, hk⟩, rfl⟩
  subst hk
  exact hterm a

/-- **Positive exposed mass.**  For every exposed block `j` and ordered rank `r`, the
canonical exposed-block mass of the selected physical eigenline is almost surely
strictly positive. -/
theorem Law.ae_mem_physicalSelectedExposedMassPositiveEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalSelectedExposedMassPositiveEvent j r := by
  filter_upwards [M.ae_normalizedPhysicalMatrix_mem_physicalSimpleSpectrumMatrices,
    M.ae_isCoprime_normalizedPhysical_exterior_charpoly j] with ω hs hc
  exact physicalMeasurableBlockMassWeight_pos_of_isCoprime _ hs j hc r

/-- **The physical coarea exceptional events are null.**  For every exposed block `j`,
almost surely the normalized physical matrix has simple spectrum, every selected energy
avoids the exterior spectrum, and every selected eigenline has positive exposed mass:
the event `physicalCoareaGoodEvent j` of `PhysicalCoareaExceptionalNull` has
probability one.

This is the exceptional-set step of the coarea theorem, for the exact law at fixed
`n ≥ 4`, `W ≥ 1`, `0 < b < 1/2`; all ranks simultaneously; no limit. -/
theorem Law.ae_mem_physicalCoareaGoodEvent {p : Params} (M : Law p) (j : Fin p.n) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalCoareaGoodEvent j := by
  have hall : ∀ᵐ ω ∂M.P, ∀ r : Fin (PhysicalDimension p),
      ω ∈ M.physicalSelectedCoareaGoodEvent j r := by
    rw [ae_all_iff]
    intro r
    filter_upwards [M.ae_mem_physicalFullSimpleSpectrumEvent,
      M.ae_mem_physicalSelectedEnergyExteriorPoleFreeEvent j r,
      M.ae_mem_physicalSelectedExposedMassPositiveEvent j r] with ω h1 h2 h3
    exact ⟨⟨h1, h2⟩, h3⟩
  filter_upwards [hall] with ω hω
  exact Set.mem_iInter.mpr hω

/-- The complement of the selected-rank physical coarea good event is null; this is the
hypothesis of `lintegral_restrict_eq_of_compl_null` in `PhysicalConditionalCoarea`. -/
theorem Law.measure_compl_physicalSelectedCoareaGoodEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    M.P (M.physicalSelectedCoareaGoodEvent j r)ᶜ = 0 := by
  have h : ∀ᵐ ω ∂M.P, ω ∈ M.physicalSelectedCoareaGoodEvent j r := by
    filter_upwards [M.ae_mem_physicalCoareaGoodEvent j] with ω hω
    exact Set.mem_iInter.mp hω r
  exact ae_iff.mp h

/-- The physical coarea good event has probability one. -/
theorem Law.measure_physicalCoareaGoodEvent {p : Params} (M : Law p) (j : Fin p.n) :
    M.P (M.physicalCoareaGoodEvent j) = 1 := by
  rw [← prob_compl_eq_zero_iff (M.measurableSet_physicalCoareaGoodEvent j)]
  exact ae_iff.mp (M.ae_mem_physicalCoareaGoodEvent j)

/-- **Positive pair mass.**  Almost surely, for every ordered rank `α` and every two
blocks `i, j`, the pair mass of the ordered normalized physical eigenvector used by
`PhysicalPairMassLaw` is strictly positive.  (Already its mass on block `i` is
positive, by common-spectrum exclusion for the exterior of block `i`.) -/
theorem Law.ae_physicalOrderedPairMass_pos {p : Params} (M : Law p) :
    ∀ᵐ ω ∂M.P, ∀ (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
      (i j : Fin p.n), 0 < M.physicalOrderedPairMass ω α i j := by
  have hall : ∀ᵐ ω ∂M.P, ∀ i : Fin p.n,
      IsCoprime (M.normalizedPhysicalMatrix ω).1.charpoly
        (M.normalizedPhysicalExteriorMatrix i ω).1.charpoly := by
    rw [ae_all_iff]
    exact M.ae_isCoprime_normalizedPhysical_exterior_charpoly
  filter_upwards [hall] with ω hω
  intro α i j
  set N := M.normalizedPhysicalMatrix ω
  set v := orderedNormalizedEigenvector N α
  have hpos : 0 < physicalBlockMassWeight p v i := by
    by_contra hle
    have hzero : physicalBlockMassWeight p v i = 0 := le_antisymm (not_lt.mp hle) bot_le
    have hterm : ∀ a : Fin (physicalBlockSizes p i), v ⟨i, a⟩ = 0 := by
      intro a
      have h := (Finset.sum_eq_zero_iff.mp hzero) a (Finset.mem_univ a)
      have h' : ‖v ⟨i, a⟩‖₊ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      exact nnnorm_eq_zero.mp h'
    have hv : (fun x => v x) ≠ 0 := by
      intro h0
      have hn : ‖v‖ = 1 := norm_orderedNormalizedEigenvector N α
      have : v = 0 := by
        ext x
        exact congrFun h0 x
      rw [this, norm_zero] at hn
      exact zero_ne_one hn
    refine eigenvector_ne_zero_off_exterior N.1
      (Subtype.val : PhysicalExteriorIndex p i → PhysicalIndex p) Subtype.val_injective
      (hω i) hv (orderedNormalizedEigenvector_eigenvector N α) ?_
    rintro ⟨k, a⟩ hx
    have hk : k = i := by
      by_contra hk
      exact hx ⟨⟨⟨k, a⟩, hk⟩, rfl⟩
    subst hk
    exact hterm a
  exact add_pos_of_pos_of_nonneg hpos bot_le

end GaussianRing
end CoareaNative.BlockBand
