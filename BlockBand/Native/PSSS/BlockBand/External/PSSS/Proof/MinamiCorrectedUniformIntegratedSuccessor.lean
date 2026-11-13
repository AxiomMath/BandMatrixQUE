module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedUniformSuccessor

/-!
# Uniform integration of the corrected Minami successor

This module retains the single corrected-mesh constant outside the order,
dimensions, and induction hypothesis while carrying it through exterior,
energy, Cauchy, and radial integration.  The coefficient remains exactly `10`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 12000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The exact, order-independent content of the corrected single-sample mesh
estimate. -/
def UniformCorrectedMeshBound (C : ℝ) : Prop :=
  ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      (Gext : BlockProductDisintegration.ExteriorSample dims j)
      (e t a b xi : ℝ), 0 < xi → ∀ (M r : ℕ),
      (∫⁻ φ, ∫⁻ Gj,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) ≤
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ENNReal.ofReal (10 * C * dims j * xi) *
        (∫⁻ φ, ∫⁻ Gj,
          fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j)) *
        ENNReal.ofReal (poissonRadialWeight eta xi)

/-- The primitive mesh theorem supplies one `UniformCorrectedMeshBound`
constant before every order and dimension. -/
theorem exists_uniformCorrectedMeshBound :
    ∃ C : ℝ, 1 ≤ C ∧ UniformCorrectedMeshBound C :=
  orderIndependent_correctedMeshConstant

/-- Exterior integration preserves a previously fixed mesh constant. -/
theorem exterior_correctedMesh_finiteStage_le_of_uniform
    {C : ℝ} (hmesh : UniformCorrectedMeshBound C)
    {C₀ : ℝ} {r : ℕ} (hind : PublicFactorialAtOrder C₀ r) :
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      {a b : ℝ} (_hab : a ≤ b) (e t xi : ℝ), 0 < xi → ∀ M,
      (∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j) ≤
      2 * (ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ENNReal.ofReal (10 * C * dims j * xi) *
        ENNReal.ofReal (C₀ * (∑ i, (dims i : ℝ)) * (b - a)) ^ r *
        ENNReal.ofReal (poissonRadialWeight eta xi)) := by
  intro k dims hd j A₀ eta heta a b _hab e t xi hxi M
  unfold UniformCorrectedMeshBound at hmesh
  let K : ℝ≥0∞ := ENNReal.ofReal (1 / Real.pi) *
    ENNReal.ofReal (standardCauchyWeight t) *
    ENNReal.ofReal (10 * C * dims j * xi) *
    ENNReal.ofReal (poissonRadialWeight eta xi)
  let W := fun Gext : BlockProductDisintegration.ExteriorSample dims j =>
    ∫⁻ φ, ∫⁻ Gj,
      fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂uniformSphere (dims j)
  have hW : Measurable W := by
    let f := fun p : BlockProductDisintegration.ExteriorSample dims j ×
        EuclideanSpace ℂ (Fin (dims j)) =>
      ∫⁻ Gj, fixedSelectedPredecessorWeight A₀ j p.2 a b r (p.1, Gj)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
    have hf : Measurable f := by
      let pull := fun q :
          (BlockProductDisintegration.ExteriorSample dims j ×
            EuclideanSpace ℂ (Fin (dims j))) ×
              BlockProductDisintegration.SelectedSample dims j =>
        (q.1.2, (q.1.1, q.2))
      have hpull : Measurable pull :=
        (measurable_snd.comp measurable_fst).prodMk
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have hjoint := (measurable_joint_fixedSelectedPredecessorWeight
        dims A₀ j a b r).comp hpull
      let g := fun p : BlockProductDisintegration.ExteriorSample dims j ×
          EuclideanSpace ℂ (Fin (dims j)) =>
        fun Gj : BlockProductDisintegration.SelectedSample dims j =>
          fixedSelectedPredecessorWeight A₀ j p.2 a b r (p.1, Gj)
      have hg : Measurable (Function.uncurry g) := by
        change Measurable (fun x :
          (BlockProductDisintegration.ExteriorSample dims j ×
            EuclideanSpace ℂ (Fin (dims j))) ×
              BlockProductDisintegration.SelectedSample dims j =>
          fixedSelectedPredecessorWeight A₀ j x.1.2 a b r (x.1.1, x.2))
        exact hjoint
      exact hg.lintegral_prod_right
    exact hf.lintegral_prod_right
  calc
    _ = ∫⁻ Gext, 2 * ∫⁻ φ, ∫⁻ Gj,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
      apply lintegral_congr
      intro Gext
      apply congrArg (fun z : ℝ≥0∞ => 2 * z)
      exact lintegral_lintegral_swap
        (((measurable_correctedMeshEventKernel
          dims A₀ j heta Gext a b M r).comp (by fun_prop)).aemeasurable)
    _ ≤ ∫⁻ Gext, 2 * (K * W Gext)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
      apply lintegral_mono
      intro Gext
      have hm := hmesh dims hd j A₀ heta Gext e t a b xi hxi M r
      simpa only [K, W, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_right hm 2)
    _ = 2 * K * ∫⁻ Gext, W Gext
        ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
      rw [show (fun Gext => 2 * (K * W Gext)) =
          fun Gext => (2 * K) * W Gext by funext Gext; ac_rfl,
        MeasureTheory.lintegral_const_mul _ hW]
    _ ≤ 2 * K * ENNReal.ofReal
        (C₀ * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
      gcongr
      exact lintegral_exterior_uniformSphere_fixedSelectedPredecessor_le
        hind dims hd j A₀ _hab
    _ = _ := by unfold K; ac_rfl
/-- With a fixed mesh constant, the radial identity absorbs the single
sphere-insertion factor two and returns the exact
coefficient `10`; Cauchy mass is one and energy contributes `b-a`. -/
theorem parameterProduct_correctedMesh_finiteStage_le_of_uniform
    {C : ℝ} (hC : 1 ≤ C) (hmesh : UniformCorrectedMeshBound C)
    {C₀ : ℝ} {r : ℕ} (hind : PublicFactorialAtOrder C₀ r) :
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      {a b : ℝ} (_hab : a ≤ b) (M : ℕ),
      let μp := ((volume.restrict (Set.Ioc a b)).prod volume).prod
        (volume.restrict (Set.Ioi 0))
      (∫⁻ q, ∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), q)
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j ∂μp) ≤
      ENNReal.ofReal (b - a) * ENNReal.ofReal (10 * C * dims j) *
        ENNReal.ofReal (C₀ * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  intro k dims hd j A₀ eta heta a b _hab M
  have hstage := exterior_correctedMesh_finiteStage_le_of_uniform
    (k := k) hmesh hind
  dsimp only
  let F := fun q : (ℝ × ℝ) × ℝ =>
    ∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
      correctedMeshEventKernel A₀ j heta Gext a b M r ((φ, Gj), q)
      ∂uniformSphere (dims j)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j
  have hF : Measurable F :=
    measurable_parameters_exterior_selected_sphere_correctedMesh
      dims hd A₀ j heta a b M r
  let D : ℝ≥0∞ := ENNReal.ofReal
    (C₀ * (∑ i, (dims i : ℝ)) * (b - a)) ^ r
  let T : ℝ≥0∞ := ENNReal.ofReal (10 * C * dims j)
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hrad : ∀ t : ℝ,
      (∫⁻ xi : ℝ in Set.Ioi 0,
        2 * (ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (standardCauchyWeight t) *
          ENNReal.ofReal (10 * C * dims j * xi) * D *
          ENNReal.ofReal (poissonRadialWeight eta xi))) =
        ENNReal.ofReal (standardCauchyWeight t) * D * T := by
    intro t
    let R := fun xi : ℝ =>
      ENNReal.ofReal (10 * C * dims j * xi) *
        ENNReal.ofReal (poissonRadialWeight eta xi)
    have hR : Measurable R := by
      unfold R poissonRadialWeight
      fun_prop
    calc
      _ = ∫⁻ xi : ℝ in Set.Ioi 0,
          (ENNReal.ofReal (standardCauchyWeight t) * D) *
            ((2 * ENNReal.ofReal (1 / Real.pi)) * R xi) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro xi hxi
        unfold R
        ac_rfl
      _ = (ENNReal.ofReal (standardCauchyWeight t) * D) *
          (∫⁻ xi : ℝ in Set.Ioi 0,
            (2 * ENNReal.ofReal (1 / Real.pi)) * R xi) := by
        rw [MeasureTheory.lintegral_const_mul]
        exact measurable_const.mul hR
      _ = (ENNReal.ofReal (standardCauchyWeight t) * D) *
          (2 * ENNReal.ofReal (1 / Real.pi) *
            (∫⁻ xi : ℝ in Set.Ioi 0, R xi)) := by
        rw [MeasureTheory.lintegral_const_mul]
        exact hR
      _ = ENNReal.ofReal (standardCauchyWeight t) * D * T := by
        rw [two_mul_normalized_correctedMesh_radial_eq_ten
          heta hC0 (dims j)]
  calc
    (∫⁻ q, F q
      ∂((volume.restrict (Set.Ioc a b)).prod volume).prod
        (volume.restrict (Set.Ioi 0))) =
      ∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ t : ℝ, ∫⁻ xi : ℝ in Set.Ioi 0,
        F ((e, t), xi) := by
      rw [MeasureTheory.lintegral_prod F hF.aemeasurable]
      let g := fun et : ℝ × ℝ =>
        ∫⁻ xi : ℝ in Set.Ioi 0, F (et, xi)
      have hg : Measurable g := hF.lintegral_prod_right
      rw [MeasureTheory.lintegral_prod g hg.aemeasurable]
    _ ≤ ∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ t : ℝ, ∫⁻ xi : ℝ in Set.Ioi 0,
        2 * (ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (standardCauchyWeight t) *
          ENNReal.ofReal (10 * C * dims j * xi) * D *
          ENNReal.ofReal (poissonRadialWeight eta xi)) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro e he
      apply lintegral_mono
      intro t
      apply setLIntegral_mono' measurableSet_Ioi
      intro xi hxi
      simpa only [F, D] using
        hstage dims hd j A₀ heta _hab e t xi hxi M
    _ = ∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ t : ℝ,
        ENNReal.ofReal (standardCauchyWeight t) * D * T := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro e he
      apply lintegral_congr
      intro t
      exact hrad t
    _ = ∫⁻ e : ℝ in Set.Ioc a b, D * T := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro e he
      rw [show (fun t : ℝ => ENNReal.ofReal (standardCauchyWeight t) * D * T) =
          fun t => (D * T) * ENNReal.ofReal (standardCauchyWeight t) by
        funext t; ac_rfl,
        MeasureTheory.lintegral_const_mul' _ _]
      · rw [lintegral_ofReal_standardCauchyWeight, mul_one]
      · exact ENNReal.mul_ne_top (by simp [D]) (by simp [T])
    _ = ENNReal.ofReal (b - a) * T * D := by
      simp [Real.volume_Ioc]
      ac_rfl
    _ = _ := by unfold T D; ac_rfl

/-- Final integration of the corrected common-mesh Fatou bound.  The same
mesh index occurs under all three parameter integrals; its uniform finite
stage estimate is passed through `liminf` only after the radial, Cauchy, and
energy integrations have been evaluated.  Thus the coefficient is exactly
`10`, and the statement is also exact when `a = b` (both sides vanish). -/
theorem parameterProduct_lintegral_normalizedOpenCount_le_ten_of_uniform
    {C : ℝ} (hC : 1 ≤ C) (hmesh : UniformCorrectedMeshBound C)
    {C₀ : ℝ} {r : ℕ} (hind : PublicFactorialAtOrder C₀ r) :
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      {a b : ℝ} (_hab : a ≤ b),
      let μp := ((volume.restrict (Set.Ioc a b)).prod volume).prod
        (volume.restrict (Set.Ioi 0))
      (∫⁻ q, ∫⁻ Gext, ∫⁻ Gj,
        ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (standardCauchyWeight q.1.2) *
          ((eigenCount
            (correctedSelectedAuxiliaryHermitian A₀ j heta
              ((((Gext, Gj), q.1.1), q.1.2), q.2))
              (Set.Ioo (-q.2) q.2) : ℝ≥0∞) *
            fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
          ENNReal.ofReal (poissonRadialWeight eta q.2)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j ∂μp) ≤
      ENNReal.ofReal (b - a) * ENNReal.ofReal (10 * C * dims j) *
        ENNReal.ofReal
          (C₀ * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  intro k dims hd j A₀ eta heta a b hab
  have hstage := parameterProduct_correctedMesh_finiteStage_le_of_uniform
    (k := k) hC hmesh hind
  dsimp only
  refine (parameterProduct_lintegral_normalizedOpenCount_le_liminf_mesh
    dims hd j A₀ heta hab r).trans ?_
  let B : ℝ≥0∞ :=
    ENNReal.ofReal (b - a) * ENNReal.ofReal (10 * C * dims j) *
      ENNReal.ofReal
        (C₀ * (∑ i, (dims i : ℝ)) * (b - a)) ^ r
  calc
    liminf (fun M => ∫⁻ q, ∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r ((φ, Gj), q)
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j
        ∂(((volume.restrict (Set.Ioc a b)).prod volume).prod
          (volume.restrict (Set.Ioi 0)))) atTop ≤
      liminf (fun _M : ℕ => B) atTop := by
        refine liminf_le_liminf ?_ (by isBoundedDefault)
          (by isBoundedDefault)
        filter_upwards with M
        exact hstage dims hd j A₀ heta hab M
    _ = B := by simp
    _ = _ := rfl

/-- Increasing the single-block DOS constant preserves the estimate. -/
theorem SingleBlockDOS.mono_constant {C C' : ℝ}
    (h : SingleBlockDOS C) (hCC' : C ≤ C') : SingleBlockDOS C' := by
  intro N hN A a b hab
  refine (h N hN A a b hab).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hdim : 0 ≤ (N : ℝ) := by positivity
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC' hdim) hlen

/-- Uniform bound for every weighted Perron approximant after summing the
selected blocks.  The same mesh constant works for all orders. -/
theorem lintegral_publicBlockWeightedPerronApprox_le_uniform_ten
    {Cmesh : ℝ} (hCmesh : 1 ≤ Cmesh)
    (hmesh : UniformCorrectedMeshBound Cmesh)
    {C : ℝ} {r : ℕ} (hind : PublicFactorialAtOrder C r)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (∫⁻ G, publicBlockWeightedPerronApprox A₀ a b r n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ENNReal.ofReal (b - a) *
      ENNReal.ofReal (10 * Cmesh * (∑ i, (dims i : ℝ))) *
      ENNReal.ofReal
        (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  refine (lintegral_publicBlockWeightedPerronApprox_le_sum_parameterProduct
    dims hd A₀ hab r n).trans ?_
  calc
    _ ≤ ∑ j : Fin k,
        ENNReal.ofReal (b - a) *
          ENNReal.ofReal (10 * Cmesh * dims j) *
          ENNReal.ofReal
            (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
      apply Finset.sum_le_sum
      intro j hj
      exact parameterProduct_lintegral_normalizedOpenCount_le_ten_of_uniform
        (k := k) hCmesh hmesh hind dims hd j A₀
          (canonicalWegnerEta_pos n) hab
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      congr 1
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        rw [Finset.mul_sum]
      · intro j hj
        positivity

/-- A fixed threshold absorbs the coefficient `10 Cmesh` and turns the
uniform Perron bound into the order-`r+1` normalization. -/
theorem lintegral_publicBlockWeightedPerronApprox_le_successorPower
    {Cmesh : ℝ} (hCmesh : 1 ≤ Cmesh)
    (hmesh : UniformCorrectedMeshBound Cmesh)
    {C : ℝ} (hC : 10 * Cmesh ≤ C) {r : ℕ}
    (hind : PublicFactorialAtOrder C r)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (∫⁻ G, publicBlockWeightedPerronApprox A₀ a b r n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ENNReal.ofReal
      (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ (r + 1) := by
  refine (lintegral_publicBlockWeightedPerronApprox_le_uniform_ten
    hCmesh hmesh hind dims hd A₀ hab n).trans ?_
  let S : ℝ := ∑ i, (dims i : ℝ)
  let L : ℝ := b - a
  have hS : 0 ≤ S := by unfold S; positivity
  have hL : 0 ≤ L := by exact sub_nonneg.mpr hab
  have hcoef : 10 * Cmesh * S * L ≤ C * S * L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC hS) hL
  calc
    ENNReal.ofReal L * ENNReal.ofReal (10 * Cmesh * S) *
        ENNReal.ofReal (C * S * L) ^ r =
      ENNReal.ofReal (10 * Cmesh * S * L) *
        ENNReal.ofReal (C * S * L) ^ r := by
          rw [← ENNReal.ofReal_mul hL]
          congr 2
          ring
    _ ≤ ENNReal.ofReal (C * S * L) *
        ENNReal.ofReal (C * S * L) ^ r := by
      gcongr
    _ = ENNReal.ofReal (C * S * L) ^ (r + 1) := by
      rw [pow_succ]
      ac_rfl
    _ = _ := rfl

/-- Order-independent successor bound for the public-law factorial.  The threshold simultaneously
dominates the absolute single-block DOS constant and the corrected mesh
coefficient.  No constant depends on the order. -/
theorem exists_orderIndependent_publicFactorial_successor :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {C : ℝ}, K ≤ C → ∀ {r : ℕ},
        PublicFactorialAtOrder C r →
        PublicFactorialAtOrder C (r + 1) := by
  obtain ⟨Cmesh, hCmesh, hmesh⟩ := exists_uniformCorrectedMeshBound
  obtain ⟨Cdos, hCdos, hdos⟩ := singleBlock_dos
  let K := max Cdos (10 * Cmesh)
  have hK : 1 ≤ K := le_trans hCdos (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro C hKC r hind k dims hd A₀ a b hab
  have hdosC : SingleBlockDOS C :=
    hdos.mono_constant ((le_max_left _ _).trans hKC)
  have hmeshC : 10 * Cmesh ≤ C :=
    (le_max_right _ _).trans hKC
  rcases hab.eq_or_lt with rfl | hablt
  · rw [publicBlock_lintegral_factorial_succ_Icc_self_eq_zero
      (le_trans hK hKC) hdosC dims hd A₀ a r]
    exact bot_le
  · refine (publicBlock_lintegral_factorial_succ_le_liminf_weightedPerron
      (le_trans hK hKC) hdosC dims hd A₀ hablt r).trans ?_
    let B : ℝ≥0∞ :=
      ENNReal.ofReal
        (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ (r + 1)
    calc
      liminf (fun n => ∫⁻ G,
          publicBlockWeightedPerronApprox A₀ a b r n G
          ∂BlockGUE.publicBlockProductMeasure dims hd) atTop ≤
          liminf (fun _n : ℕ => B) atTop := by
        refine liminf_le_liminf ?_ (by isBoundedDefault)
          (by isBoundedDefault)
        filter_upwards with n
        exact lintegral_publicBlockWeightedPerronApprox_le_successorPower
          hCmesh hmesh hmeshC hind dims hd A₀ hablt.le n
      _ = B := by simp
      _ = _ := rfl

end PSSSNative.BlockBand.PSSS
