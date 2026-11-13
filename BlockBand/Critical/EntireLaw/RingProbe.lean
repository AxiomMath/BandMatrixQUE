module

public import BlockBand.Critical.EntireLaw.EntireGrowth
public import BlockBand.Critical.EntireLaw.ProbeTightness
public import BlockBand.Critical.EntireLaw.FiniteMoment

/-!
# The entire law: the one-probe matrices of the ring

For a profile `Q_a`, `oneProbeMatrix` is `A_a = D_a R D_a` with `D_a = diag(√(W⁻² Q_a(j/n)))` and
`R = (H - E)⁻¹`, so that the one-probe variable of the ring is `g^* A_a g`. The file relates
`Tr A_a` and `‖A_a‖_HS` to the quantities in the growth bound of `D_W`, and transfers the law of the
one-probe variable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Matrix Set
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.CriticalEntire

variable {p : Parameters}

/-- The one-probe matrix `A_a = D_a R D_a`, `D_a = diag(√(W⁻² Q_a(j/n)))`, `R = (H - E)⁻¹`:
the ring probe `ζ = W⁻¹ Q_a^{1/2} g` has `ζ^* R ζ = g^* A_a g`. -/
def oneProbeMatrix (p : Parameters) (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (a : Fin m)
    (H : p.SiteMatrix) : p.SiteMatrix :=
  coneRootDiag p Q (Pi.single a 1) * (H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹ *
    coneRootDiag p Q (Pi.single a 1)

theorem isHermitian_oneProbeMatrix (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (a : Fin m)
    {H : p.SiteMatrix} (hH : H.IsHermitian) : (oneProbeMatrix p E Q a H).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose (coneRootDiag p Q (Pi.single a 1))
    (isHermitian_resolvent hH E)
  rwa [coneRootDiag_conjTranspose] at h

theorem measurable_oneProbeMatrix (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (a : Fin m) :
    Measurable (oneProbeMatrix p E Q a) := by
  have hinv : Measurable fun H : p.SiteMatrix => (H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹ :=
    BlockBand.Critical.GlobalSource.measurable_matrix_inv.comp
      (continuous_id.sub continuous_const).measurable
  have hc : Continuous fun M : p.SiteMatrix =>
      coneRootDiag p Q (Pi.single a 1) * M * coneRootDiag p Q (Pi.single a 1) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact hc.measurable.comp hinv

theorem sum_single_smul {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (a : Fin m) :
    ∑ b, (Pi.single a (1 : ℝ) : Fin m → ℝ) b • Q b = Q a := by
  simp [Pi.single_apply]

/-- The one-probe variable of the ring is the quadratic form of `A_a`. -/
theorem ringSourceMatrix_one_eq (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (a : Fin m)
    (H : p.SiteMatrix) (g : Fin 1 → p.Site → ℂ) :
    ringSourceMatrix p E (fun _ : Fin 1 => Q a) H g 0 0 =
      probeForm (oneProbeMatrix p E Q a H) (g 0) := by
  show star (ringProbeVector p (Q a) (g 0)) ⬝ᵥ
      ((H - (E : ℂ) • 1)⁻¹ *ᵥ ringProbeVector p (Q a) (g 0)) = _
  rw [← sum_single_smul Q a, ringProbeVector_eq_mulVec, star_mulVec_dotProduct_mulVec,
    coneRootDiag_conjTranspose]
  rfl

theorem coneRootDiag_mul_self {m : ℕ} {Q : Fin m → C(Torus, ℝ)} (hQ : ∀ a t, 0 ≤ Q a t)
    (a : Fin m) :
    coneRootDiag p Q (Pi.single a 1) * coneRootDiag p Q (Pi.single a 1) =
      BlockBand.Critical.widthSourceScale p.W • p.profileSourceMatrix (Q a) := by
  have hw : ∀ x : p.Site, coneWeight p Q (Pi.single a 1) x =
      ((p.W : ℝ)⁻¹) ^ 2 * Q a (p.ringProfilePoint x.1) := by
    intro x
    simp [coneWeight, Pi.single_apply]
  ext x x'
  by_cases hxx : x = x'
  · subst hxx
    simp only [coneRootDiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, Parameters.profileSourceMatrix, smul_eq_mul,
      BlockBand.Critical.widthSourceScale]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (coneWeight_nonneg hQ
      (fun b => by simp only [Pi.single_apply]; split_ifs <;> norm_num) x), hw]
    push_cast
    ring
  · simp [coneRootDiag, Parameters.profileSourceMatrix, Matrix.diagonal_apply_ne _ hxx]

/-- `W⁻² Tr(R Q_a) = Tr A_a`. -/
theorem profileTrace_eq_trace (E : ℝ) {m : ℕ} {Q : Fin m → C(Torus, ℝ)} (hQ : ∀ a t, 0 ≤ Q a t)
    (H : p.SiteMatrix) (a : Fin m) :
    profileTrace p E Q H a = (oneProbeMatrix p E Q a H).trace := by
  unfold profileTrace oneProbeMatrix
  rw [Matrix.trace_mul_comm, ← coneRootDiag_mul_self hQ a]
  exact (Matrix.trace_mul_cycle _ _ _).symm

/-- `‖W⁻² R‖²_HS = ‖A_0‖²_HS` for the full profile family (`Q_0 = 1`). -/
theorem scaledResolventHS_eq_hsSq (E : ℝ) {k : ℕ} (q : Fin k → C(Torus, ℝ)) (H : p.SiteMatrix) :
    scaledResolventHS p E H = hsSq (oneProbeMatrix p E (fullProfile q) 0 H) := by
  have hd : coneRootDiag p (fullProfile q) (Pi.single 0 1) =
      Matrix.diagonal fun _ : p.Site => (((p.W : ℝ)⁻¹ : ℝ) : ℂ) := by
    unfold coneRootDiag
    congr 1
    funext x
    have : coneWeight p (fullProfile q) (Pi.single 0 1) x = ((p.W : ℝ)⁻¹) ^ 2 := by
      simp [coneWeight, Pi.single_apply, fullProfile]
    rw [this, Real.sqrt_sq (inv_nonneg.mpr (Nat.cast_nonneg _))]
  unfold scaledResolventHS hsSq oneProbeMatrix
  rw [hd]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul,
    BlockBand.Critical.widthSourceScale]
  congr 2
  push_cast
  ring

/-- Transfer of the one-probe law: the `J = 1` law of `fullRingProbeLaw` and the product with
one circular Gaussian vector give the same tail of the one-probe variable. -/
theorem measureReal_ringSource_eq (model : p.GaussianRingModel) (E : ℝ) {m : ℕ}
    (Q : Fin m → C(Torus, ℝ)) (a : Fin m) (M : ℝ) :
    (fullRingProbeLaw model 1).real
        {x | M < ‖ringSourceMatrix p E (fun _ : Fin 1 => Q a) x.1 x.2 0 0‖} =
      ((model.law : Measure p.SiteMatrix).prod (circularVectorLaw p.Site)).real
        {x | M < ‖probeForm (oneProbeMatrix p E Q a x.1) x.2‖} := by
  set f : p.SiteMatrix × (Fin 1 → p.Site → ℂ) → p.SiteMatrix × (p.Site → ℂ) :=
    Prod.map id (Function.eval 0)
  have hf : Measurable f := measurable_id.prodMap (measurable_pi_apply 0)
  have hmap : (fullRingProbeLaw model 1).map f =
      (model.law : Measure p.SiteMatrix).prod (circularVectorLaw p.Site) := by
    unfold fullRingProbeLaw
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply 0), Measure.map_id,
      Measure.pi_map_eval]
    simp
  have hS : MeasurableSet {x : p.SiteMatrix × (p.Site → ℂ) |
      M < ‖probeForm (oneProbeMatrix p E Q a x.1) x.2‖} :=
    measurableSet_lt measurable_const
      (measurable_probeForm_comp (measurable_oneProbeMatrix E Q a)).norm
  rw [← hmap, map_measureReal_apply hf hS]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, f, Prod.map_fst, Prod.map_snd, id, Function.eval,
    ringSourceMatrix_one_eq]

end BlockBand.Critical.EntireLaw
