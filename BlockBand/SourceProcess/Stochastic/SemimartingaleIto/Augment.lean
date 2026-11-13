module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Calculus
public import BlockBand.Internal.Contracts.Transmission
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The augmented state `(t, a, y) ∈ ℝ^{d+2}`)

Coordinates of `z : Fin (d+2) → ℝ`: `z 0` = time, `z 1` = the compensator coordinate `a`,
`z (i+2)` = `y_i`. `projL d z = (z 0, y)`, `projA d z = z 1`. For
`φ : ℝ × ℝ^d → ℝ` of class `C²` on `univ ×ˢ U`, `hAug φ z = φ(z 0, y) - z 1` is `C²` on
`augSet U = projL⁻¹(univ ×ˢ U)`. With drift `consAug b₀ b₁ b` and covariance `embA a`
(zero outside the `y`-block):

* `schemeGen_hAug`: `𝓛 hAug = b₀ ∂_tφ - b₁ + Σ b_i ∂_iφ + ½ Σ a_{ij} ∂_i∂_jφ` (at `(z 0, y)`);
* `bracket_hAug`: `Σ_{kl} (embA a)_{kl} ∂_k hAug ∂_l hAug = Σ_{ij} a_{ij} ∂_iφ ∂_jφ`.

The partial derivatives are those of `BlockBand.Internal.Contracts.Transmission`.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ}

/-- `z ↦ (z 0, (z (i+2))_i)`. -/
def projL (d : ℕ) : (Fin (d + 2) → ℝ) →L[ℝ] ℝ × (Fin d → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℝ) 0).prod
    (ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℝ) i.succ.succ)

/-- `z ↦ z 1`. -/
def projA (d : ℕ) : (Fin (d + 2) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℝ) (Fin.succ 0)

theorem projL_apply (z : Fin (d + 2) → ℝ) : projL d z = (z 0, fun i => z i.succ.succ) := rfl

theorem projA_apply (z : Fin (d + 2) → ℝ) : projA d z = z (Fin.succ 0) := rfl

/-- `hAug φ z = φ(z 0, y) - z 1`. -/
def hAug (φ : ℝ × (Fin d → ℝ) → ℝ) (z : Fin (d + 2) → ℝ) : ℝ := φ (projL d z) - projA d z

/-- `projL⁻¹ (univ ×ˢ U)`. -/
def augSet (U : Set (Fin d → ℝ)) : Set (Fin (d + 2) → ℝ) := projL d ⁻¹' (univ ×ˢ U)

theorem isOpen_augSet {U : Set (Fin d → ℝ)} (hU : IsOpen U) : IsOpen (augSet U) :=
  (isOpen_univ.prod hU).preimage (projL d).continuous

theorem contDiffOn_hAug {U : Set (Fin d → ℝ)} {φ : ℝ × (Fin d → ℝ) → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U)) : ContDiffOn ℝ 2 (hAug φ) (augSet U) :=
  (hφ.comp (projL d).contDiff.contDiffOn (fun _ h => h)).sub (projA d).contDiff.contDiffOn

/-- The three-block vector `(b₀, b₁, b)`. -/
def consAug (b0 b1 : ℝ) (b : Fin d → ℝ) : Fin (d + 2) → ℝ := Fin.cons b0 (Fin.cons b1 b)

/-- The covariance `a` embedded in the `y`-block. -/
def embA (a : Fin d → Fin d → ℝ) : Fin (d + 2) → Fin (d + 2) → ℝ :=
  Fin.cons (0 : Fin (d + 2) → ℝ) (Fin.cons (0 : Fin (d + 2) → ℝ) fun i => consAug 0 0 (a i))

@[simp] theorem consAug_zero (b0 b1 : ℝ) (b : Fin d → ℝ) : consAug b0 b1 b 0 = b0 := rfl
@[simp] theorem consAug_one (b0 b1 : ℝ) (b : Fin d → ℝ) : consAug b0 b1 b (Fin.succ 0) = b1 :=
  rfl
@[simp] theorem consAug_ss (b0 b1 : ℝ) (b : Fin d → ℝ) (i : Fin d) :
    consAug b0 b1 b i.succ.succ = b i := rfl
@[simp] theorem embA_zero (a : Fin d → Fin d → ℝ) (l : Fin (d + 2)) : embA a 0 l = 0 := rfl
@[simp] theorem embA_one (a : Fin d → Fin d → ℝ) (l : Fin (d + 2)) :
    embA a (Fin.succ 0) l = 0 := rfl
@[simp] theorem embA_ss (a : Fin d → Fin d → ℝ) (i : Fin d) (l : Fin (d + 2)) :
    embA a i.succ.succ l = consAug 0 0 (a i) l := rfl

theorem consAug_zero_zero_zero : consAug 0 0 (0 : Fin d → ℝ) = 0 := by
  funext k; refine Fin.cases rfl (fun k => Fin.cases rfl (fun i => rfl) k) k

theorem embA_zero_eq : embA (0 : Fin d → Fin d → ℝ) = 0 := by
  funext k l
  refine Fin.cases rfl (fun k => Fin.cases rfl (fun i => ?_) k) k
  simp only [embA_ss]
  exact congrFun consAug_zero_zero_zero l

theorem ss_ne_one (i : Fin d) : (i.succ.succ : Fin (d + 2)) ≠ 1 := by
  rw [← Fin.succ_zero_eq_one]
  exact fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h)

theorem sum_aug (f : Fin (d + 2) → ℝ) :
    ∑ k, f k = f 0 + (f (Fin.succ 0) + ∑ i : Fin d, f i.succ.succ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]

theorem projL_ev0 : projL d (ev 0) = (1, 0) := by
  rw [projL_apply]; ext i
  · simp [ev]
  · simp [ev, Fin.succ_ne_zero]

theorem projL_ev1 : projL d (ev (Fin.succ 0)) = 0 := by
  rw [projL_apply]; ext i
  · simp [ev]
  · simp [ev, ss_ne_one]

theorem projL_evss (i : Fin d) : projL d (ev i.succ.succ) = (0, Pi.single i 1) := by
  rw [projL_apply]; ext j
  · simp [ev, (Fin.succ_ne_zero _).symm]
  · simp [ev, Pi.single_apply]

theorem projA_ev0 : projA d (ev 0) = 0 := by
  simp [projA_apply, ev]

theorem projA_ev1 : projA d (ev (Fin.succ 0)) = 1 := by simp [projA_apply, ev]

theorem projA_evss (i : Fin d) : projA d (ev i.succ.succ) = 0 := by
  simp [projA_apply, ev, (ss_ne_one i).symm]

variable {U : Set (Fin d → ℝ)} {φ : ℝ × (Fin d → ℝ) → ℝ}

theorem fderiv_hAug_apply (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {z : Fin (d + 2) → ℝ} (hz : z ∈ augSet U) (v : Fin (d + 2) → ℝ) :
    fderiv ℝ (hAug φ) z v = fderiv ℝ φ (projL d z) (projL d v) - projA d v := by
  have hO := isOpen_augSet (d := d) hU
  have hc : ContDiffOn ℝ 2 (fun y => φ (projL d y)) (augSet U) :=
    hφ.comp (projL d).contDiff.contDiffOn (fun _ h => h)
  rw [show hAug φ = fun y => φ (projL d y) - projA d y from rfl, fderiv_sub_clm hO hc _ hz]
  simp only [sub_apply]
  rw [fderiv_comp_clm_apply (isOpen_univ.prod hU) hφ (projL d) hz]

theorem fderiv2_hAug_apply (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {z : Fin (d + 2) → ℝ} (hz : z ∈ augSet U) (v w : Fin (d + 2) → ℝ) :
    fderiv ℝ (fderiv ℝ (hAug φ)) z v w =
      fderiv ℝ (fderiv ℝ φ) (projL d z) (projL d v) (projL d w) := by
  have hO := isOpen_augSet (d := d) hU
  have hc : ContDiffOn ℝ 2 (fun y => φ (projL d y)) (augSet U) :=
    hφ.comp (projL d).contDiff.contDiffOn (fun _ h => h)
  rw [show hAug φ = fun y => φ (projL d y) - projA d y from rfl, fderiv2_sub_clm hO hc _ hz,
    fderiv2_comp_clm_apply (isOpen_univ.prod hU) hφ (projL d) hz]

theorem fderiv_hAug_ev0 (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {z : Fin (d + 2) → ℝ} (hz : z ∈ augSet U) :
    fderiv ℝ (hAug φ) z (ev 0) = partialTime φ (projL d z) := by
  rw [fderiv_hAug_apply hU hφ hz, projL_ev0, projA_ev0, sub_zero]; rfl

theorem fderiv_hAug_ev1 (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {z : Fin (d + 2) → ℝ} (hz : z ∈ augSet U) :
    fderiv ℝ (hAug φ) z (ev (Fin.succ 0)) = -1 := by
  rw [fderiv_hAug_apply hU hφ hz, projL_ev1, projA_ev1, map_zero, zero_sub]

theorem fderiv_hAug_evss (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {z : Fin (d + 2) → ℝ} (hz : z ∈ augSet U) (i : Fin d) :
    fderiv ℝ (hAug φ) z (ev i.succ.succ) = partialSpace φ (projL d z) i := by
  rw [fderiv_hAug_apply hU hφ hz, projL_evss, projA_evss, sub_zero]; rfl

theorem fderiv2_hAug_evss (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {z : Fin (d + 2) → ℝ} (hz : z ∈ augSet U) (i j : Fin d) :
    fderiv ℝ (fderiv ℝ (hAug φ)) z (ev i.succ.succ) (ev j.succ.succ) =
      partialSpace2 φ (projL d z) i j := by
  rw [fderiv2_hAug_apply hU hφ hz, projL_evss, projL_evss]; rfl

variable {Ω : Type*}

/-- **Generator of `hAug φ`** for block characteristics. -/
theorem schemeGen_hAug (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    (Z β : ℝ≥0 → Ω → Fin (d + 2) → ℝ) (α : ℝ≥0 → Ω → Fin (d + 2) → Fin (d + 2) → ℝ)
    {u : ℝ≥0} {ω : Ω} (hz : Z u ω ∈ augSet U) {b0 b1 : ℝ} {b : Fin d → ℝ}
    {a : Fin d → Fin d → ℝ} (hβ : β u ω = consAug b0 b1 b) (hα : α u ω = embA a) :
    schemeGen (hAug φ) Z β α u ω = b0 * partialTime φ (projL d (Z u ω)) - b1 +
      ∑ i, b i * partialSpace φ (projL d (Z u ω)) i +
      (1 / 2) * ∑ i, ∑ j, a i j * partialSpace2 φ (projL d (Z u ω)) i j := by
  unfold schemeGen
  rw [hβ, hα, sum_aug, sum_aug]
  simp only [consAug_zero, consAug_one, consAug_ss, embA_zero, embA_one, embA_ss,
    zero_mul, Finset.sum_const_zero, zero_add,
    fderiv_hAug_ev0 hU hφ hz, fderiv_hAug_ev1 hU hφ hz, fderiv_hAug_evss hU hφ hz]
  congr 1
  · ring
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_aug]
    simp only [consAug_zero, consAug_one, consAug_ss, zero_mul, zero_add,
      fderiv2_hAug_evss hU hφ hz]

/-- **Bracket density of `hAug φ`** for block covariance. -/
theorem bracket_hAug (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {z : Fin (d + 2) → ℝ} (hz : z ∈ augSet U) (a : Fin d → Fin d → ℝ) :
    ∑ k, ∑ l, embA a k l * fderiv ℝ (hAug φ) z (ev k) * fderiv ℝ (hAug φ) z (ev l) =
      ∑ i, ∑ j, a i j * partialSpace φ (projL d z) i * partialSpace φ (projL d z) j := by
  rw [sum_aug]
  simp only [embA_zero, embA_one, embA_ss, zero_mul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_aug]
  simp only [consAug_zero, consAug_one, consAug_ss, zero_mul, zero_add,
    fderiv_hAug_evss hU hφ hz]

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
