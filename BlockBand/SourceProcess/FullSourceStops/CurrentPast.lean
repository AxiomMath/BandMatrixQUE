module

public import BlockBand.SourceProcess.FullSourceStops.CurrentSpectral
public import BlockBand.SourceProcess.FullSourceStops.WordValue
public import BlockBand.SourceProcess.FullSource.TagPath

/-!
# The current carrier along the path

Base length `k+1` (so the stop `stopEv b E W k d` starts there). `carrier b E W k i` is the
carrier at length `k+1+i`: `H_0 = cfc |·| J_{k+1}`, `H_{i+1} = NᴴH_iN`.
* `carrier_eq_past`, `measurable_carrierPast`: `H_i` is a measurable function of the past
  coordinates at length `k+1+i` (`extPast` extends a past sample by zeros; `cfc |·|` is
  measurable because it is continuous on the closed set of Hermitian matrices);
* `carrierPast_posSemidef`: every `H_i` is positive semidefinite (everywhere);
* `ae_carrier_sandwich`: a.s. `H_i ∓ J_{k+1+i} ⪰ 0` for all `i` (current conservation);
* `ae_trace_carrier_zero`: a.s. `Re Tr H_0 = 2 fracTrace (1/2) T_{k+1}` (`CurrentSpectral`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.FullSource
open scoped ComplexOrder

variable {W : ℕ}

/-!
## `|·|` through the continuous functional calculus
-/

section Abs

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
theorem measurable_cfc_abs : Measurable (fun A : Matrix n n ℂ => cfc (fun x : ℝ => |x|) A) := by
  classical
  have hc : ContinuousOn (fun A : Matrix n n ℂ => cfc (fun x : ℝ => |x|) A)
      {A | IsSelfAdjoint A} :=
    ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) _ (by simp) continuousOn_id
      (fun x hx => hx) (by fun_prop)
  have hS : IsClosed {A : Matrix n n ℂ | IsSelfAdjoint A} :=
    isClosed_eq continuous_star continuous_id
  have e : (fun A : Matrix n n ℂ => cfc (fun x : ℝ => |x|) A) =
      Set.piecewise {A | IsSelfAdjoint A} (fun A => cfc (fun x : ℝ => |x|) A) (fun _ => 0) := by
    funext A
    by_cases h : IsSelfAdjoint A
    · simp [Set.piecewise, h]
    · simp [Set.piecewise, h, cfc_apply_of_not_predicate A h]
  rw [e]
  exact hc.measurable_piecewise continuousOn_const hS.measurableSet

theorem cfc_abs_eq_absMat {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    cfc (fun x : ℝ => |x|) J = absMat hJ := by
  rw [hJ.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, absMat,
    Matrix.star_eq_conjTranspose]
  rfl

end Abs

/-!
## Functions of the past
-/

/-- A past sample at length `n`, extended by zero coordinates to a whole growth sample. -/
def extPast (W n : ℕ) (p : PastSample W n) : GrowthPath W :=
  (fun k => if h : k < n then p.1 ⟨k, h⟩ else 0, fun k => if h : k < n + 1 then p.2 ⟨k, h⟩ else 0)

theorem measurable_extPast (n : ℕ) : Measurable (extPast W n) := by
  refine Measurable.prodMk (Measurable.of_eval fun k => ?_) (Measurable.of_eval fun k => ?_)
  · by_cases h : k < n
    · simp only [h, dite_true]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, dite_false]; exact measurable_const
  · by_cases h : k < n + 1
    · simp only [h, dite_true]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [h, dite_false]; exact measurable_const

theorem pastCoords_extPast (n : ℕ) (p : PastSample W n) : pastCoords W n (extPast W n p) = p := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    simp only [pastCoords, extPast, k.isLt, dite_true]

theorem pathAt_extPast (n : ℕ) (ω : GrowthPath W) :
    pathAt W n (extPast W n (pastCoords W n ω)) = pathAt W n ω := by
  rw [pathAt_eq_pathOfPast, Function.comp_apply, Function.comp_apply, pastCoords_extPast]

theorem pathCurrent_extPast (b E : ℝ) (n : ℕ) (ω : GrowthPath W) :
    pathCurrent b E W n (extPast W n (pastCoords W n ω)) = pathCurrent b E W n ω := by
  simp only [pathCurrent, scatteringMatrix, boundaryResolvent, fullInverse, fullPathMatrix,
    pathAt_extPast]

/-- The transport `N_j` as a function of the past at length `j+1`. -/
def pastN (b E : ℝ) (W j : ℕ) (p : PastSample W (j + 1)) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  transportN b E W j (extPast W (j + 1) p)

theorem transportN_eq_past (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    transportN b E W j ω = pastN b E W j (pastCoords W (j + 1) ω) := by
  have h1 : pathAt W j (extPast W (j + 1) (pastCoords W (j + 1) ω)) = pathAt W j ω := by
    rw [pathAt_eq_pathOfPast, Function.comp_apply, Function.comp_apply,
      pastCoords_restrict (Nat.le_succ j), pastCoords_extPast, ← pastCoords_restrict]
  have h2 : freshSample W j (extPast W (j + 1) (pastCoords W (j + 1) ω)) = freshSample W j ω := by
    simp [freshSample, extPast, pastCoords]
  simp only [pastN, transportN, h1, h2]

theorem measurable_transportN (b E : ℝ) (j : ℕ) : Measurable (transportN b E W j) := by
  have hXX : Measurable fun ω : GrowthPath W => pathSchur E (pathAt W j ω) := by
    have e : (fun ω : GrowthPath W => pathSchur E (pathAt W j ω)) =
        pastXX E W j ∘ pastCoords W j := funext fun ω => pastXX_eq E j ω
    rw [e]; exact (measurable_pastXX E j).comp (measurable_pastCoords W j)
  exact measurable_freshTransport_comp b E hXX (measurable_freshSample W j)

theorem measurable_pastN (b E : ℝ) (j : ℕ) : Measurable (pastN b E W j) :=
  (measurable_transportN b E j).comp (measurable_extPast _)

/-!
## The carrier
-/

/-- The carrier at length `k+1+i`: `H_0 = |J_{k+1}|`, `H_{i+1} = NᴴH_iN`. -/
def carrier (b E : ℝ) (W k : ℕ) : ℕ → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => fun ω => cfc (fun x : ℝ => |x|) (pathCurrent b E W (k + 1) ω)
  | i + 1 => fun ω => (transportN b E W (k + 1 + i) ω)ᴴ * carrier b E W k i ω *
      transportN b E W (k + 1 + i) ω

/-- The carrier as a function of the past coordinates at length `k+1+i`. -/
def carrierPast (b E : ℝ) (W k : ℕ) :
    (i : ℕ) → PastSample W (k + 1 + i) → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => fun p => cfc (fun x : ℝ => |x|) (pathCurrent b E W (k + 1) (extPast W (k + 1) p))
  | i + 1 => fun p => (pastN b E W (k + 1 + i) p)ᴴ *
      carrierPast b E W k i (restrictPast (by omega : k + 1 + i ≤ k + 1 + (i + 1)) p) *
        pastN b E W (k + 1 + i) p

theorem carrier_eq_past (b E : ℝ) (k : ℕ) :
    ∀ (i : ℕ) (ω : GrowthPath W),
      carrier b E W k i ω = carrierPast b E W k i (pastCoords W (k + 1 + i) ω)
  | 0, ω => by simp only [carrier, carrierPast, pathCurrent_extPast]
  | i + 1, ω => by
      simp only [carrier, carrierPast]
      rw [carrier_eq_past b E k i ω, transportN_eq_past]
      rfl

theorem measurable_carrierPast (b E : ℝ) (k : ℕ) :
    ∀ i : ℕ, Measurable (carrierPast b E W k i)
  | 0 => measurable_cfc_abs.comp ((measurable_pathCurrent b E (k + 1)).comp (measurable_extPast _))
  | i + 1 => by
      have hN := measurable_pastN (W := W) b E (k + 1 + i)
      have hH := (measurable_carrierPast b E k i).comp (measurable_restrictPast (W := W)
        (by omega : k + 1 + i ≤ k + 1 + (i + 1)))
      exact measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hN)
        hH) hN

theorem measurable_carrier (b E : ℝ) (k i : ℕ) : Measurable (carrier b E W k i) := by
  have e : carrier b E W k i = carrierPast b E W k i ∘ pastCoords W (k + 1 + i) :=
    funext fun ω => carrier_eq_past b E k i ω
  rw [e]; exact (measurable_carrierPast b E k i).comp (measurable_pastCoords W _)

theorem pathCurrent_isHermitian (b E : ℝ) (n : ℕ) (ω : GrowthPath W) :
    (pathCurrent b E W n ω).IsHermitian :=
  twoPortCurrent_isHermitian _

theorem carrierPast_posSemidef (b E : ℝ) (k : ℕ) :
    ∀ (i : ℕ) (p : PastSample W (k + 1 + i)), (carrierPast b E W k i p).PosSemidef
  | 0, p => by
      simp only [carrierPast]
      rw [cfc_abs_eq_absMat (pathCurrent_isHermitian b E _ _)]
      exact absMat_posSemidef _
  | i + 1, p => by
      simp only [carrierPast]
      exact (carrierPast_posSemidef b E k i _).conjTranspose_mul_mul_same _

/-- **The Loewner sandwich along the path**: a.s. `H_i ∓ J_{k+1+i} ⪰ 0` for every `i`. -/
theorem ae_carrier_sandwich {b E : ℝ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ i,
      (carrier b E W k i ω - pathCurrent b E W (k + 1 + i) ω).PosSemidef ∧
        (carrier b E W k i ω + pathCurrent b E W (k + 1 + i) ω).PosSemidef := by
  filter_upwards [ae_pathCurrent_succ_full hb hb2 hE1 hE2 hW] with ω hJ i
  induction i with
  | zero =>
    simp only [carrier, Nat.add_zero]
    rw [cfc_abs_eq_absMat (pathCurrent_isHermitian b E _ _)]
    exact ⟨absMat_sub_posSemidef _, absMat_add_posSemidef _⟩
  | succ i ih =>
    have e : pathCurrent b E W (k + 1 + (i + 1)) ω = (transportN b E W (k + 1 + i) ω)ᴴ *
        pathCurrent b E W (k + 1 + i) ω * transportN b E W (k + 1 + i) ω :=
      hJ (k + 1 + i) (by omega)
    simp only [carrier]
    rw [e]
    exact loewner_congr _ ih.1 ih.2

/-- **The first moment at the base length**: a.s. `Re Tr H_0 = 2 fracTrace (1/2) T_{k+1}`. -/
theorem ae_trace_carrier_zero {b E : ℝ} (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, (carrier b E W k 0 ω).trace.re =
      2 * fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W (k + 1) ω) := by
  filter_upwards [ae_isUnit_pathPencil_growth hb2 hW E, ae_growth_isHermitian W b] with ω hF hA
  simp only [carrier]
  rw [cfc_abs_eq_absMat (pathCurrent_isHermitian b E _ _), trace_absMat,
    pathCurrent_eq b E (k + 1) ω (hF (k + 1)),
    nuclearNorm_twoPortCurrent_eq b E _ (pathSchur_isHermitian E (k + 1) ω hA)
      (boundaryZ_im_pos (by linarith) hE1 hE2),
    pathTransmission, ← pathX, pathX_eq]

end BlockBand.SourceProcess.FullSourceStops
