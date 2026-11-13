module

public import BlockBand.Transmission.PathJet.JetResid
public import BlockBand.Transmission.PathScalar.AbsorbedStep

/-!
# The mean of the fresh jet is the derivative of the mean port trace

* `jetFun b E X ω = -W⁻¹Tr R₊²`, `R₊ = (z - X₊)⁻¹`: a jointly measurable version of the fresh
  jet (`measurable_jetFun_comp`); `freshJet = jetFun` at Hermitian `A` (`freshJet_eq_jetFun`);
  `‖jetFun‖ ≤ η⁻²` (`norm_jetFun_le`);
* `deriv_uW_eq`: for passive `X`, `u'(z) = E freshJet`, where `u(w) = E⟨𝒢₂₂(w)⟩ =
  E W⁻¹Tr(w - X₊)⁻¹` (`ae_g22_eq_Rplus`) and dominated differentiation with the
  deterministic bound `‖(w - X₊)⁻¹‖ ≤ (Im w)⁻¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Metric Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The measurable fresh jet `-W⁻¹Tr R₊²` at `w = z_∂`. -/
def jetFun (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  -crossTr (freshSchur E X ω) (boundaryZ b E) (boundaryZ b E)

theorem measurable_freshRes_comp {α : Type*} [MeasurableSpace α] (E : ℝ) (w : ℂ)
    {X : α → Matrix (Fin W) (Fin W) ℂ} {f : α → LayerSample W .oneBlockOnePort}
    (hX : Measurable X) (hf : Measurable f) :
    Measurable fun a => (w • (1 : Matrix (Fin W) (Fin W) ℂ) - freshSchur E (X a) (f a))⁻¹ := by
  have hlift : Measurable fun a => (Matrix.of fun (u v : Fin 1 × Fin W) => X a u.2 v.2 :
      Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) :=
    Measurable.of_eval_matrix _ fun u v => hX.eval_matrix
  have hS : Measurable fun a => freshSchur E (X a) (f a) :=
    Measurable.of_eval_matrix _ fun x y =>
      (measurable_layerSchur .oneBlockOnePort E hlift hf).eval_matrix
  refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
  simp only [Matrix.sub_apply]
  exact measurable_const.sub hS.eval_matrix

theorem measurable_crossTr_fresh {α : Type*} [MeasurableSpace α] (E : ℝ) (w : ℂ)
    {X : α → Matrix (Fin W) (Fin W) ℂ} {f : α → LayerSample W .oneBlockOnePort}
    (hX : Measurable X) (hf : Measurable f) :
    Measurable fun a => crossTr (freshSchur E (X a) (f a)) w w := by
  have hR := measurable_freshRes_comp E w hX hf
  simp only [crossTr_self_eq, Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (Bridge.measurable_matrix_mul' hR hR).eval_matrix)

theorem measurable_stieltjes_fresh {α : Type*} [MeasurableSpace α] (E : ℝ) (w : ℂ)
    {X : α → Matrix (Fin W) (Fin W) ℂ} {f : α → LayerSample W .oneBlockOnePort}
    (hX : Measurable X) (hf : Measurable f) :
    Measurable fun a => stieltjes (freshSchur E (X a) (f a)) w := by
  have hR := measurable_freshRes_comp E w hX hf
  simp only [stieltjes, Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hR.eval_matrix)

theorem measurable_jetFun_comp {α : Type*} [MeasurableSpace α] (b E : ℝ)
    {X : α → Matrix (Fin W) (Fin W) ℂ} {f : α → LayerSample W .oneBlockOnePort}
    (hX : Measurable X) (hf : Measurable f) :
    Measurable fun a => jetFun b E (X a) (f a) :=
  (measurable_crossTr_fresh E (boundaryZ b E) hX hf).neg

theorem norm_crossTr_le_sq {X' : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X').PosSemidef)
    {w : ℂ} (hw : 0 < w.im) : ‖crossTr X' w w‖ ≤ (w.im)⁻¹ ^ 2 := by
  rw [crossTr_self_eq]
  refine (norm_normTrace_le _).trans ((norm_mul_le _ _).trans ?_)
  have h := norm_inv_le_of_im _ _ hw hY (im_pencil X' w)
  rw [sq]
  exact mul_le_mul h h (norm_nonneg _) (by positivity)

theorem freshJet_eq_jetFun {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ω : LayerSample W .oneBlockOnePort} (hA : (ω.1 0).IsHermitian) :
    freshJet b E X ω = jetFun b E X ω :=
  deriv_stieltjes (passiveY_freshSchur E hY ω hA) (Bridge.boundaryZ_im_pos hb h1 h2)

theorem norm_jetFun_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ω : LayerSample W .oneBlockOnePort} (hA : (ω.1 0).IsHermitian) :
    ‖jetFun b E X ω‖ ≤ (etaZ b E)⁻¹ ^ 2 := by
  rw [jetFun, norm_neg]
  exact norm_crossTr_le_sq (passiveY_freshSchur E hY ω hA) (Bridge.boundaryZ_im_pos hb h1 h2)

/-- **`u'(z) = E freshJet`** for passive `X`. -/
theorem deriv_uW_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (h1 : -2 < E)
    (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    HasDerivAt (fun w => uW b E w X) (∫ ω, freshJet b E X ω ∂freshLaw W b) (boundaryZ b E) := by
  set z := boundaryZ b E
  have hz : 0 < z.im := Bridge.boundaryZ_im_pos (by linarith) h1 h2
  set r := z.im / 2
  have hr : 0 < r := by positivity
  have him : ∀ w ∈ ball z r, r < w.im := by
    intro w hw
    have h1' : |w.im - z.im| ≤ ‖w - z‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2' : ‖w - z‖ < r := by rwa [mem_ball, dist_eq_norm] at hw
    have := (abs_lt.mp (lt_of_le_of_lt h1' h2')).1
    have hrd : r = z.im / 2 := rfl
    linarith
  have hmeasX : Measurable fun _ : LayerSample W .oneBlockOnePort => X := measurable_const
  have hF := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := freshLaw W b)
    (F := fun w ω => stieltjes (freshSchur E X ω) w)
    (F' := fun w ω => -crossTr (freshSchur E X ω) w w) (bound := fun _ => r⁻¹ ^ 2)
    (ball_mem_nhds z hr)
    (Eventually.of_forall fun w => (measurable_stieltjes_fresh E w hmeasX measurable_id).aestronglyMeasurable)
    (Integrable.of_bound (measurable_stieltjes_fresh E z hmeasX measurable_id).aestronglyMeasurable
      (z.im)⁻¹ ((ae_layer_herm b).mono fun ω hA =>
        (norm_normTrace_le _).trans (norm_inv_le_of_im _ _ hz (passiveY_freshSchur E hY ω hA)
          (im_pencil _ z))))
    (measurable_crossTr_fresh E z hmeasX measurable_id).neg.aestronglyMeasurable
    ((ae_layer_herm b).mono fun ω hA w hw => by
      rw [norm_neg]
      refine (norm_crossTr_le_sq (passiveY_freshSchur E hY ω hA) (hr.trans (him w hw))).trans ?_
      exact pow_le_pow_left₀ (inv_nonneg.2 (hr.trans (him w hw)).le)
        (inv_anti₀ hr (him w hw).le) 2)
    (integrable_const _)
    ((ae_layer_herm b).mono fun ω hA w hw =>
      hasDerivAt_stieltjes (passiveY_freshSchur E hY ω hA) (hr.trans (him w hw)))
  have hJ : ∫ ω, -crossTr (freshSchur E X ω) z z ∂freshLaw W b = ∫ ω, freshJet b E X ω ∂freshLaw W b :=
    integral_congr_ae ((ae_layer_herm b).mono fun ω hA =>
      (freshJet_eq_jetFun (by linarith) h1 h2 hY hA).symm)
  rw [← hJ]
  refine hF.2.congr_of_eventuallyEq ?_
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds hz] with w hw
  change uW b E w X = ∫ ω, stieltjes (freshSchur E X ω) w ∂freshLaw W b
  refine integral_congr_ae ?_
  filter_upwards [ae_g22_eq_Rplus hb0 hb hW E hw hY] with ω hω
  change (W : ℂ)⁻¹ * (g22 E w X ω).trace = _
  rw [hω]; rfl

end BlockBand.Transmission.PathJet
